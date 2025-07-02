"""Enhanced Manim MCP server integration with robust error handling."""

import asyncio
import json
import logging
import random
import subprocess
import time
from pathlib import Path
from typing import Any, Dict, List, Optional
from urllib.parse import urljoin

import aiohttp
import tenacity

from ..core.exceptions import AnimatorError, AnimationTimeoutError
from ..generator.models import ProofSketch
from .mock_mcp import MockMCPTransport
from .models import AnimationResponse, AnimationStyle, ManimConfig, AnimationQuality


class EnhancedManimMCPClient:
    """Enhanced MCP client with production-ready error handling and fallbacks."""

    def __init__(self, config: Optional[ManimConfig] = None, use_mock: bool = False):
        """Initialize the enhanced MCP client.

        Args:
            config: Manim configuration
            use_mock: Use mock server for testing
        """
        self.config = config or ManimConfig()
        self.logger = logging.getLogger(__name__)
        self.server_process: Optional[subprocess.Popen] = None
        self.session: Optional[aiohttp.ClientSession] = None
        self._health_check_task: Optional[asyncio.Task] = None
        self._shutdown_event = asyncio.Event()
        self._request_id = 0
        
        # Mock server for testing
        self.use_mock = use_mock
        self.mock_transport: Optional[MockMCPTransport] = None
        if use_mock:
            self.mock_transport = MockMCPTransport()
        
        # Circuit breaker state
        self.failure_count = 0
        self.last_failure_time = 0
        self.circuit_open = False
        self.circuit_timeout = 60.0  # 1 minute
        
        # Connection state
        self.is_connected = False

    async def __aenter__(self):
        """Async context manager entry."""
        await self.connect()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit."""
        await self.disconnect()

    @tenacity.retry(
        wait=tenacity.wait_exponential(multiplier=1, min=1, max=10),
        stop=tenacity.stop_after_attempt(3),
        retry=tenacity.retry_if_exception_type((ConnectionError, asyncio.TimeoutError))
    )
    async def connect(self) -> bool:
        """Connect to MCP server with retry logic."""
        if self._is_circuit_open():
            raise AnimatorError("Circuit breaker is open, server unavailable")

        # Handle mock mode
        if self.use_mock and self.mock_transport:
            await self.mock_transport.connect()
            self.is_connected = True
            self.logger.info("Connected to mock MCP server")
            return True

        try:
            # Check if Manim is available
            if not self._check_manim_available():
                self.logger.error("Manim not found in PATH")
                return False

            # Start server if needed
            if not await self._ensure_server_running():
                return False

            # Create HTTP session
            timeout = aiohttp.ClientTimeout(total=self.config.request_timeout)
            self.session = aiohttp.ClientSession(timeout=timeout)

            # Verify connection
            if await self.health_check():
                self.is_connected = True
                self.failure_count = 0  # Reset on successful connection
                
                # Start health monitoring
                if self.config.enable_health_checks:
                    self._health_check_task = asyncio.create_task(self._health_check_loop())
                
                self.logger.info("Connected to Manim MCP server")
                return True
            else:
                await self.disconnect()
                return False

        except Exception as e:
            self.logger.error(f"Failed to connect to MCP server: {e}")
            self._record_failure()
            await self.disconnect()
            return False

    async def disconnect(self) -> None:
        """Disconnect from MCP server."""
        self._shutdown_event.set()
        self.is_connected = False

        # Stop health check task
        if self._health_check_task:
            self._health_check_task.cancel()
            try:
                await self._health_check_task
            except asyncio.CancelledError:
                pass

        # Close HTTP session
        if self.session:
            await self.session.close()
            self.session = None

        # Handle mock transport
        if self.use_mock and self.mock_transport:
            await self.mock_transport.disconnect()
            self.logger.info("Disconnected from mock MCP server")
            return

        # Stop server process
        if self.server_process:
            try:
                self.server_process.terminate()
                try:
                    self.server_process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    self.logger.warning("Server didn't shutdown gracefully, forcing termination")
                    self.server_process.kill()
                    self.server_process.wait()
                self.logger.info("MCP server stopped")
            except Exception as e:
                self.logger.error(f"Error stopping server: {e}")
            finally:
                self.server_process = None

    async def health_check(self) -> bool:
        """Check if server is healthy."""
        if not self.is_connected:
            return False

        try:
            # Handle mock mode
            if self.use_mock and self.mock_transport:
                health_data = await self.mock_transport.mock_server.health_check()
                return health_data.get("status") == "healthy"

            # Real health check
            if not self.session:
                return False

            async with self.session.get(
                f"{self._get_server_url()}/health",
                timeout=aiohttp.ClientTimeout(total=5)
            ) as response:
                if response.status == 200:
                    data = await response.json()
                    return data.get("status") == "healthy"
                return False

        except Exception as e:
            self.logger.debug(f"Health check failed: {e}")
            return False

    async def render_animation(self, 
                             proof_sketch: ProofSketch,
                             style: AnimationStyle = AnimationStyle.MODERN,
                             quality: AnimationQuality = AnimationQuality.MEDIUM,
                             output_filename: str = "animation.mp4") -> AnimationResponse:
        """Render animation for a proof sketch.

        Args:
            proof_sketch: The proof sketch to animate
            style: Animation style
            quality: Quality level
            output_filename: Output filename

        Returns:
            AnimationResponse with results or error info
        """
        if not self.is_connected:
            raise AnimatorError("Not connected to MCP server")

        if self._is_circuit_open():
            raise AnimatorError("Circuit breaker open, server unavailable")

        try:
            # Handle mock mode
            if self.use_mock and self.mock_transport:
                return await self._render_with_mock(
                    proof_sketch, style, quality, output_filename
                )

            # Real rendering
            return await self._render_with_mcp(
                proof_sketch, style, quality, output_filename
            )

        except Exception as e:
            self.logger.error(f"Animation rendering failed: {e}")
            self._record_failure()
            
            # Return error response
            return AnimationResponse(
                video_path=None,
                thumbnail_path=None,
                duration=0,
                frame_count=0,
                size_bytes=0,
                error=str(e),
                metadata={
                    "error_type": type(e).__name__,
                    "theorem": proof_sketch.theorem_name
                }
            )

    async def _render_with_mock(self, proof_sketch: ProofSketch, 
                               style: AnimationStyle, quality: AnimationQuality,
                               output_filename: str) -> AnimationResponse:
        """Render animation using mock server."""
        params = {
            "proof_sketch": proof_sketch.dict(),
            "style": style.value,
            "quality": quality.value,
            "output_filename": output_filename
        }

        response = await self.mock_transport.send_request(
            "manim.render_proof", params
        )

        if "error" in response:
            raise AnimatorError(f"Mock render failed: {response['error']['message']}")

        result = response["result"]
        return AnimationResponse(
            video_path=Path(result["video_path"]) if result.get("video_path") else None,
            thumbnail_path=Path(result["thumbnail_path"]) if result.get("thumbnail_path") else None,
            duration=result.get("duration", 0),
            frame_count=result.get("frame_count", 0),
            size_bytes=result.get("size_bytes", 0),
            metadata=result.get("metadata", {})
        )

    async def _render_with_mcp(self, proof_sketch: ProofSketch,
                              style: AnimationStyle, quality: AnimationQuality,
                              output_filename: str) -> AnimationResponse:
        """Render animation using real MCP server."""
        if not self.session:
            raise AnimatorError("No active session")

        # Prepare request
        request_data = {
            "jsonrpc": "2.0",
            "method": "manim.render_proof",
            "params": {
                "proof_sketch": proof_sketch.dict(),
                "style": style.value,
                "quality": quality.value,
                "output_filename": output_filename
            },
            "id": self._get_next_request_id()
        }

        # Calculate timeout based on complexity
        timeout = 60 + len(proof_sketch.key_steps) * 30
        client_timeout = aiohttp.ClientTimeout(total=timeout)

        async with self.session.post(
            f"{self._get_server_url()}/jsonrpc",
            json=request_data,
            timeout=client_timeout
        ) as response:
            if response.status != 200:
                raise AnimatorError(f"HTTP {response.status}: {await response.text()}")

            data = await response.json()

            if "error" in data:
                error = data["error"]
                raise AnimatorError(f"MCP error {error['code']}: {error['message']}")

            result = data["result"]
            return AnimationResponse(
                video_path=Path(result["video_path"]) if result.get("video_path") else None,
                thumbnail_path=Path(result["thumbnail_path"]) if result.get("thumbnail_path") else None,
                duration=result.get("duration", 0),
                frame_count=result.get("frame_count", 0),
                size_bytes=result.get("size_bytes", 0),
                metadata=result.get("metadata", {})
            )

    def _check_manim_available(self) -> bool:
        """Check if Manim is available."""
        try:
            result = subprocess.run(
                ["manim", "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            return result.returncode == 0
        except (subprocess.SubprocessError, FileNotFoundError):
            return False

    async def _ensure_server_running(self) -> bool:
        """Ensure MCP server is running."""
        if self._is_server_running():
            return True

        if not self.config.auto_start:
            self.logger.error("Server not running and auto_start disabled")
            return False

        return await self._start_server()

    def _is_server_running(self) -> bool:
        """Check if server process is running."""
        return (self.server_process is not None and 
                self.server_process.poll() is None)

    async def _start_server(self) -> bool:
        """Start the MCP server process."""
        try:
            # For now, we simulate starting a server
            # In production, this would start the actual MCP server
            self.logger.warning("MCP server not implemented, using simulation")
            
            # Create a dummy process that does nothing
            self.server_process = subprocess.Popen(
                ["python", "-c", "import time; time.sleep(3600)"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE
            )
            
            await asyncio.sleep(1)  # Simulate startup time
            return True

        except Exception as e:
            self.logger.error(f"Failed to start server: {e}")
            return False

    async def _health_check_loop(self) -> None:
        """Background health monitoring."""
        while not self._shutdown_event.is_set():
            try:
                await asyncio.sleep(30)
                if not await self.health_check():
                    self.logger.warning("Health check failed")
                    self._record_failure()
            except asyncio.CancelledError:
                break
            except Exception as e:
                self.logger.warning(f"Health check error: {e}")

    def _record_failure(self) -> None:
        """Record a failure for circuit breaker."""
        self.failure_count += 1
        self.last_failure_time = time.time()
        
        if self.failure_count >= 3:
            self.circuit_open = True
            self.logger.warning("Circuit breaker opened")

    def _is_circuit_open(self) -> bool:
        """Check if circuit breaker is open."""
        if not self.circuit_open:
            return False
        
        if time.time() - self.last_failure_time > self.circuit_timeout:
            self.circuit_open = False
            self.failure_count = 0
            self.logger.info("Circuit breaker reset")
            return False
        
        return True

    def _get_server_url(self) -> str:
        """Get server URL."""
        return f"http://{self.config.host}:{self.config.port}"

    def _get_next_request_id(self) -> int:
        """Get next request ID."""
        self._request_id += 1
        return self._request_id