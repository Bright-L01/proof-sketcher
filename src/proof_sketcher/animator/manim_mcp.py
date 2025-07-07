"""Manim MCP server integration for animation generation."""

import asyncio
import logging
import subprocess
import time
from contextlib import asynccontextmanager
from pathlib import Path
from typing import AsyncIterator, List, Optional, Any, Dict

import aiohttp
import tenacity

from ..core.exceptions import AnimationTimeoutError
from .mock_mcp import MockMCPTransport
from .models import AnimationRequest, AnimationResponse, AnimationScene, ManimConfig


class ManimMCPClient:
    """Client for interacting with Manim MCP server with robust error handling."""

    def __init__(self, config: Optional[ManimConfig] = None, use_mock: bool = False):
        """Initialize the MCP client.

        Args:
            config: Manim configuration. Uses default if None.
            use_mock: Use mock server for testing
        """
        self.config = config or ManimConfig.model_validate({})
        self.logger = logging.getLogger(__name__)
        self.server_process: Optional[subprocess.Popen[str]] = None
        self.session: Optional[aiohttp.ClientSession] = None
        self.session_pool: Optional[aiohttp.ClientSession] = None
        self.active_connections = 0
        self._health_check_task: Optional[asyncio.Task[None]] = None
        self._shutdown_event = asyncio.Event()
        self._request_id = 0
        self._connected = False
        
        # Mock server for testing
        self.use_mock = use_mock
        self.mock_transport: Optional[MockMCPTransport] = None
        if use_mock:
            self.mock_transport = MockMCPTransport()
        
        # Connection retry settings
        self.max_retries = 3
        self.base_delay = 1.0
        self.max_delay = 30.0
        
        # Circuit breaker state
        self.failure_count = 0
        self.last_failure_time = 0.0
        self.circuit_open = False
        self.circuit_timeout = 60.0  # 1 minute
    
    def _increment_circuit_breaker(self) -> None:
        """Increment circuit breaker failure count."""
        self.failure_count += 1
        self.last_failure_time = time.time()
        
        if self.failure_count >= 5:  # Open circuit after 5 failures
            self.circuit_open = True
            self.logger.warning("Circuit breaker opened due to repeated failures")
    
    def _is_circuit_open(self) -> bool:
        """Check if circuit breaker is open."""
        if not self.circuit_open:
            return False
            
        # Check if timeout has passed
        if time.time() - self.last_failure_time > self.circuit_timeout:
            self.circuit_open = False
            self.failure_count = 0
            return False
            
        return True

    @tenacity.retry(
        wait=tenacity.wait_exponential(multiplier=1, min=1, max=10),
        stop=tenacity.stop_after_attempt(3),
        retry=tenacity.retry_if_exception_type((ConnectionError, asyncio.TimeoutError))
    )
    async def start_server(self) -> bool:
        """Start the Manim MCP server with retry logic.

        Returns:
            True if server started successfully, False otherwise
        """
        # Handle mock mode
        if self.use_mock and self.mock_transport:
            await self.mock_transport.connect()
            self.logger.info("Mock MCP server started")
            return True
            
        if self.is_server_running():
            self.logger.info("Manim server already running")
            return True

        if not self.config.auto_start:
            self.logger.error("Server not running and auto_start is disabled")
            return False

        try:
            # Ensure output directories exist
            if self.config.output_dir:
                self.config.output_dir.mkdir(parents=True, exist_ok=True)
            if self.config.temp_dir:
                self.config.temp_dir.mkdir(parents=True, exist_ok=True)

            # Check if manim is available
            if not self._check_manim_available():
                self.logger.error("Manim not found in PATH")
                return False

            # Build server command
            cmd = self._build_server_command()

            self.logger.info(f"Starting Manim MCP server: {' '.join(cmd)}")
            
            # Start the server process
            self.server_process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            
            # Wait for server to be ready
            await self._wait_for_server_ready()
            
            # Start health check monitoring
            if self.config.enable_health_checks:
                self._health_check_task = asyncio.create_task(self._health_check_loop())
            
            self.logger.info("Manim MCP server started successfully")
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to start Manim server: {e}")
            if self.server_process:
                self.server_process.terminate()
                self.server_process = None
            return False

    def _check_manim_available(self) -> bool:
        """Check if Manim is available in PATH."""
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

    def _build_server_command(self) -> List[str]:
        """Build the command to start the MCP server."""
        # For now, we'll use a simple Python script approach
        # In a real implementation, this would start the actual MCP server
        cmd = [
            "python", "-m", "manim_mcp_server",
            "--host", self.config.server_host,
            "--port", str(self.config.server_port)
        ]
        
        if self.config.temp_dir:
            cmd.extend(["--temp-dir", str(self.config.temp_dir)])
        if self.config.output_dir:
            cmd.extend(["--output-dir", str(self.config.output_dir)])
        
        return cmd

    async def _wait_for_server_ready(self, timeout: float = 30.0) -> None:
        """Wait for the server to be ready to accept connections."""
        start_time = time.time()
        
        while time.time() - start_time < timeout:
            try:
                if await self.health_check():
                    return
            except Exception:
                pass
            
            await asyncio.sleep(1.0)
        
        raise AnimationTimeoutError("Server failed to start within timeout")

    async def connect(self) -> bool:
        """Connect to the MCP server.
        
        Returns:
            True if connection successful, False otherwise
        """
        if self._connected:
            self.logger.debug("Already connected to MCP server")
            return True
            
        try:
            # Start server if needed
            if not await self.start_server():
                return False
                
            # Initialize session pool
            if not self.session_pool:
                self.session_pool = aiohttp.ClientSession(
                    timeout=aiohttp.ClientTimeout(total=self.config.server_timeout)
                )
            
            # Verify connection with health check
            if await self.health_check():
                self._connected = True
                
                # Start health check loop
                if not self._health_check_task or self._health_check_task.done():
                    self._health_check_task = asyncio.create_task(self._health_check_loop())
                
                self.logger.info("Successfully connected to MCP server")
                return True
            else:
                self.logger.error("Failed to verify MCP server connection")
                return False
                
        except Exception as e:
            self.logger.error(f"Failed to connect to MCP server: {e}")
            return False
    
    async def disconnect(self) -> None:
        """Disconnect from the MCP server and clean up resources."""
        try:
            # Stop health check task
            if self._health_check_task and not self._health_check_task.done():
                self._health_check_task.cancel()
                try:
                    await self._health_check_task
                except asyncio.CancelledError:
                    pass
            
            # Close session pool
            if self.session_pool:
                await self.session_pool.close()
                self.session_pool = None
            
            # Stop server if we started it
            if self.server_process:
                self.logger.info("Stopping MCP server")
                self.server_process.terminate()
                try:
                    self.server_process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    self.server_process.kill()
                    self.server_process.wait()
                self.server_process = None
            
            # Disconnect mock transport
            if self.use_mock and self.mock_transport:
                await self.mock_transport.disconnect()
            
            self._connected = False
            self.logger.info("Disconnected from MCP server")
            
        except Exception as e:
            self.logger.error(f"Error during disconnect: {e}")

    async def _health_check_loop(self) -> None:
        """Background task to monitor server health."""
        while not self._shutdown_event.is_set():
            try:
                await asyncio.sleep(30)  # Check every 30 seconds
                if not await self.health_check():
                    self.logger.warning("Health check failed, server may be unresponsive")
                    self._record_failure()
            except asyncio.CancelledError:
                break
            except Exception as e:
                self.logger.warning(f"Health check error: {e}")
                self._record_failure()

    def _record_failure(self) -> None:
        """Record a failure for circuit breaker logic."""
        self.failure_count += 1
        self.last_failure_time = time.time()
        
        if self.failure_count >= 3:
            self.circuit_open = True
            self.logger.warning("Circuit breaker opened due to repeated failures")

    def _is_circuit_open(self) -> bool:
        """Check if circuit breaker is open."""
        if not self.circuit_open:
            return False
        
        # Check if timeout has passed
        if time.time() - self.last_failure_time > self.circuit_timeout:
            self.circuit_open = False
            self.failure_count = 0
            self.logger.info("Circuit breaker reset")
            return False
        
        return True

    async def stop_server(self) -> None:
        """Stop the Manim MCP server."""
        self._shutdown_event.set()

        # Stop health check task
        if self._health_check_task:
            self._health_check_task.cancel()
            try:
                await self._health_check_task
            except asyncio.CancelledError:
                pass

        # Close session pool
        await self._close_session_pool()

        # Stop server process
        if self.server_process:
            try:
                self.server_process.terminate()

                # Wait for graceful shutdown
                try:
                    self.server_process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    self.logger.warning(
                        "Server didn't shutdown gracefully, forcing termination"
                    )
                    self.server_process.kill()
                    self.server_process.wait()

                self.logger.info("Manim server stopped")
            except Exception as e:
                self.logger.error(f"Error stopping server: {e}")
            finally:
                self.server_process = None

    async def render_scene(self, scene: AnimationScene, output_path: Path) -> bool:
        """Render a single animation scene.

        Args:
            scene: Scene to render
            output_path: Path for output video

        Returns:
            True if rendering succeeded, False otherwise
        """
        async with self._get_session() as session:
            try:
                # Prepare render request
                request_data = {
                    "scene_id": scene.scene_id,
                    "initial_formula": scene.initial_formula,
                    "final_formula": scene.final_formula,
                    "intermediate_formulas": scene.intermediate_formulas,
                    "transformation_type": scene.transformation_type.value,
                    "duration": scene.duration,
                    "highlighted_parts": scene.highlighted_parts,
                    "output_path": str(output_path),
                    "fade_in_time": scene.fade_in_time,
                    "fade_out_time": scene.fade_out_time,
                }

                url = f"{self.config.get_server_url()}/render_scene"

                timeout = aiohttp.ClientTimeout(total=self.config.render_timeout)

                async with session.post(
                    url, json=request_data, timeout=timeout
                ) as response:
                    if response.status == 200:
                        result = await response.json()
                        if result.get("success"):
                            self.logger.debug(
                                f"Successfully rendered scene {scene.scene_id}"
                            )
                            return True
                        else:
                            error_msg = result.get("error", "Unknown error")
                            self.logger.error(f"Scene rendering failed: {error_msg}")
                            return False
                    else:
                        error_text = await response.text()
                        self.logger.error(
                            f"Server error {response.status}: {error_text}"
                        )
                        return False

            except asyncio.TimeoutError:
                self.logger.error(f"Rendering timeout for scene {scene.scene_id}")
                return False
            except Exception as e:
                self.logger.error(f"Error rendering scene {scene.scene_id}: {e}")
                return False

    async def render_animation(self, request: AnimationRequest) -> AnimationResponse:
        """Render complete animation from request.

        Args:
            request: Animation request

        Returns:
            Animation response with results
        """
        start_time = time.time()
        
        # Check circuit breaker
        if self._is_circuit_open():
            from ..core.exceptions import MCPConnectionError
            raise MCPConnectionError("Circuit breaker is open")
        
        # Handle mock mode
        if self.use_mock and self.mock_transport:
            from .mock_mcp import create_mock_animation_response
            from ..generator.models import ProofSketch, ProofStep
            
            # Create a simple proof sketch from the request
            proof_sketch = ProofSketch(
                theorem_name=request.theorem_name,
                introduction="Mock introduction",
                key_steps=[
                    ProofStep(
                        step_number=i+1,
                        description=f"Step {i+1}",
                        mathematical_content="",
                        tactics=[]
                    )
                    for i in range(len(request.segments))
                ],
                conclusion="Mock conclusion"
            )
            
            return create_mock_animation_response(proof_sketch, success=True)

        try:
            # Ensure server is running
            if not await self._ensure_server_running():
                return AnimationResponse(
                    success=False,
                    error_message="Failed to start Manim server",
                    metadata={"theorem_name": request.theorem_name}
                )

            # Prepare output paths
            output_dir = self.config.output_dir or Path.cwd() / "animations"
            output_dir.mkdir(parents=True, exist_ok=True)

            video_path = output_dir / f"{request.theorem_name}_{request.request_id}.mp4"
            preview_path = (
                output_dir / f"{request.theorem_name}_{request.request_id}_preview.png"
            )

            # Render segments
            segment_paths = []
            chapter_markers = []
            current_time = 0.0

            for i, segment in enumerate(request.segments):
                segment_path = (
                    output_dir
                    / f"{request.theorem_name}_{request.request_id}_segment_{i}.mp4"
                )

                if await self._render_segment(segment, segment_path):
                    segment_paths.append(segment_path)
                    chapter_markers.append((current_time, segment.title))
                    current_time += segment.total_duration
                else:
                    return AnimationResponse(
                        success=False,
                        error_message=f"Failed to render segment {i}: {segment.title}",
                        metadata={"theorem_name": request.theorem_name}
                    )

            # Combine segments into final video
            if len(segment_paths) > 1:
                if not await self._combine_segments(segment_paths, video_path):
                    return AnimationResponse(
                        success=False,
                        error_message="Failed to combine video segments",
                        metadata={"theorem_name": request.theorem_name}
                    )
            elif len(segment_paths) == 1:
                # Single segment, just copy/move
                import shutil

                shutil.copy2(segment_paths[0], video_path)
            else:
                return AnimationResponse(
                    success=False,
                    error_message="No segments were successfully rendered",
                    metadata={"theorem_name": request.theorem_name}
                )

            # Generate preview image
            await self._generate_preview(video_path, preview_path)

            # Calculate file size
            file_size_mb = (
                video_path.stat().st_size / (1024 * 1024)
                if video_path.exists()
                else None
            )

            # Get actual duration
            actual_duration = await self._get_video_duration(video_path)

            generation_time = (time.time() - start_time) * 1000

            return AnimationResponse(
                video_path=video_path,
                preview_image_path=preview_path if preview_path.exists() else None,
                segments_paths=segment_paths,
                duration=actual_duration or request.estimated_duration,
                actual_duration=actual_duration,
                file_size_mb=file_size_mb,
                generation_time_ms=generation_time,
                chapter_markers=chapter_markers,
                success=True,
                metadata={
                    "theorem_name": request.theorem_name,
                    "request_id": request.request_id,
                    "style": request.config.style.value if request.config else "modern",
                    "quality": request.config.quality.value if request.config else "medium"
                }
            )

        except Exception as e:
            generation_time = (time.time() - start_time) * 1000
            self.logger.exception("Animation rendering failed")

            return AnimationResponse(
                generation_time_ms=generation_time,
                success=False,
                error_message=str(e),
                metadata={"theorem_name": request.theorem_name if request else "unknown"}
            )

    async def health_check(self) -> bool:
        """Check if server is healthy.

        Returns:
            True if server is healthy, False otherwise
        """
        # In mock mode, always return True
        if self.use_mock:
            return True
            
        # If not connected, return False
        if not self._connected and not self.server_process:
            return False
            
        try:
            async with self._get_session() as session:
                url = f"{self.config.get_server_url()}/health"
                timeout = aiohttp.ClientTimeout(total=5.0)

                async with session.get(url, timeout=timeout) as response:
                    if response.status == 200:
                        result = await response.json()
                        return result.get("status") == "healthy"
                    return False

        except Exception:
            return False

    def is_server_running(self) -> bool:
        """Check if server process is running.

        Returns:
            True if server process is alive, False otherwise
        """
        if not self.server_process:
            return False

        try:
            # Check if process is still alive
            return self.server_process.poll() is None
        except Exception:
            return False

    @asynccontextmanager
    async def _get_session(self) -> AsyncIterator[aiohttp.ClientSession]:
        """Get a session from the pool or create a new one."""
        # Check if we need to create a new session
        if not self.session_pool or self.session_pool.closed:
            self.session_pool = aiohttp.ClientSession(
                timeout=aiohttp.ClientTimeout(total=self.config.server_timeout)
            )
        
        yield self.session_pool

    async def __aenter__(self) -> "ManimMCPClient":
        """Async context manager entry."""
        await self.connect()
        return self
    
    async def __aexit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        """Async context manager exit."""
        await self.disconnect()
    
    async def _close_session_pool(self) -> None:
        """Close all sessions in the pool."""
        if self.session_pool and not self.session_pool.closed:
            await self.session_pool.close()
            self.session_pool = None

    def _build_server_command(self) -> List[str]:
        """Build command to start Manim MCP server."""
        cmd = [
            "python",
            "-m",
            "manim_mcp_server",
            "--host",
            self.config.server_host,
            "--port",
            str(self.config.server_port),
            "--max-renders",
            str(self.config.max_concurrent_renders),
        ]

        if self.config.output_dir:
            cmd.extend(["--output-dir", str(self.config.output_dir)])

        if self.config.temp_dir:
            cmd.extend(["--temp-dir", str(self.config.temp_dir)])

        if self.config.keep_temp_files:
            cmd.append("--keep-temp")

        return cmd

    async def _wait_for_server_ready(self) -> bool:
        """Wait for server to be ready to accept connections."""
        start_time = time.time()

        while time.time() - start_time < self.config.server_timeout:
            if await self.health_check():
                return True

            await asyncio.sleep(1.0)

        return False

    async def _ensure_server_running(self) -> bool:
        """Ensure server is running, start if needed."""
        if await self.health_check():
            return True

        if self.config.auto_start:
            return await self.start_server()

        return False

    async def _health_check_loop(self) -> None:
        """Background task for health checking and auto-restart."""
        while not self._shutdown_event.is_set():
            try:
                await asyncio.sleep(self.config.health_check_interval)

                if self._shutdown_event.is_set():
                    break

                if not await self.health_check():
                    self.logger.warning("Server health check failed")

                    if self.config.auto_restart:
                        self.logger.info("Attempting to restart server")
                        await self.stop_server()
                        await asyncio.sleep(2.0)

                        if not self._shutdown_event.is_set():
                            await self.start_server()

            except asyncio.CancelledError:
                break
            except Exception as e:
                self.logger.error(f"Health check error: {e}")

    async def _render_segment(self, segment, output_path: Path) -> bool:
        """Render a single segment."""
        try:
            async with self._get_session() as session:
                request_data = {
                    "segment_title": segment.title,
                    "scenes": [
                        {
                            "scene_id": scene.scene_id,
                            "initial_formula": scene.initial_formula,
                            "final_formula": scene.final_formula,
                            "intermediate_formulas": scene.intermediate_formulas,
                            "transformation_type": scene.transformation_type.value,
                            "duration": scene.duration,
                            "highlighted_parts": scene.highlighted_parts,
                            "narration_text": scene.narration_text,
                        }
                        for scene in segment.scenes
                    ],
                    "output_path": str(output_path),
                }

                url = f"{self.config.get_server_url()}/render_segment"
                timeout = aiohttp.ClientTimeout(
                    total=self.config.render_timeout * len(segment.scenes)
                )

                async with session.post(
                    url, json=request_data, timeout=timeout
                ) as response:
                    if response.status == 200:
                        result = await response.json()
                        return result.get("success", False)
                    return False

        except Exception as e:
            self.logger.error(f"Error rendering segment: {e}")
            return False

    async def _combine_segments(
        self, segment_paths: List[Path], output_path: Path
    ) -> bool:
        """Combine multiple segments into final video."""
        try:
            async with self._get_session() as session:
                request_data = {
                    "segment_paths": [str(p) for p in segment_paths],
                    "output_path": str(output_path),
                }

                url = f"{self.config.get_server_url()}/combine_segments"
                timeout = aiohttp.ClientTimeout(total=300.0)  # 5 minutes for combining

                async with session.post(
                    url, json=request_data, timeout=timeout
                ) as response:
                    if response.status == 200:
                        result = await response.json()
                        return result.get("success", False)
                    return False

        except Exception as e:
            self.logger.error(f"Error combining segments: {e}")
            return False

    async def _generate_preview(self, video_path: Path, preview_path: Path) -> bool:
        """Generate preview image from video."""
        try:
            async with self._get_session() as session:
                request_data = {
                    "video_path": str(video_path),
                    "preview_path": str(preview_path),
                    "timestamp": 5.0,  # Generate preview at 5 seconds
                }

                url = f"{self.config.get_server_url()}/generate_preview"
                timeout = aiohttp.ClientTimeout(total=30.0)

                async with session.post(
                    url, json=request_data, timeout=timeout
                ) as response:
                    if response.status == 200:
                        result = await response.json()
                        return result.get("success", False)
                    return False

        except Exception as e:
            self.logger.error(f"Error generating preview: {e}")
            return False

    async def _get_video_duration(self, video_path: Path) -> Optional[float]:
        """Get duration of video file."""
        try:
            async with self._get_session() as session:
                request_data = {"video_path": str(video_path)}

                url = f"{self.config.get_server_url()}/get_duration"
                timeout = aiohttp.ClientTimeout(total=10.0)

                async with session.post(
                    url, json=request_data, timeout=timeout
                ) as response:
                    if response.status == 200:
                        result = await response.json()
                        return result.get("duration")
                    return None

        except Exception as e:
            self.logger.error(f"Error getting video duration: {e}")
            return None


class ManimMCPManager:
    """High-level manager for Manim MCP operations."""

    def __init__(self, config: Optional[ManimConfig] = None):
        """Initialize the manager.

        Args:
            config: Manim configuration
        """
        self.config = config or ManimConfig.model_validate({})
        self.client = ManimMCPClient(self.config)
        self.logger = logging.getLogger(__name__)

    async def __aenter__(self):
        """Async context manager entry."""
        await self.client.start_server()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit."""
        await self.client.stop_server()

    async def render_animation(self, request: AnimationRequest) -> AnimationResponse:
        """Render animation with automatic retries."""
        for attempt in range(self.config.retry_attempts):
            try:
                return await self.client.render_animation(request)
            except Exception as e:
                if attempt < self.config.retry_attempts - 1:
                    self.logger.warning(
                        f"Render attempt {attempt + 1} failed: {e}, retrying..."
                    )
                    await asyncio.sleep(self.config.retry_delay * (attempt + 1))
                else:
                    self.logger.error(f"All render attempts failed: {e}")
                    return AnimationResponse(
                        success=False,
                        error_message=f"Rendering failed after {self.config.retry_attempts} attempts: {e}",
                        metadata={"theorem_name": request.theorem_name}
                    )

    async def validate_setup(self) -> bool:
        """Validate that Manim setup is working."""
        try:
            # Check if we can start the server
            if not await self.client.start_server():
                return False

            # Check health
            if not await self.client.health_check():
                return False

            self.logger.info("Manim MCP setup validation successful")
            return True

        except Exception as e:
            self.logger.error(f"Manim setup validation failed: {e}")
            return False
        finally:
            await self.client.stop_server()
