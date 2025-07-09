"""Mock MCP server for testing without real Manim."""

import asyncio
import logging
import secrets
import tempfile
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

from ..generator.models import ProofSketch
from .models import AnimationResponse


class MockMCPServer:
    """Mock MCP server that simulates Manim responses for testing."""
    
    def __init__(self, success_rate: float = 0.8, delay_range: Tuple[float, float] = (0.1, 0.5)):
        """Initialize mock MCP server.
        
        Args:
            success_rate: Probability of successful response (0-1)
            delay_range: Min and max delay for responses in seconds
        """
        self.success_rate = success_rate
        self.delay_range = delay_range
        self.logger = logging.getLogger(__name__)
        self.is_running = False
        self.request_count = 0
        self.temp_dir = Path(tempfile.mkdtemp(prefix="mock_mcp_"))
        
    async def start(self):
        """Simulate server startup."""
        await asyncio.sleep(0.1)  # Simulate startup time
        self.is_running = True
        self.logger.info("Mock MCP server started")
        
    async def stop(self):
        """Simulate server shutdown."""
        self.is_running = False
        self.logger.info("Mock MCP server stopped")
        
    async def health_check(self) -> Dict[str, Any]:
        """Simulate health check response."""
        if not self.is_running:
            raise ConnectionError("Server not running")
            
        await asyncio.sleep(0.05)  # Small delay
        
        return {
            "status": "healthy",
            "manim_version": "0.17.3-mock",
            "server_version": "1.0.0-mock",
            "uptime": 3600,
            "request_count": self.request_count
        }
    
    async def handle_request(self, method: str, params: Dict[str, Any]) -> Dict[str, Any]:
        """Handle a mock MCP request.
        
        Args:
            method: Method name
            params: Request parameters
            
        Returns:
            Mock response
        """
        if not self.is_running:
            raise ConnectionError("Server not running")
            
        # Simulate processing delay
        delay = secrets.randbelow(int((self.delay_range[1] - self.delay_range[0]) * 1000)) / 1000 + self.delay_range[0]
        await asyncio.sleep(delay)
        
        self.request_count += 1
        
        # Simulate random failures
        if secrets.randbelow(100) / 100 > self.success_rate:
            error_types = [
                {"code": -32603, "message": "Internal error: Memory limit exceeded"},
                {"code": -32603, "message": "Internal error: Rendering failed"},
                {"code": -32504, "message": "Timeout: Animation took too long"},
                {"code": -32602, "message": "Invalid params: Unsupported animation style"}
            ]
            error = error_types[secrets.randbelow(len(error_types))]
            self.logger.warning(f"Mock server simulating error: {error['message']}")
            return {"error": error}
        
        # Handle different methods
        if method == "manim.render_proof":
            return await self._mock_render_proof(params)
        elif method == "manim.get_progress":
            return self._mock_progress()
        elif method == "manim.cancel_render":
            return {"result": {"cancelled": True}}
        else:
            return {"error": {"code": -32601, "message": f"Method not found: {method}"}}
    
    async def _mock_render_proof(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Mock proof rendering.
        
        Args:
            params: Render parameters
            
        Returns:
            Mock render response
        """
        # Simulate longer processing for complex proofs
        proof_data = params.get("proof_sketch", {})
        step_count = len(proof_data.get("key_steps", []))
        
        # Additional delay based on complexity
        complexity_delay = step_count * 0.2
        await asyncio.sleep(complexity_delay)
        
        # Create a mock video file
        video_filename = params.get("output_filename", "animation.mp4")
        video_path = self.temp_dir / video_filename
        
        # Write some dummy data to make it look real
        video_path.write_bytes(b"MOCK_VIDEO_DATA" * 1000)
        
        # Create a mock thumbnail
        thumbnail_path = self.temp_dir / video_filename.replace(".mp4", "_thumb.png")
        thumbnail_path.write_bytes(b"MOCK_THUMBNAIL_DATA" * 100)
        
        # Simulate different quality outputs
        quality = params.get("quality", "medium")
        quality_multipliers = {"low": 0.5, "medium": 1.0, "high": 2.0}
        multiplier = quality_multipliers.get(quality, 1.0)
        
        return {
            "result": {
                "video_path": str(video_path),
                "thumbnail_path": str(thumbnail_path),
                "duration": 30.0 + step_count * 15.0,
                "frame_count": int((30 + step_count * 15) * 30),  # 30 fps
                "size_bytes": int(1024 * 1024 * multiplier * (1 + step_count * 0.5)),
                "metadata": {
                    "renderer": "mock",
                    "quality": quality,
                    "style": params.get("style", "modern"),
                    "steps_animated": step_count
                }
            }
        }
    
    def _mock_progress(self) -> Dict[str, Any]:
        """Mock progress response."""
        progress = secrets.randbelow(100)
        return {
            "result": {
                "progress": progress,
                "stage": "rendering" if progress < 90 else "encoding",
                "eta_seconds": max(0, int((100 - progress) * 0.5))
            }
        }


class MockMCPTransport:
    """Mock transport for testing MCP client without real server."""
    
    def __init__(self, mock_server: Optional[MockMCPServer] = None):
        """Initialize mock transport.
        
        Args:
            mock_server: MockMCPServer instance
        """
        self.mock_server = mock_server or MockMCPServer()
        self.is_connected = False
        
    async def connect(self):
        """Simulate connection."""
        await self.mock_server.start()
        self.is_connected = True
        
    async def disconnect(self):
        """Simulate disconnection."""
        await self.mock_server.stop()
        self.is_connected = False
        
    async def send_request(self, method: str, params: Dict[str, Any], 
                          request_id: Optional[int] = None) -> Dict[str, Any]:
        """Send mock request.
        
        Args:
            method: Method name
            params: Request parameters
            request_id: Request ID
            
        Returns:
            Mock response
        """
        if not self.is_connected:
            raise ConnectionError("Not connected")
            
        # Create JSON-RPC request
        request = {
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
            "id": request_id or secrets.randbelow(10000) + 1
        }
        
        # Get response from mock server
        response = await self.mock_server.handle_request(method, params)
        
        # Format as JSON-RPC response
        if "error" in response:
            return {
                "jsonrpc": "2.0",
                "error": response["error"],
                "id": request["id"]
            }
        else:
            return {
                "jsonrpc": "2.0",
                "result": response.get("result", {}),
                "id": request["id"]
            }


def create_mock_animation_response(proof_sketch: ProofSketch, 
                                 success: bool = True,
                                 video_path: Optional[Path] = None) -> AnimationResponse:
    """Create a mock AnimationResponse for testing.
    
    Args:
        proof_sketch: The proof sketch
        success: Whether the animation succeeded
        video_path: Optional video path
        
    Returns:
        Mock AnimationResponse
    """
    if success and not video_path:
        # Create a temporary mock video
        temp_dir = Path(tempfile.mkdtemp(prefix="mock_animation_"))
        video_path = temp_dir / "mock_animation.mp4"
        video_path.write_bytes(b"MOCK_VIDEO" * 100)
    
    if success:
        return AnimationResponse(
            video_path=video_path,
            thumbnail_path=video_path.with_suffix('.png') if video_path else None,
            duration=30.0 + len(proof_sketch.key_steps) * 15.0,
            frame_count=int((30 + len(proof_sketch.key_steps) * 15) * 30),
            size_bytes=video_path.stat().st_size if video_path else 0,
            metadata={
                "mock": True,
                "theorem": proof_sketch.theorem_name
            }
        )
    else:
        return AnimationResponse(
            video_path=None,
            thumbnail_path=None,
            duration=0,
            frame_count=0,
            size_bytes=0,
            error="Mock animation failure",
            metadata={"mock": True, "failed": True}
        )