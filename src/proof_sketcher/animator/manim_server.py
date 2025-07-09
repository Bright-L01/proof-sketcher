"""
Manim MCP Server Integration

This module implements a Model Context Protocol (MCP) server for Manim animations,
providing a clean interface for generating mathematical proof animations.
"""

import asyncio
import json
import logging
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional

try:
    from mcp.server import Server
    from mcp.server.stdio import stdio_server

    MCP_AVAILABLE = True
except ImportError:
    MCP_AVAILABLE = False
    Server = None
    stdio_server = None

from ..utils.security import sanitize_filename, validate_file_path


class ManimMCPServer:
    """MCP server for Manim animations with security and error handling."""

    def __init__(self, temp_dir: Optional[Path] = None):
        """Initialize the Manim MCP server.

        Args:
            temp_dir: Directory for temporary files
        """
        self.logger = logging.getLogger(__name__)
        self.temp_dir = temp_dir or Path(tempfile.gettempdir()) / "proof_sketcher_manim"
        self.temp_dir.mkdir(exist_ok=True, parents=True)

        if not MCP_AVAILABLE:
            self.logger.warning("MCP not available - using direct subprocess mode")
            self.server = None
        else:
            try:
                self.server = Server("manim-server")
                self.setup_handlers()
            except Exception as e:
                self.logger.warning(f"MCP server setup failed: {e}")
                self.server = None

        # Check Manim availability
        self.manim_available = self._check_manim_available()
        if not self.manim_available:
            self.logger.warning(
                "Manim not available - animations will fall back to static generation"
            )

    def _check_manim_available(self) -> bool:
        """Check if Manim is available."""
        try:
            result = subprocess.run(
                ["manim", "--version"], capture_output=True, text=True, timeout=10
            )
            return result.returncode == 0
        except (subprocess.SubprocessError, FileNotFoundError):
            return False

    def setup_handlers(self):
        """Set up MCP server handlers."""
        if not self.server:
            return

        # Check if server has tool decorator
        if not hasattr(self.server, "tool"):
            self.logger.warning("MCP server does not support tool decorator")
            return

        @self.server.tool()
        async def create_animation(
            script: str,
            output_path: str,
            quality: str = "medium_quality",
            scene_name: str = "Scene",
        ) -> Dict[str, Any]:
            """Create Manim animation from script.

            Args:
                script: Python script with Manim scene
                output_path: Path for output video
                quality: Manim quality setting
                scene_name: Name of scene class to render

            Returns:
                Result dictionary with success status and details
            """
            return await self._create_animation_impl(
                script, output_path, quality, scene_name
            )

        @self.server.tool()
        async def validate_script(script: str) -> Dict[str, Any]:
            """Validate Manim script syntax.

            Args:
                script: Python script to validate

            Returns:
                Validation result
            """
            try:
                compile(script, "<string>", "exec")
                return {"valid": True, "error": None}
            except SyntaxError as e:
                return {"valid": False, "error": str(e)}

        @self.server.tool()
        async def get_server_status() -> Dict[str, Any]:
            """Get server status and capabilities.

            Returns:
                Server status information
            """
            return {
                "manim_available": self.manim_available,
                "temp_dir": str(self.temp_dir),
                "version": "1.0.0",
            }

    async def _create_animation_impl(
        self,
        script: str,
        output_path: str,
        quality: str = "medium_quality",
        scene_name: str = "Scene",
    ) -> Dict[str, Any]:
        """Implementation of animation creation.

        Args:
            script: Python script with Manim scene
            output_path: Path for output video
            quality: Manim quality setting
            scene_name: Name of scene class to render

        Returns:
            Result dictionary
        """
        try:
            # Validate and sanitize paths
            output_path = sanitize_filename(output_path)
            temp_script_path = self.temp_dir / f"manim_scene_{hash(script) % 10000}.py"

            # Security validation
            try:
                validate_file_path(temp_script_path, self.temp_dir)
            except Exception as e:
                return {"success": False, "error": f"Security validation failed: {e}"}

            # Write script to temporary file
            temp_script_path.write_text(script, encoding="utf-8")

            if not self.manim_available:
                return {
                    "success": False,
                    "error": "Manim not available",
                    "fallback_recommended": True,
                }

            # Prepare Manim command
            cmd = [
                "manim",
                "-q",
                quality,
                "-o",
                output_path,
                str(temp_script_path),
                scene_name,
            ]

            self.logger.debug(f"Running Manim command: {' '.join(cmd)}")

            # Run Manim with timeout
            proc = await asyncio.create_subprocess_exec(
                *cmd,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                cwd=self.temp_dir,
            )

            try:
                stdout, stderr = await asyncio.wait_for(
                    proc.communicate(), timeout=300  # 5 minute timeout
                )
            except asyncio.TimeoutError:
                proc.kill()
                await proc.wait()
                return {
                    "success": False,
                    "error": "Animation generation timed out",
                    "timeout": True,
                }

            # Clean up temporary script
            try:
                temp_script_path.unlink()
            except OSError:
                pass  # Ignore cleanup errors

            if proc.returncode != 0:
                error_msg = stderr.decode("utf-8", errors="replace")
                return {
                    "success": False,
                    "error": f"Manim failed: {error_msg}",
                    "stdout": stdout.decode("utf-8", errors="replace"),
                    "returncode": proc.returncode,
                }

            # Check if output file was created
            output_file = Path(output_path)
            if not output_file.exists():
                # Manim might have created the file in a different location
                # Try to find it in the media directory
                media_dir = self.temp_dir / "media"
                if media_dir.exists():
                    for video_file in media_dir.rglob("*.mp4"):
                        if scene_name.lower() in video_file.name.lower():
                            # Move to desired location
                            shutil.move(str(video_file), output_path)
                            output_file = Path(output_path)
                            break

            if not output_file.exists():
                return {
                    "success": False,
                    "error": "Output file not created",
                    "stdout": stdout.decode("utf-8", errors="replace"),
                }

            return {
                "success": True,
                "output": str(output_file),
                "logs": stdout.decode("utf-8", errors="replace"),
                "size_bytes": output_file.stat().st_size,
            }

        except Exception as e:
            self.logger.exception("Unexpected error in animation creation")
            return {
                "success": False,
                "error": f"Unexpected error: {str(e)}",
                "exception_type": type(e).__name__,
            }

    def create_animation_sync(
        self,
        script: str,
        output_path: str,
        quality: str = "medium_quality",
        scene_name: str = "Scene",
    ) -> Dict[str, Any]:
        """Synchronous wrapper for animation creation.

        Args:
            script: Python script with Manim scene
            output_path: Path for output video
            quality: Manim quality setting
            scene_name: Name of scene class to render

        Returns:
            Result dictionary
        """
        if not self.manim_available:
            return {
                "success": False,
                "error": "Manim not available",
                "fallback_recommended": True,
            }

        try:
            # Run the async function in a new event loop
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            try:
                return loop.run_until_complete(
                    self._create_animation_impl(
                        script, output_path, quality, scene_name
                    )
                )
            finally:
                loop.close()
        except Exception as e:
            self.logger.exception("Error in synchronous animation creation")
            return {
                "success": False,
                "error": f"Synchronous execution failed: {str(e)}",
            }

    async def run_server(self):
        """Run the MCP server."""
        if not MCP_AVAILABLE:
            raise RuntimeError("MCP not available - cannot run server mode")

        if not self.server:
            raise RuntimeError("Server not initialized")

        async with stdio_server() as (read_stream, write_stream):
            await self.server.run(read_stream, write_stream)

    def cleanup(self):
        """Clean up temporary files and resources."""
        try:
            if self.temp_dir.exists():
                # Clean up old temporary files
                for temp_file in self.temp_dir.glob("manim_scene_*.py"):
                    try:
                        temp_file.unlink()
                    except OSError:
                        pass

                # Clean up media directories
                media_dir = self.temp_dir / "media"
                if media_dir.exists():
                    shutil.rmtree(media_dir, ignore_errors=True)
        except Exception as e:
            self.logger.warning(f"Cleanup failed: {e}")


# Global server instance
_global_server: Optional[ManimMCPServer] = None


def get_manim_server() -> ManimMCPServer:
    """Get global Manim MCP server instance.

    Returns:
        ManimMCPServer instance
    """
    global _global_server
    if _global_server is None:
        _global_server = ManimMCPServer()
    return _global_server


async def main():
    """Main entry point for running the server."""
    server = ManimMCPServer()
    try:
        await server.run_server()
    finally:
        server.cleanup()


if __name__ == "__main__":
    asyncio.run(main())
