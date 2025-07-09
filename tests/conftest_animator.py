"""Shared test fixtures for animator tests."""

import asyncio
from pathlib import Path
from unittest.mock import MagicMock, Mock

import pytest

from src.proof_sketcher.animator.models import (
    AnimationConfig,
    AnimationResponse,
    ManimConfig,
)
from src.proof_sketcher.generator.models import ProofSketch, ProofStep


@pytest.fixture
def animation_config():
    """Standard animation config for tests."""
    return AnimationConfig(max_memory_mb=512, max_processing_time=60.0)


@pytest.fixture
def manim_config(tmp_path):
    """Standard manim config for tests."""
    return ManimConfig(
        server_host="localhost",
        server_port=8080,
        output_dir=tmp_path / "animations",
        temp_dir=tmp_path / "temp",
        auto_start=False,  # Don't try to start real server
    )


@pytest.fixture
def sample_proof_sketch():
    """Create a sample proof sketch for testing."""
    return ProofSketch(
        theorem_name="test_theorem",
        introduction="Test introduction",
        key_steps=[
            ProofStep(
                step_number=1,
                description="First step",
                mathematical_content="a = b",
                tactics=["rfl"],
            ),
            ProofStep(
                step_number=2,
                description="Second step",
                mathematical_content="b = c",
                tactics=["simp"],
            ),
        ],
        conclusion="Test conclusion",
    )


@pytest.fixture
def mock_animation_response():
    """Create a mock animation response."""
    return AnimationResponse(
        video_path=Path("/tmp/test.mp4"),
        thumbnail_path=Path("/tmp/test_thumb.png"),
        duration=30.0,
        frame_count=900,
        size_bytes=1024000,
        metadata={"style": "modern", "quality": "high"},
    )


class MockMCPServer:
    """Mock MCP server for testing."""

    def __init__(self):
        self.is_running = False
        self.health_check_count = 0
        self.render_count = 0

    async def start(self):
        """Start mock server."""
        self.is_running = True
        return True

    async def stop(self):
        """Stop mock server."""
        self.is_running = False

    async def health_check(self):
        """Mock health check."""
        self.health_check_count += 1
        return self.is_running

    async def render_animation(self, request):
        """Mock animation rendering."""
        self.render_count += 1
        # Simulate some processing time
        await asyncio.sleep(0.1)

        return AnimationResponse(
            video_path=Path(f"/tmp/{request.theorem_name}.mp4"),
            duration=30.0,
            frame_count=900,
            size_bytes=1024000,
        )


@pytest.fixture
def mock_mcp_server():
    """Create mock MCP server."""
    return MockMCPServer()
