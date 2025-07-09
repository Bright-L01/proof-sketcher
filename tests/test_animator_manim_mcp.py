"""Simplified tests for Manim MCP client focusing on core functionality."""

import asyncio
import subprocess
from pathlib import Path
from unittest.mock import AsyncMock, Mock, patch

import pytest

from proof_sketcher.animator.manim_mcp import ManimMCPClient
from proof_sketcher.animator.models import (
    AnimationConfig,
    AnimationRequest,
    AnimationResponse,
    AnimationScene,
    AnimationSegment,
    ManimConfig,
    TransformationType,
)


class TestManimMCPClientCore:
    """Core functionality tests for ManimMCPClient."""

    @pytest.fixture
    def config(self, tmp_path):
        """Create a test ManimConfig."""
        return ManimConfig(
            server_host="localhost",
            server_port=8080,
            output_dir=tmp_path / "output",
            temp_dir=tmp_path / "temp",
            auto_start=True,
            auto_restart=True,
        )

    @pytest.fixture
    def client(self, config):
        """Create a ManimMCPClient instance."""
        return ManimMCPClient(config)

    @pytest.fixture
    def sample_scene(self):
        """Create a sample animation scene."""
        return AnimationScene(
            scene_id="test_scene",
            title="Test Scene",
            duration=2.0,
            initial_formula="x + y",
            final_formula="x + y + z",
            transformation_type=TransformationType.REWRITE,
        )

    @pytest.fixture
    def sample_segment(self, sample_scene):
        """Create a sample animation segment."""
        return AnimationSegment(
            segment_id="test_segment",
            title="Test Segment",
            scenes=[sample_scene],
            total_duration=2.0,
        )

    @pytest.fixture
    def sample_request(self, sample_segment):
        """Create a sample animation request."""
        return AnimationRequest(
            theorem_name="test_theorem",
            request_id="test_request_123",
            segments=[sample_segment],
        )

    def test_client_initialization_default_config(self):
        """Test client initialization with default config."""
        client = ManimMCPClient()

        assert client.config is not None
        assert isinstance(client.config, ManimConfig)
        assert client.server_process is None
        assert client.session_pool == []
        assert client.active_connections == 0

    def test_client_initialization_custom_config(self, config):
        """Test client initialization with custom config."""
        client = ManimMCPClient(config)

        assert client.config == config
        assert client.config.server_host == "localhost"
        assert client.config.server_port == 8080

    def test_is_server_running_no_process(self, client):
        """Test is_server_running with no process."""
        assert client.is_server_running() is False

    def test_is_server_running_with_process(self, client):
        """Test is_server_running with running process."""
        # Mock a running process
        mock_process = Mock()
        mock_process.poll.return_value = None  # Process is running
        client.server_process = mock_process

        assert client.is_server_running() is True

    def test_is_server_running_with_dead_process(self, client):
        """Test is_server_running with dead process."""
        # Mock a dead process
        mock_process = Mock()
        mock_process.poll.return_value = 1  # Process has exited
        client.server_process = mock_process

        assert client.is_server_running() is False

    def test_build_server_command(self, client):
        """Test server command building."""
        cmd = client._build_server_command()

        assert isinstance(cmd, list)
        assert len(cmd) > 0
        assert "python" in cmd
        assert "-m" in cmd
        assert "manim_mcp_server" in cmd

    def test_config_get_server_url(self, config):
        """Test getting server URL from config."""
        url = config.get_server_url()
        assert url == "http://localhost:8080"

    @pytest.mark.asyncio
    async def test_start_server_already_running(self, client):
        """Test starting server when already running."""
        with patch.object(client, "is_server_running", return_value=True):
            result = await client.start_server()

        assert result is True

    @pytest.mark.asyncio
    async def test_start_server_auto_start_disabled(self, client):
        """Test starting server with auto_start disabled."""
        client.config.auto_start = False

        with patch.object(client, "is_server_running", return_value=False):
            result = await client.start_server()

        assert result is False

    @pytest.mark.asyncio
    async def test_stop_server_simple(self, client):
        """Test server stop without health check task."""
        client._health_check_task = None

        with patch.object(client, "_close_session_pool") as mock_close_pool:
            await client.stop_server()

            assert client._shutdown_event.is_set()
            mock_close_pool.assert_called_once()

    @pytest.mark.asyncio
    async def test_health_check_no_server(self, client):
        """Test health check when server is not available."""
        # Mock _get_session to raise an exception
        with patch.object(
            client, "_get_session", side_effect=Exception("Connection error")
        ):
            result = await client.health_check()

        assert result is False

    @pytest.mark.asyncio
    async def test_ensure_server_running_already_running(self, client):
        """Test ensuring server is running when it already is."""
        with patch.object(client, "health_check", return_value=True):
            result = await client._ensure_server_running()

        assert result is True

    @pytest.mark.asyncio
    async def test_ensure_server_running_start_needed(self, client):
        """Test ensuring server is running by starting it."""
        with (
            patch.object(client, "health_check", return_value=False),
            patch.object(client, "start_server", return_value=True),
        ):

            result = await client._ensure_server_running()

        assert result is True

    @pytest.mark.asyncio
    async def test_render_animation_server_unavailable(self, client, sample_request):
        """Test animation rendering when server can't be started."""
        with patch.object(client, "_ensure_server_running", return_value=False):
            response = await client.render_animation(sample_request)

        assert isinstance(response, AnimationResponse)
        assert response.success is False
        assert "Failed to start Manim server" in response.error_message

    @pytest.mark.asyncio
    async def test_render_animation_with_mocked_segments(self, client, sample_request):
        """Test successful animation rendering with mocked segment rendering."""
        with (
            patch.object(client, "_ensure_server_running", return_value=True),
            patch.object(client, "_render_segment", return_value=True),
            patch.object(client, "_generate_preview", return_value=True),
            patch.object(client, "_get_video_duration", return_value=2.0),
            patch("shutil.copy2"),
        ):  # Mock file operations

            response = await client.render_animation(sample_request)

        assert isinstance(response, AnimationResponse)
        assert response.success is True

    @pytest.mark.asyncio
    async def test_render_animation_segment_failure(self, client, sample_request):
        """Test animation rendering when segment rendering fails."""
        with (
            patch.object(client, "_ensure_server_running", return_value=True),
            patch.object(client, "_render_segment", return_value=False),
        ):

            response = await client.render_animation(sample_request)

        assert isinstance(response, AnimationResponse)
        assert response.success is False
        assert "Failed to render segment" in response.error_message

    @pytest.mark.asyncio
    async def test_close_session_pool(self, client):
        """Test closing session pool."""
        # Add mock sessions to pool
        mock_session1 = AsyncMock()
        mock_session2 = AsyncMock()
        client.session_pool.extend([mock_session1, mock_session2])

        await client._close_session_pool()

        # Check that close was called on both sessions
        mock_session1.close.assert_called_once()
        mock_session2.close.assert_called_once()
        assert len(client.session_pool) == 0

    def test_config_development(self):
        """Test development configuration."""
        config = ManimConfig.development()

        assert config.server_timeout == 60.0
        assert config.max_concurrent_renders == 1
        assert config.keep_temp_files is True

    def test_config_production(self):
        """Test production configuration."""
        config = ManimConfig.production()

        assert config.server_timeout == 600.0
        assert config.max_concurrent_renders == 4
        assert config.memory_limit_mb == 4096

    def test_animation_config_preview(self):
        """Test animation configuration for previews."""
        config = AnimationConfig.preview()

        assert config.quality.value == "low"
        assert config.fps == 15
        assert config.base_duration == 15.0

    def test_animation_config_publication(self):
        """Test animation configuration for publication."""
        config = AnimationConfig.publication()

        assert config.quality.value == "high"
        assert config.fps == 60
        assert config.width == 1920

    def test_animation_request_cache_key(self, sample_request):
        """Test cache key generation for animation requests."""
        cache_key = sample_request.get_cache_key()

        assert isinstance(cache_key, str)
        assert len(cache_key) == 64  # SHA256 hex string length

    def test_animation_request_duration_calculation(self, sample_request):
        """Test duration calculation for animation requests."""
        duration = sample_request.calculate_estimated_duration()

        assert duration > 0
        assert duration == sample_request.estimated_duration

    def test_transformation_type_enum(self):
        """Test transformation type enum values."""
        assert TransformationType.REWRITE == "rewrite"
        assert TransformationType.SUBSTITUTION == "substitution"
        assert TransformationType.SIMPLIFICATION == "simplification"
        assert TransformationType.EXPANSION == "expansion"

    @pytest.mark.asyncio
    async def test_concurrent_session_limiting(self, client):
        """Test that session pool respects max connections."""
        client.config.max_connections = 2
        client.active_connections = 2  # At limit

        # This should wait (we'll mock the sleep to avoid actual waiting)
        with patch("asyncio.sleep", new_callable=AsyncMock) as mock_sleep:
            async with client._get_session():
                pass

        # Should have called sleep since we were at the connection limit
        mock_sleep.assert_called()
