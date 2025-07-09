"""
Intelligent export streaming - Milestone 3.2.1

This module provides memory-efficient streaming for large exports including:
- Incremental template rendering
- Memory-bounded buffering
- Progressive file writing
- Chunked content generation
- Backpressure handling
"""

import asyncio
import gzip
import io
import logging
import tempfile
import threading
import time
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, AsyncGenerator, Dict, List, Optional, TextIO, Union

from ..exporter.models import ExportContext, ExportFormat
from ..generator.models import ProofSketch


@dataclass
class StreamConfig:
    """Configuration for streaming export."""

    buffer_size_mb: int = 10
    chunk_size_kb: int = 64
    max_memory_mb: int = 100
    enable_compression: bool = True
    compression_level: int = 6
    write_batch_size: int = 100
    backpressure_threshold: int = 1000


@dataclass
class StreamStats:
    """Statistics for streaming operation."""

    total_bytes_written: int = 0
    total_chunks_processed: int = 0
    compression_ratio: float = 1.0
    peak_memory_mb: float = 0.0
    total_time: float = 0.0
    average_throughput_mbps: float = 0.0


class MemoryBoundedBuffer:
    """Memory-bounded buffer with backpressure."""

    def __init__(self, max_size_mb: int = 10):
        """Initialize buffer.

        Args:
            max_size_mb: Maximum buffer size in MB
        """
        self.max_size_bytes = max_size_mb * 1024 * 1024
        self.buffer = deque()
        self.current_size = 0
        self.lock = asyncio.Lock()
        self.not_full = asyncio.Condition(self.lock)
        self.not_empty = asyncio.Condition(self.lock)

    async def put(self, data: bytes):
        """Add data to buffer, waiting if full."""
        async with self.not_full:
            while self.current_size + len(data) > self.max_size_bytes:
                await self.not_full.wait()

            self.buffer.append(data)
            self.current_size += len(data)
            self.not_empty.notify()

    async def get(self) -> Optional[bytes]:
        """Get data from buffer, waiting if empty."""
        async with self.not_empty:
            while not self.buffer:
                await self.not_empty.wait()

            data = self.buffer.popleft()
            self.current_size -= len(data)
            self.not_full.notify()
            return data

    async def get_nowait(self) -> Optional[bytes]:
        """Get data without waiting."""
        async with self.lock:
            if self.buffer:
                data = self.buffer.popleft()
                self.current_size -= len(data)
                self.not_full.notify()
                return data
            return None

    def is_empty(self) -> bool:
        """Check if buffer is empty."""
        return len(self.buffer) == 0

    def size_bytes(self) -> int:
        """Get current buffer size."""
        return self.current_size


class ChunkedWriter:
    """Chunked file writer with compression support."""

    def __init__(
        self,
        output_path: Path,
        enable_compression: bool = True,
        compression_level: int = 6,
        buffer_size: int = 64 * 1024,
    ):
        """Initialize chunked writer.

        Args:
            output_path: Output file path
            enable_compression: Whether to enable compression
            compression_level: Compression level (1-9)
            buffer_size: Write buffer size
        """
        self.output_path = output_path
        self.enable_compression = enable_compression
        self.compression_level = compression_level
        self.buffer_size = buffer_size

        # Create output directory
        output_path.parent.mkdir(parents=True, exist_ok=True)

        # Initialize file handle
        if enable_compression and output_path.suffix != ".gz":
            self.output_path = output_path.with_suffix(output_path.suffix + ".gz")

        self.file_handle: Optional[Union[TextIO, gzip.GzipFile]] = None
        self.bytes_written = 0
        self.lock = threading.Lock()

    def open(self):
        """Open file for writing."""
        if self.enable_compression:
            self.file_handle = gzip.open(
                self.output_path,
                "wt",
                encoding="utf-8",
                compresslevel=self.compression_level,
            )
        else:
            self.file_handle = open(
                self.output_path, "w", encoding="utf-8", buffering=self.buffer_size
            )

    def write_chunk(self, data: str):
        """Write chunk of data."""
        if not self.file_handle:
            self.open()

        with self.lock:
            self.file_handle.write(data)
            self.bytes_written += len(data.encode("utf-8"))

    def flush(self):
        """Flush buffered data."""
        if self.file_handle:
            with self.lock:
                self.file_handle.flush()

    def close(self):
        """Close file."""
        if self.file_handle:
            with self.lock:
                self.file_handle.close()
                self.file_handle = None

    def __enter__(self):
        self.open()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()


class StreamingTemplateRenderer:
    """Template renderer with streaming support."""

    def __init__(self, template_manager, chunk_size_kb: int = 64):
        """Initialize streaming renderer.

        Args:
            template_manager: Template manager instance
            chunk_size_kb: Chunk size in KB
        """
        self.template_manager = template_manager
        self.chunk_size_bytes = chunk_size_kb * 1024
        self.logger = logging.getLogger(__name__)

    async def render_streaming(
        self,
        format_type: ExportFormat,
        template_name: str,
        context: Dict[str, Any],
        writer: ChunkedWriter,
    ) -> StreamStats:
        """Render template with streaming output.

        Args:
            format_type: Export format
            template_name: Template name
            context: Template context
            writer: Output writer

        Returns:
            Streaming statistics
        """
        start_time = time.time()
        stats = StreamStats()

        try:
            # For large contexts, break into chunks
            if self._is_large_context(context):
                await self._render_large_context_streaming(
                    format_type, template_name, context, writer, stats
                )
            else:
                # Standard rendering for small contexts
                content = self.template_manager.render_template(
                    format_type, template_name, context
                )
                await self._write_content_chunked(content, writer, stats)

            stats.total_time = time.time() - start_time
            stats.average_throughput_mbps = (
                (stats.total_bytes_written / 1024 / 1024) / stats.total_time
                if stats.total_time > 0
                else 0
            )

        except Exception as e:
            self.logger.error(f"Streaming render failed: {e}")
            raise

        return stats

    def _is_large_context(self, context: Dict[str, Any]) -> bool:
        """Check if context is large enough to require streaming."""
        # Estimate context size
        estimated_size = 0

        if "sketches" in context:
            sketches = context["sketches"]
            estimated_size += len(sketches) * 10000  # Rough estimate per sketch

        if "proof_steps" in context:
            steps = context["proof_steps"]
            estimated_size += len(steps) * 1000  # Rough estimate per step

        return estimated_size > 100000  # 100KB threshold

    async def _render_large_context_streaming(
        self,
        format_type: ExportFormat,
        template_name: str,
        context: Dict[str, Any],
        writer: ChunkedWriter,
        stats: StreamStats,
    ):
        """Render large context with streaming."""
        # Break context into smaller chunks
        if "sketches" in context and len(context["sketches"]) > 10:
            await self._render_sketches_streaming(
                format_type, template_name, context, writer, stats
            )
        else:
            # Fallback to regular rendering
            content = self.template_manager.render_template(
                format_type, template_name, context
            )
            await self._write_content_chunked(content, writer, stats)

    async def _render_sketches_streaming(
        self,
        format_type: ExportFormat,
        template_name: str,
        context: Dict[str, Any],
        writer: ChunkedWriter,
        stats: StreamStats,
    ):
        """Render sketches with streaming."""
        sketches = context["sketches"]
        chunk_size = 5  # Process 5 sketches at a time

        # Render header
        header_context = {**context, "sketches": []}
        header_template = f"{template_name}_header"

        try:
            header_content = self.template_manager.render_template(
                format_type, header_template, header_context
            )
        except Exception:
            # Fallback to full template with empty sketches
            header_content = self.template_manager.render_template(
                format_type, template_name, header_context
            )

        await self._write_content_chunked(header_content, writer, stats)

        # Render sketches in chunks
        for i in range(0, len(sketches), chunk_size):
            chunk_sketches = sketches[i : i + chunk_size]
            chunk_context = {**context, "sketches": chunk_sketches}

            # Render chunk
            try:
                chunk_template = f"{template_name}_chunk"
                chunk_content = self.template_manager.render_template(
                    format_type, chunk_template, chunk_context
                )
            except Exception:
                # Fallback to individual sketch rendering
                chunk_content = ""
                for sketch in chunk_sketches:
                    sketch_context = {**context, "sketch": sketch}
                    sketch_content = self.template_manager.render_template(
                        format_type, "sketch", sketch_context
                    )
                    chunk_content += sketch_content

            await self._write_content_chunked(chunk_content, writer, stats)

            # Allow other tasks to run
            await asyncio.sleep(0)

        # Render footer
        footer_context = {**context, "sketches": []}
        footer_template = f"{template_name}_footer"

        try:
            footer_content = self.template_manager.render_template(
                format_type, footer_template, footer_context
            )
            await self._write_content_chunked(footer_content, writer, stats)
        except Exception:
            # No footer template, that's okay
            pass

    async def _write_content_chunked(
        self, content: str, writer: ChunkedWriter, stats: StreamStats
    ):
        """Write content in chunks."""
        if not content:
            return

        # Split content into chunks
        for i in range(0, len(content), self.chunk_size_bytes):
            chunk = content[i : i + self.chunk_size_bytes]

            # Write chunk
            await asyncio.to_thread(writer.write_chunk, chunk)

            # Update stats
            stats.total_bytes_written += len(chunk.encode("utf-8"))
            stats.total_chunks_processed += 1

            # Allow other tasks to run
            await asyncio.sleep(0)


class StreamingExporter:
    """Main streaming exporter with memory management."""

    def __init__(self, config: StreamConfig = None):
        """Initialize streaming exporter.

        Args:
            config: Streaming configuration
        """
        self.config = config or StreamConfig()
        self.logger = logging.getLogger(__name__)

        # Memory monitoring
        self.peak_memory = 0.0
        self.current_memory = 0.0

    async def export_large_dataset(
        self,
        sketches: List[ProofSketch],
        output_path: Path,
        format_type: ExportFormat,
        template_manager,
        context: ExportContext = None,
    ) -> StreamStats:
        """Export large dataset with streaming.

        Args:
            sketches: List of proof sketches
            output_path: Output file path
            format_type: Export format
            template_manager: Template manager
            context: Export context

        Returns:
            Export statistics
        """
        self.logger.info(f"Starting streaming export of {len(sketches)} sketches")

        start_time = time.time()
        total_stats = StreamStats()

        # Create context if not provided
        if context is None:
            context = ExportContext(
                format=format_type, output_dir=output_path.parent, sketches=sketches
            )

        # Create streaming components
        writer = ChunkedWriter(
            output_path,
            enable_compression=self.config.enable_compression,
            compression_level=self.config.compression_level,
        )

        renderer = StreamingTemplateRenderer(
            template_manager, chunk_size_kb=self.config.chunk_size_kb
        )

        try:
            with writer:
                # Create template context
                template_context = {
                    "sketches": sketches,
                    "context": context,
                    "total_sketches": len(sketches),
                    "format": format_type.value,
                    "streaming": True,
                }

                # Determine template name
                template_name = self._get_template_name(format_type)

                # Render with streaming
                stats = await renderer.render_streaming(
                    format_type, template_name, template_context, writer
                )

                # Update total stats
                total_stats.total_bytes_written = stats.total_bytes_written
                total_stats.total_chunks_processed = stats.total_chunks_processed
                total_stats.total_time = time.time() - start_time

                # Calculate compression ratio
                if self.config.enable_compression:
                    uncompressed_size = writer.bytes_written
                    compressed_size = (
                        output_path.stat().st_size if output_path.exists() else 0
                    )
                    total_stats.compression_ratio = (
                        compressed_size / uncompressed_size
                        if uncompressed_size > 0
                        else 1.0
                    )

                # Calculate throughput
                total_stats.average_throughput_mbps = (
                    (total_stats.total_bytes_written / 1024 / 1024)
                    / total_stats.total_time
                    if total_stats.total_time > 0
                    else 0
                )

        except Exception as e:
            self.logger.error(f"Streaming export failed: {e}")
            raise

        self.logger.info(
            f"Streaming export completed: {total_stats.total_bytes_written:,} bytes "
            f"in {total_stats.total_time:.2f}s "
            f"({total_stats.average_throughput_mbps:.2f} MB/s)"
        )

        return total_stats

    def _get_template_name(self, format_type: ExportFormat) -> str:
        """Get template name for format."""
        template_map = {
            ExportFormat.HTML: "index",
            ExportFormat.MARKDOWN: "index",
            ExportFormat.PDF: "document",
            ExportFormat.JUPYTER: "notebook",
        }

        return template_map.get(format_type, "index")

    async def export_with_memory_limit(
        self,
        sketches: List[ProofSketch],
        output_path: Path,
        format_type: ExportFormat,
        template_manager,
        memory_limit_mb: int = 100,
    ) -> StreamStats:
        """Export with strict memory limit."""
        # Monitor memory usage
        import psutil

        process = psutil.Process()

        initial_memory = process.memory_info().rss / 1024 / 1024

        # Use smaller chunks for memory-constrained export
        config = StreamConfig(
            buffer_size_mb=min(self.config.buffer_size_mb, memory_limit_mb // 4),
            chunk_size_kb=min(self.config.chunk_size_kb, 16),
            max_memory_mb=memory_limit_mb,
        )

        # Process in smaller batches
        batch_size = max(1, memory_limit_mb // 10)  # Rough heuristic

        all_stats = []

        for i in range(0, len(sketches), batch_size):
            batch_sketches = sketches[i : i + batch_size]

            # Check memory usage
            current_memory = process.memory_info().rss / 1024 / 1024
            memory_used = current_memory - initial_memory

            if memory_used > memory_limit_mb * 0.8:  # 80% threshold
                # Force garbage collection
                import gc

                gc.collect()

                current_memory = process.memory_info().rss / 1024 / 1024
                memory_used = current_memory - initial_memory

                if memory_used > memory_limit_mb:
                    self.logger.warning(
                        f"Memory limit exceeded: {memory_used:.1f}MB > {memory_limit_mb}MB"
                    )

            # Export batch
            batch_output = output_path.with_name(
                f"{output_path.stem}_batch_{i // batch_size}{output_path.suffix}"
            )

            batch_stats = await self.export_large_dataset(
                batch_sketches, batch_output, format_type, template_manager
            )

            all_stats.append(batch_stats)

        # Combine batch files if needed
        if len(all_stats) > 1:
            await self._combine_batch_files(output_path, all_stats)

        # Return combined stats
        total_stats = StreamStats()
        for stats in all_stats:
            total_stats.total_bytes_written += stats.total_bytes_written
            total_stats.total_chunks_processed += stats.total_chunks_processed
            total_stats.total_time += stats.total_time

        return total_stats

    async def _combine_batch_files(
        self, output_path: Path, batch_stats: List[StreamStats]
    ):
        """Combine batch files into single output."""
        # This would depend on the specific format
        # For now, just log that batching occurred
        self.logger.info(
            f"Exported in {len(batch_stats)} batches, combination may be needed"
        )


# Utility functions for streaming export


async def stream_export_html(
    sketches: List[ProofSketch],
    output_path: Path,
    template_manager,
    config: StreamConfig = None,
) -> StreamStats:
    """Stream export HTML format."""
    exporter = StreamingExporter(config)
    return await exporter.export_large_dataset(
        sketches, output_path, ExportFormat.HTML, template_manager
    )


async def stream_export_markdown(
    sketches: List[ProofSketch],
    output_path: Path,
    template_manager,
    config: StreamConfig = None,
) -> StreamStats:
    """Stream export Markdown format."""
    exporter = StreamingExporter(config)
    return await exporter.export_large_dataset(
        sketches, output_path, ExportFormat.MARKDOWN, template_manager
    )


def estimate_memory_usage(sketches: List[ProofSketch]) -> int:
    """Estimate memory usage for export in MB."""
    # Rough estimation based on sketch content
    total_chars = 0

    for sketch in sketches:
        total_chars += len(sketch.introduction or "")
        total_chars += len(sketch.conclusion or "")
        total_chars += sum(len(step.description or "") for step in sketch.key_steps)
        total_chars += sum(
            len(step.mathematical_content or "") for step in sketch.key_steps
        )

    # Estimate memory usage (rough multiplier for template overhead)
    estimated_mb = (total_chars * 3) / 1024 / 1024

    return max(1, int(estimated_mb))


def should_use_streaming(
    sketches: List[ProofSketch], memory_limit_mb: int = 100
) -> bool:
    """Determine if streaming should be used based on data size."""
    estimated_memory = estimate_memory_usage(sketches)
    return estimated_memory > memory_limit_mb * 0.5  # Use streaming if > 50% of limit
