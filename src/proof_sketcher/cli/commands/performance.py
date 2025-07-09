"""Performance monitoring and optimization CLI commands."""

import asyncio
import json
import time
from pathlib import Path
from typing import Optional

import click

from ...core.monitoring import get_health_status, global_health_monitor
from ...core.optimization import get_optimization_stats
from ...core.performance import get_performance_report, global_monitor


@click.group()
def performance():
    """Performance monitoring and optimization commands."""
    pass


@performance.command()
@click.option(
    "--format",
    "output_format",
    type=click.Choice(["json", "prometheus", "table"]),
    default="table",
    help="Output format",
)
@click.option("--output", type=click.Path(), help="Output file (default: stdout)")
def status(output_format: str, output: Optional[str]):
    """Show current performance status and metrics."""
    try:
        if output_format == "table":
            _display_status_table()
        else:
            # Get comprehensive status
            status_data = {
                "health": get_health_status(),
                "performance": get_performance_report(),
                "optimization": get_optimization_stats(),
            }

            if output_format == "json":
                output_text = json.dumps(status_data, indent=2, default=str)
            elif output_format == "prometheus":
                output_text = global_health_monitor.export_metrics("prometheus")

            if output:
                Path(output).write_text(output_text)
                click.echo(f"Status exported to {output}")
            else:
                click.echo(output_text)

    except Exception as e:
        click.echo(f"Error getting performance status: {e}", err=True)
        raise click.Abort()


def _display_status_table():
    """Display status in a formatted table."""
    health_status = get_health_status()

    # Overall status
    overall = health_status["overall_status"]
    status_color = "green" if overall == "healthy" else "red"
    click.echo(f"Overall Status: {click.style(overall.upper(), fg=status_color)}")
    click.echo()

    # Health checks
    click.echo("Health Checks:")
    click.echo("-" * 50)
    for name, check in health_status["health_checks"].items():
        status_icon = "✓" if check["status"] == "pass" else "✗"
        status_color = "green" if check["status"] == "pass" else "red"
        critical_marker = " (CRITICAL)" if check["critical"] else ""

        click.echo(
            f"{click.style(status_icon, fg=status_color)} {name}{critical_marker}"
        )
        click.echo(f"  {check['description']}")

        if check["last_error"]:
            click.echo(f"  Error: {click.style(check['last_error'], fg='red')}")

        if check["last_run"]:
            last_run = time.strftime(
                "%Y-%m-%d %H:%M:%S", time.localtime(check["last_run"])
            )
            click.echo(f"  Last run: {last_run}")

        click.echo()

    # System metrics
    system = health_status["system_metrics"]
    click.echo("System Metrics:")
    click.echo("-" * 50)
    click.echo(f"CPU Usage: {system.get('cpu_percent', 0):.1f}%")
    click.echo(f"Memory Usage: {system.get('memory_percent', 0):.1f}%")
    click.echo(f"Disk Usage: {system.get('disk_percent', 0):.1f}%")
    click.echo(
        f"Process Memory: {system.get('process_memory', 0) / 1024 / 1024:.1f} MB"
    )
    click.echo()

    # Usage metrics
    usage = health_status["usage_metrics"]
    click.echo("Usage Metrics:")
    click.echo("-" * 50)
    click.echo(f"Theorems Processed: {usage.get('theorems_processed', 0)}")
    click.echo(f"Files Processed: {usage.get('files_processed', 0)}")
    click.echo(f"Exports Generated: {usage.get('exports_generated', 0)}")
    click.echo(f"Cache Hits: {usage.get('cache_hits', 0)}")
    click.echo(f"Cache Misses: {usage.get('cache_misses', 0)}")
    click.echo(f"Errors: {usage.get('errors_encountered', 0)}")

    # Cache hit rate
    total_cache_requests = usage.get("cache_hits", 0) + usage.get("cache_misses", 0)
    if total_cache_requests > 0:
        hit_rate = (usage.get("cache_hits", 0) / total_cache_requests) * 100
        hit_rate_color = (
            "green" if hit_rate > 70 else "yellow" if hit_rate > 40 else "red"
        )
        click.echo(
            f"Cache Hit Rate: {click.style(f'{hit_rate:.1f}%', fg=hit_rate_color)}"
        )

    click.echo()

    # Recent alerts
    alerts = health_status["alert_summary"]
    if alerts["recent_alerts"] > 0:
        click.echo("Recent Alerts:")
        click.echo("-" * 50)
        click.echo(f"Total alerts in last hour: {alerts['recent_alerts']}")
        click.echo(f"Critical alerts: {alerts['critical_alerts']}")
        click.echo()


@performance.command()
@click.option(
    "--interval", type=float, default=30.0, help="Monitoring interval in seconds"
)
@click.option(
    "--duration", type=float, help="How long to monitor (seconds, default: indefinite)"
)
def monitor(interval: float, duration: Optional[float]):
    """Start continuous performance monitoring."""

    async def run_monitoring():
        try:
            click.echo(f"Starting performance monitoring (interval: {interval}s)")
            if duration:
                click.echo(f"Monitoring for {duration} seconds...")
            else:
                click.echo("Monitoring indefinitely (Ctrl+C to stop)...")

            await global_health_monitor.start_monitoring(interval)

            if duration:
                await asyncio.sleep(duration)
                await global_health_monitor.stop_monitoring()
                click.echo("Monitoring completed")
            else:
                # Monitor until interrupted
                try:
                    while True:
                        await asyncio.sleep(1)
                except KeyboardInterrupt:
                    click.echo("\nStopping monitoring...")
                    await global_health_monitor.stop_monitoring()
                    click.echo("Monitoring stopped")

        except Exception as e:
            click.echo(f"Monitoring error: {e}", err=True)
            raise click.Abort()

    try:
        asyncio.run(run_monitoring())
    except KeyboardInterrupt:
        click.echo("\nMonitoring interrupted")


@performance.command()
@click.option(
    "--output-dir",
    type=click.Path(),
    default="benchmark_results",
    help="Output directory for benchmark results",
)
@click.option(
    "--scales",
    type=str,
    default="1,5,10,20",
    help="Comma-separated list of scales to test",
)
def benchmark(output_dir: str, scales: str):
    """Run performance benchmarks to measure optimizations."""
    try:
        # Parse scales
        scale_list = [int(s.strip()) for s in scales.split(",")]

        click.echo("Starting performance benchmark...")
        click.echo(f"Testing scales: {scale_list}")
        click.echo(f"Results will be saved to: {output_dir}")

        # Import benchmark here to avoid circular imports
        import sys

        sys.path.append(".")
        from benchmark_performance import PerformanceBenchmark

        async def run_benchmark():
            benchmark_runner = PerformanceBenchmark(Path(output_dir))
            await benchmark_runner.run_all_benchmarks()

        asyncio.run(run_benchmark())

        click.echo()
        click.echo(click.style("Benchmark completed!", fg="green"))
        click.echo(f"Results saved to: {output_dir}")
        click.echo(f"Performance report: {Path(output_dir) / 'performance_report.md'}")

    except Exception as e:
        click.echo(f"Benchmark failed: {e}", err=True)
        raise click.Abort()


@performance.command()
@click.option("--metric", type=str, help="Specific metric to show (default: all)")
@click.option(
    "--format",
    "output_format",
    type=click.Choice(["table", "json"]),
    default="table",
    help="Output format",
)
def metrics(metric: Optional[str], output_format: str):
    """Show detailed performance metrics."""
    try:
        # Get all metrics
        perf_report = get_performance_report()

        if metric:
            # Show specific metric
            if metric in perf_report.get("application", {}).get("metrics", {}):
                metric_data = perf_report["application"]["metrics"][metric]
                if output_format == "json":
                    click.echo(json.dumps({metric: metric_data}, indent=2))
                else:
                    click.echo(f"Metric: {metric}")
                    click.echo(f"Count: {metric_data.get('count', 0)}")
                    click.echo(
                        f"Min: {metric_data.get('min', 0):.3f} {metric_data.get('unit', '')}"
                    )
                    click.echo(
                        f"Max: {metric_data.get('max', 0):.3f} {metric_data.get('unit', '')}"
                    )
                    click.echo(
                        f"Average: {metric_data.get('avg', 0):.3f} {metric_data.get('unit', '')}"
                    )
                    click.echo(
                        f"Latest: {metric_data.get('latest', 0):.3f} {metric_data.get('unit', '')}"
                    )
            else:
                click.echo(f"Metric '{metric}' not found", err=True)
                raise click.Abort()
        else:
            # Show all metrics
            if output_format == "json":
                click.echo(json.dumps(perf_report, indent=2, default=str))
            else:
                _display_metrics_table(perf_report)

    except Exception as e:
        click.echo(f"Error getting metrics: {e}", err=True)
        raise click.Abort()


def _display_metrics_table(perf_report: dict):
    """Display metrics in table format."""
    # Application metrics
    app_metrics = perf_report.get("application", {}).get("metrics", {})
    if app_metrics:
        click.echo("Application Metrics:")
        click.echo("-" * 80)
        click.echo(
            f"{'Metric':<30} {'Count':<8} {'Min':<10} {'Max':<10} {'Avg':<10} {'Latest':<10}"
        )
        click.echo("-" * 80)

        for name, data in app_metrics.items():
            unit = data.get("unit", "")
            click.echo(
                f"{name:<30} "
                f"{data.get('count', 0):<8} "
                f"{data.get('min', 0):<10.3f} "
                f"{data.get('max', 0):<10.3f} "
                f"{data.get('avg', 0):<10.3f} "
                f"{data.get('latest', 0):<10.3f}"
            )
        click.echo()

    # Counters
    app_counters = perf_report.get("application", {}).get("counters", {})
    if app_counters:
        click.echo("Counters:")
        click.echo("-" * 40)
        for name, count in app_counters.items():
            click.echo(f"{name:<30} {count:>8}")
        click.echo()

    # System metrics
    system = perf_report.get("system", {})
    if system:
        click.echo("System Metrics:")
        click.echo("-" * 40)
        click.echo(f"CPU Usage: {system.get('cpu_percent', 0):.1f}%")

        memory = system.get("memory", {})
        if memory:
            click.echo(
                f"Memory Used: {memory.get('used', 0) / 1024 / 1024 / 1024:.1f} GB"
            )
            click.echo(
                f"Memory Available: {memory.get('available', 0) / 1024 / 1024 / 1024:.1f} GB"
            )
            click.echo(f"Memory Percent: {memory.get('percent', 0):.1f}%")

        disk = system.get("disk", {})
        if disk:
            click.echo(f"Disk Used: {disk.get('used', 0) / 1024 / 1024 / 1024:.1f} GB")
            click.echo(f"Disk Free: {disk.get('free', 0) / 1024 / 1024 / 1024:.1f} GB")
            click.echo(f"Disk Percent: {disk.get('percent', 0):.1f}%")


@performance.command()
@click.option("--clear-metrics", is_flag=True, help="Clear performance metrics")
@click.option("--clear-cache", is_flag=True, help="Clear optimization cache")
@click.option("--clear-alerts", is_flag=True, help="Clear alert history")
def reset(clear_metrics: bool, clear_cache: bool, clear_alerts: bool):
    """Reset performance monitoring data."""
    try:
        if not any([clear_metrics, clear_cache, clear_alerts]):
            click.echo("Nothing to reset. Use --help to see options.")
            return

        if clear_metrics:
            # Reset global monitor metrics
            global_monitor._metrics.clear()
            global_monitor._counters.clear()
            global_monitor._timers.clear()
            click.echo("Performance metrics cleared")

        if clear_cache:
            from ...core.optimization import cache_manager

            cache_manager.clear()
            click.echo("Optimization cache cleared")

        if clear_alerts:
            global_health_monitor.alert_history.clear()
            click.echo("Alert history cleared")

        click.echo("Reset completed")

    except Exception as e:
        click.echo(f"Reset failed: {e}", err=True)
        raise click.Abort()


@performance.command()
def optimize():
    """Apply performance optimizations to the current session."""
    try:
        from ...core.optimization import optimize_batch_processor

        click.echo("Applying performance optimizations...")

        # Apply optimizations
        optimize_batch_processor()

        click.echo(click.style("Optimizations applied successfully!", fg="green"))
        click.echo()
        click.echo("Optimizations include:")
        click.echo("- Advanced caching with TTL")
        click.echo("- Batch processing optimization")
        click.echo("- Lazy loading for templates")
        click.echo("- Resource limiting and monitoring")
        click.echo("- Performance metric collection")
        click.echo()
        click.echo(
            "Use 'proof-sketcher performance benchmark' to measure improvements."
        )

    except Exception as e:
        click.echo(f"Optimization failed: {e}", err=True)
        raise click.Abort()
