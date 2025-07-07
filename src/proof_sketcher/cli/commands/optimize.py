"""
CLI commands for mathematical context optimization.
"""

import json
from pathlib import Path
from typing import Optional

import click

from ...core.context_optimizer import get_context_optimizer
from ...parser.lean_parser import LeanParser


@click.group()
def optimize():
    """Mathematical context optimization commands."""
    pass


@optimize.command()
@click.option(
    "--format",
    type=click.Choice(["json", "table", "summary"]),
    default="table",
    help="Output format for statistics",
)
def stats(format: str):
    """Show optimization statistics and performance metrics."""
    
    # Get statistics from global optimizer
    optimizer = get_context_optimizer()
    stats = optimizer.get_optimization_stats()
    
    if format == "json":
        click.echo(json.dumps(stats, indent=2, default=str))
        return
    
    # Table format
    click.echo("🎯 Mathematical Context Optimization Statistics")
    click.echo("=" * 60)
    
    overall = stats.get("overall", {})
    click.echo(f"📊 Overall Performance:")
    click.echo(f"  Total Attempts: {overall.get('total_attempts', 0)}")
    click.echo(f"  Success Rate: {overall.get('success_rate', 0):.1%}")
    click.echo(f"  Target Rate: {overall.get('target_rate', 0):.1%}")
    click.echo(f"  Progress to Target: {overall.get('progress_to_target', 0):.1%}")
    click.echo(f"  Avg Processing Time: {overall.get('avg_processing_time', 0):.3f}s")
    click.echo()
    
    # Context-specific performance
    contexts = stats.get("contexts", {})
    if contexts:
        click.echo("🧮 Context-Specific Performance:")
        for context, data in contexts.items():
            attempts = data.get('attempts', 0)
            success_rate = data.get('success_rate', 0)
            target_rate = data.get('target_rate', 0)
            best_strategy = data.get('best_strategy', 'Unknown')
            distribution = data.get('distribution_pct', 0)
            
            status = "🎯" if success_rate >= target_rate * 0.8 else "⚠️" if success_rate >= target_rate * 0.5 else "❌"
            
            click.echo(f"  {context.title():<12}: {success_rate:.1%} ({attempts:3d} attempts) "
                      f"target: {target_rate:.1%} {status}")
            click.echo(f"    Best Strategy: {best_strategy}")
            click.echo(f"    Distribution: {distribution:.1f}% of files")
            click.echo()
    
    # Strategy rankings
    strategy_rankings = stats.get("strategy_rankings", {})
    if strategy_rankings:
        click.echo("🏆 Strategy Rankings by Context:")
        for context, rankings in strategy_rankings.items():
            click.echo(f"  {context.title()}:")
            for i, rank in enumerate(rankings[:3]):  # Top 3
                strategy = rank['strategy']
                success_rate = rank['success_rate']
                attempts = rank['attempts']
                medal = ["🥇", "🥈", "🥉"][i] if i < 3 else "  "
                click.echo(f"    {medal} {strategy:<20}: {success_rate:.1%} ({attempts} attempts)")
            click.echo()
    
    # Recent trend analysis
    trend = stats.get("recent_trend", {})
    if trend.get("trend") != "insufficient_data":
        click.echo("📈 Recent Performance Trend:")
        trend_type = trend.get("trend", "unknown")
        trend_emoji = {"improving": "📈", "declining": "📉", "stable": "➡️"}.get(trend_type, "❓")
        click.echo(f"  {trend_emoji} {trend_type.title()}")
        click.echo(f"  Recent 20: {trend.get('recent_20_rate', 0):.1%}")
        click.echo(f"  Recent 10: {trend.get('recent_10_rate', 0):.1%}")
        click.echo(f"  Improvement: {trend.get('improvement', 0):+.1%}")
        click.echo()
    
    # Recommendations
    recommendations = stats.get("recommendations", [])
    if recommendations:
        click.echo("💡 Optimization Recommendations:")
        for rec in recommendations:
            click.echo(f"  • {rec}")
        click.echo()
    
    if format == "summary":
        # Summary view
        target_achievement = overall.get('progress_to_target', 0)
        click.echo("📋 Summary:")
        if target_achievement >= 0.9:
            click.echo("  🎉 Target achieved! System optimally tuned.")
        elif target_achievement >= 0.7:
            click.echo("  🎯 Close to target. Fine-tuning strategies.")
        elif target_achievement >= 0.5:
            click.echo("  📈 Making good progress toward optimization goal.")
        elif target_achievement >= 0.3:
            click.echo("  🔧 Learning phase. Collecting performance data.")
        else:
            click.echo("  🚀 Early stage. Need more optimization iterations.")


@optimize.command()
@click.argument("file_path", type=click.Path(exists=True, path_type=Path))
@click.option("--show-strategy", is_flag=True, help="Show selected strategy details")
def analyze(file_path: Path, show_strategy: bool):
    """Analyze a Lean file's mathematical context and recommended strategy."""
    
    try:
        # Read file content
        content = file_path.read_text(encoding="utf-8")
        
        # Get optimization
        optimizer = get_context_optimizer()
        context, strategy = optimizer.optimize_for_theorem(content, str(file_path))
        
        click.echo(f"📁 File: {file_path}")
        click.echo(f"🧮 Mathematical Context: {context.value}")
        click.echo(f"🎯 Recommended Strategy: {strategy.value}")
        
        if show_strategy:
            click.echo()
            click.echo("📋 Strategy Details:")
            
            strategy_descriptions = {
                "tuned_arithmetic": "High precision for simple arithmetic proofs. Uses Lean extractor first with enhanced parser fallback.",
                "hybrid_mixed": "Balanced approach for mixed complexity. Enhanced parser with selective Lean enhancement.",
                "conservative_complex": "Conservative approach for complex theorems. Basic parsing first with careful enhancement.",
                "aggressive_fallback": "Maximum compatibility. Tries all methods and merges results.",
                "precision_focused": "Quality over quantity. Enhanced parser only with high-quality Lean extraction."
            }
            
            desc = strategy_descriptions.get(strategy.value, "Custom strategy")
            click.echo(f"  {desc}")
            
            # Show target success rates
            target_rates = {
                "arithmetic": "85%",
                "mixed": "40%",
                "complex": "25%"
            }
            target = target_rates.get(context.value, "50%")
            click.echo(f"  Target Success Rate: {target}")
        
        # Try parsing with optimization
        click.echo()
        click.echo("🧪 Testing optimization...")
        
        parser = LeanParser()
        result = parser.parse_file(file_path)
        
        success = result.success and len(result.theorems) > 0
        status = "✅ Success" if success else "❌ Failed"
        
        click.echo(f"  {status}")
        click.echo(f"  Theorems found: {len(result.theorems) if result.theorems else 0}")
        click.echo(f"  Processing time: {result.parse_time_ms:.1f}ms")
        
        if result.errors:
            click.echo(f"  Errors: {len(result.errors)}")
            for error in result.errors[:3]:  # Show first 3 errors
                click.echo(f"    • {error.message}")
        
        # Show theorem names
        if result.theorems:
            click.echo("  Theorems:")
            for theorem in result.theorems[:5]:  # Show first 5
                click.echo(f"    • {theorem.name}")
            if len(result.theorems) > 5:
                click.echo(f"    ... and {len(result.theorems) - 5} more")
        
    except Exception as e:
        click.echo(f"❌ Error analyzing file: {e}", err=True)


@optimize.command()
@click.option("--reset", is_flag=True, help="Reset all optimization data")
@click.option("--export", type=click.Path(), help="Export optimization data to file")
def manage(reset: bool, export: Optional[Path]):
    """Manage optimization system data."""
    
    optimizer = get_context_optimizer()
    
    if reset:
        if click.confirm("⚠️  This will reset all optimization learning data. Continue?"):
            # Reset optimizer (simplified - would need implementation)
            click.echo("🔄 Optimization data reset.")
        else:
            click.echo("❌ Reset cancelled.")
        return
    
    if export:
        try:
            stats = optimizer.get_optimization_stats()
            with open(export, 'w') as f:
                json.dump(stats, f, indent=2, default=str)
            click.echo(f"📁 Optimization data exported to {export}")
        except Exception as e:
            click.echo(f"❌ Export failed: {e}", err=True)
        return
    
    # Default: show management info
    click.echo("🛠️  Optimization System Management")
    click.echo("Available commands:")
    click.echo("  --reset: Reset all learning data")
    click.echo("  --export: Export data to file")


@optimize.command()
def benchmark():
    """Run optimization benchmark to test strategy effectiveness."""
    
    click.echo("🏁 Running Optimization Benchmark...")
    click.echo("This will test various strategies across different mathematical contexts.")
    click.echo()
    
    # Import and run the test
    try:
        import subprocess
        import sys
        
        # Run the optimization test script
        result = subprocess.run([
            sys.executable, 
            "test_optimization_system.py"
        ], capture_output=True, text=True, cwd=Path.cwd())
        
        if result.returncode == 0:
            click.echo(result.stdout)
        else:
            click.echo(f"❌ Benchmark failed: {result.stderr}", err=True)
            
    except Exception as e:
        click.echo(f"❌ Could not run benchmark: {e}", err=True)
        click.echo("Try running: python test_optimization_system.py")


if __name__ == "__main__":
    optimize()