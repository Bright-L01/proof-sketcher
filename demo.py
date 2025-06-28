#!/usr/bin/env python3
"""
Proof Sketcher Demo Script

This script demonstrates the core functionality of Proof Sketcher,
showing how it transforms Lean 4 theorems into natural language explanations.
"""

import sys
from pathlib import Path

from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax
from rich.table import Table

# Add src to path for demo
sys.path.insert(0, str(Path(__file__).parent / "src"))

from proof_sketcher.parser import LeanParser
from proof_sketcher.parser.config import ParserConfig

console = Console()

def demo_parser():
    """Demonstrate the Lean parser functionality."""
    console.print("\n[bold blue]🔍 Proof Sketcher Parser Demo[/bold blue]\n")

    # Create parser with fallback enabled
    config = ParserConfig(fallback_to_regex=True)
    parser = LeanParser(config)

    # Check Lean availability
    console.print(f"Lean available: {'✅' if parser.check_lean_available() else '❌'}")
    console.print(f"Lake available: {'✅' if parser.check_lake_available() else '❌'}")

    # Parse example file
    example_file = Path("examples/lean_project/ProofSketcherExamples/Nat.lean")

    if not example_file.exists():
        console.print(f"[red]Example file not found: {example_file}[/red]")
        return

    console.print(f"\n📄 Parsing: [cyan]{example_file}[/cyan]")

    # Show file content
    content = example_file.read_text()
    syntax = Syntax(content[:500] + "...", "lean", theme="monokai", line_numbers=True)
    console.print(Panel(syntax, title="File Content (Preview)"))

    # Parse file
    result = parser.parse_file(example_file)

    # Show results
    if result.success:
        console.print(f"\n✅ Parse successful! Found {len(result.theorems)} theorems\n")

        # Create table of theorems
        table = Table(title="Extracted Theorems")
        table.add_column("Name", style="cyan")
        table.add_column("Statement", style="white")
        table.add_column("Line", style="green")

        for theorem in result.theorems:
            statement = theorem.statement[:60] + "..." if len(theorem.statement) > 60 else theorem.statement
            table.add_row(theorem.name, statement, str(theorem.line_number))

        console.print(table)

        # Show detailed info for first theorem
        if result.theorems:
            theorem = result.theorems[0]
            console.print(f"\n[bold]Detailed View: {theorem.name}[/bold]")
            console.print(Panel(f"""
[cyan]Statement:[/cyan] {theorem.statement}

[cyan]Proof:[/cyan] {theorem.proof[:200] if theorem.proof else 'N/A'}...

[cyan]Dependencies:[/cyan] {', '.join(theorem.dependencies) if theorem.dependencies else 'None detected'}

[cyan]Docstring:[/cyan] {theorem.docstring or 'None'}
            """, title=f"Theorem: {theorem.name}"))
    else:
        console.print(f"[red]Parse failed with {len(result.errors)} errors[/red]")
        for error in result.errors:
            console.print(f"  - {error.message}")

def show_next_steps():
    """Show what would happen next in the pipeline."""
    console.print("\n[bold yellow]🚀 Next Steps (when Lean is installed):[/bold yellow]\n")

    steps = [
        ("1. Enhanced Parsing", "Extract tactics, dependencies, and docstrings using Lean 4 meta-programming"),
        ("2. Natural Language Generation", "Use Claude Code CLI to generate explanations"),
        ("3. Animation Creation", "Generate Manim animations via MCP server"),
        ("4. Multi-Format Export", "Create HTML, PDF, Markdown, and Jupyter outputs")
    ]

    for step, description in steps:
        console.print(f"  [green]{step}[/green]: {description}")

    console.print("\n[dim]Install Lean 4 and Claude Code CLI for full functionality[/dim]")

def show_example_output():
    """Show what the final output would look like."""
    console.print("\n[bold magenta]📝 Example Generated Explanation:[/bold magenta]\n")

    example_explanation = """
The theorem `nat_add_comm` states that addition of natural numbers is commutative.
In mathematical notation: ∀ (m n : Nat), m + n = n + m

**Proof Strategy**: We use mathematical induction on the first argument m.

**Base Case** (m = 0):
We need to show that 0 + n = n + 0. By the definition of addition, 0 + n = n.
We also know that n + 0 = n (a basic property). Therefore, 0 + n = n + 0.

**Inductive Step**:
Assume m + n = n + m (inductive hypothesis).
We need to show that (m + 1) + n = n + (m + 1).
Using the successor property of addition and our hypothesis, we complete the proof.

This fundamental property underpins many other results in arithmetic.
    """

    console.print(Panel(example_explanation.strip(), title="Generated Explanation", border_style="green"))

if __name__ == "__main__":
    console.print(Panel.fit(
        "[bold]Welcome to Proof Sketcher![/bold]\n\n"
        "Transform Lean 4 theorems into natural language explanations",
        border_style="blue"
    ))

    # Run demo
    demo_parser()
    show_next_steps()
    show_example_output()

    console.print("\n[bold green]✨ Demo complete![/bold green]")
    console.print("\nTo get started with full functionality:")
    console.print("  1. Install Lean 4: [link]https://leanprover.github.io/lean4/doc/setup.html[/link]")
    console.print("  2. Install Claude Code CLI: [link]https://github.com/anthropics/claude-code[/link]")
    console.print("  3. Run: [cyan]proof-sketcher prove your-theorem.lean[/cyan]\n")
