"""Alpha warning utilities."""

from __future__ import annotations

import os
from datetime import datetime


def should_show_warning() -> bool:
    """Check if the alpha warning should be shown."""
    # Check environment variable to suppress warning
    if os.environ.get("PROOF_SKETCHER_SUPPRESS_WARNING") == "1":
        return False

    # Check if warning was recently shown (within same session)
    warning_file = os.path.expanduser("~/.proof_sketcher_warning_shown")
    if os.path.exists(warning_file):
        try:
            with open(warning_file) as f:
                last_shown = datetime.fromisoformat(f.read().strip())
                # Show warning once per day
                if (datetime.now() - last_shown).days < 1:
                    return False
        except (ValueError, OSError, PermissionError):
            pass

    return True


def print_cli_warning() -> None:
    """Print the alpha software warning."""
    from rich.console import Console
    from rich.panel import Panel
    from rich.text import Text

    console = Console()

    warning_text = Text()
    warning_text.append("⚠️  ALPHA SOFTWARE WARNING ⚠️\n\n", style="bold red")
    warning_text.append(
        "This is experimental software with known issues:\n", style="yellow"
    )
    warning_text.append("• Limited theorem parsing functionality\n", style="yellow")
    warning_text.append("• Security vulnerabilities present\n", style="yellow")
    warning_text.append("• Low test coverage (11%)\n", style="yellow")
    warning_text.append("• NOT suitable for production use\n\n", style="yellow")
    warning_text.append("For testing and development only.\n", style="italic")
    warning_text.append("See docs/production-status.md for details.", style="dim")

    panel = Panel(
        warning_text,
        title="[bold red]PROOF SKETCHER ALPHA[/bold red]",
        border_style="red",
        padding=(1, 2),
    )

    console.print(panel)
    console.print()

    # Record that warning was shown
    try:
        warning_file = os.path.expanduser("~/.proof_sketcher_warning_shown")
        with open(warning_file, "w") as f:
            f.write(datetime.now().isoformat())
    except (OSError, PermissionError):
        pass
