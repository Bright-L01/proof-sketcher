"""Parser configuration."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict


@dataclass
class ParserConfig:
    """Configuration for the Lean parser."""

    # Parser behavior
    timeout: int = 30
    timeout_seconds: int = 30  # Alternative field name for compatibility
    max_file_size: int = 10_000_000  # 10MB
    encoding: str = "utf-8"

    # Lean settings
    lean_executable: str = "lean"
    lake_executable: str = "lake"
    search_paths: list[str] = field(default_factory=list)

    # Feature flags
    use_lsp: bool = False  # DEPRECATED: LSP is non-functional, always use False
    extract_proofs: bool = True
    extract_comments: bool = True
    extract_tactics: bool = True
    calculate_complexity: bool = False
    include_dependencies: bool = False

    # Error handling
    strict_mode: bool = False
    continue_on_error: bool = True

    # Notation handling
    unicode_map: Dict[str, str] = field(
        default_factory=lambda: {
            "forall": "∀",
            "exists": "∃",
            "Nat": "ℕ",
            "Real": "ℝ",
            "subset": "⊆",
            "union": "∪",
            "intersection": "∩",
            "alpha": "α",
            "beta": "β",
            "gamma": "γ",
            "delta": "δ",
            "epsilon": "ε",
            "varepsilon": "ε",
            "to": "→",
            "rarr": "→",
            "in": "∈",
        }
    )

    latex_map: Dict[str, str] = field(
        default_factory=lambda: {
            "∀": "\\forall",
            "∃": "\\exists",
            "ℕ": "\\mathbb{N}",
            "ℝ": "\\mathbb{R}",
            "⊆": "\\subseteq",
            "∪": "\\cup",
            "∩": "\\cap",
            "α": "\\alpha",
            "β": "\\beta",
            "γ": "\\gamma",
            "δ": "\\delta",
            "ε": "\\varepsilon",
            "→": "\\to",
            "∈": "\\in",
        }
    )

    def __post_init__(self):
        """Validate configuration."""
        # Sync timeout fields
        if hasattr(self, "timeout_seconds") and self.timeout_seconds != self.timeout:
            self.timeout = self.timeout_seconds

        if self.timeout <= 0 or self.timeout_seconds <= 0:
            raise ValueError("timeout must be positive")
        if self.max_file_size <= 0:
            raise ValueError("max_file_size must be positive")

        # Warn if LSP is enabled
        if self.use_lsp:
            import warnings

            warnings.warn(
                "LSP integration is deprecated and non-functional. "
                "It extracts 0 theorems and is 1000x slower than the simple parser. "
                "Setting use_lsp=False automatically.",
                DeprecationWarning,
                stacklevel=2,
            )
            self.use_lsp = False

    @classmethod
    def from_file(cls, file_path: str) -> ParserConfig:
        """Load configuration from a file.

        Args:
            file_path: Path to configuration file

        Returns:
            ParserConfig instance
        """
        import json
        from pathlib import Path

        path = Path(file_path)
        if not path.exists():
            raise FileNotFoundError(f"Config file not found: {file_path}")

        with open(path, "r") as f:
            data = json.load(f)

        return cls(**data)

    def model_dump(self) -> dict:
        """Export configuration as dictionary (Pydantic-style interface).

        Returns:
            Dictionary representation of config
        """
        from dataclasses import asdict

        return asdict(self)

    def convert_to_unicode(self, text: str) -> str:
        """Convert ASCII mathematical symbols to Unicode.

        Args:
            text: Text to convert

        Returns:
            Text with Unicode symbols
        """
        result = text
        for ascii_form, unicode_form in self.unicode_map.items():
            result = result.replace(ascii_form, unicode_form)
        return result

    def convert_to_latex(self, text: str) -> str:
        """Convert Unicode mathematical symbols to LaTeX.

        Args:
            text: Text to convert

        Returns:
            Text with LaTeX symbols
        """
        result = text
        for unicode_form, latex_form in self.latex_map.items():
            result = result.replace(unicode_form, latex_form)
        return result

    def convert_to_html(self, text: str) -> str:
        """Convert Unicode mathematical symbols to HTML entities.

        Args:
            text: Text to convert

        Returns:
            Text with HTML entities
        """
        html_map = {
            "∀": "&forall;",
            "∃": "&exist;",
            "ℕ": "&#8469;",
            "ℝ": "&#8477;",
            "→": "&rarr;",
            "∈": "&isin;",
            "⊆": "&sube;",
            "∪": "&cup;",
            "∩": "&cap;",
        }

        result = text
        for unicode_form, html_form in html_map.items():
            result = result.replace(unicode_form, html_form)
        return result

    def enhance_theorem(self, theorem_info):
        """Enhance a theorem with notation improvements.

        Args:
            theorem_info: TheoremInfo object to enhance

        Returns:
            Enhanced TheoremInfo object
        """
        from .models import TheoremInfo

        enhanced_statement = self.convert_to_unicode(theorem_info.statement)

        return TheoremInfo(
            name=theorem_info.name,
            statement=enhanced_statement,
            proof=theorem_info.proof,
            dependencies=theorem_info.dependencies,
            line_number=theorem_info.line_number,
            docstring=theorem_info.docstring,
            namespace=theorem_info.namespace,
            visibility=theorem_info.visibility,
            tactics=theorem_info.tactics,
            is_axiom=theorem_info.is_axiom,
            file_path=theorem_info.file_path,
            start_line=theorem_info.start_line,
            end_line=theorem_info.end_line,
        )
