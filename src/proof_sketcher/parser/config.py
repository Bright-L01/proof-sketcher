"""Parser configuration."""

from dataclasses import dataclass, field


@dataclass
class ParserConfig:
    """Configuration for the Lean parser."""

    # Parser behavior
    timeout: int = 30
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

    # Error handling
    strict_mode: bool = False
    continue_on_error: bool = True

    def __post_init__(self):
        """Validate configuration."""
        if self.timeout <= 0:
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
                stacklevel=2
            )
            self.use_lsp = False
