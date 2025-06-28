# Changelog

All notable changes to Proof Sketcher will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- Initial release of Proof Sketcher
- Lean 4 parser with Lake project support
- Natural language generation using Claude Code CLI
- Mathematical animations via Manim MCP protocol
- Multi-format export (HTML, Markdown, PDF, Jupyter)
- Comprehensive CLI with batch processing
- Smart caching system
- Configuration management
- Full test suite with 80%+ coverage
- CI/CD with GitHub Actions

### Parser Features
- Extract theorem names, types, and proofs
- Detect dependencies and tactics
- Parse docstrings and comments
- Support for Lake projects
- Graceful fallback to regex parsing

### Generator Features
- Multiple explanation types (concise, detailed, tutorial)
- Context-aware explanations
- Mathematical notation preservation
- Streaming support
- Response caching

### Animator Features
- Synchronized proof animations
- Multiple visual styles
- Customizable timing
- Formula extraction and conversion
- LaTeX rendering

### Exporter Features
- HTML with MathJax integration
- GitHub-flavored Markdown
- LaTeX/PDF generation
- Interactive Jupyter notebooks
- Template customization

## [0.1.0] - TBD

Initial public release.