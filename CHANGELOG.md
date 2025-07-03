# Changelog

All notable changes to Proof Sketcher will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.0] - 2025-07-03

### Added
- Initial release of Proof Sketcher
- Transform Lean 4 theorems into natural language explanations with synchronized animations
- Multi-format export support (HTML, Markdown, PDF, Jupyter)
- Lean 4 parser with Lake project support and advanced language constructs
- Natural language generation using Claude Code CLI
- Mathematical animations via Manim MCP protocol with fallback support
- Batch processing capability for multiple Lean files
- Offline mode for environments without API access
- Resource management with memory and disk space monitoring
- Comprehensive error handling and recovery strategies
- Template-based export system with customizable themes
- Caching system for improved performance
- 95%+ test coverage across all modules

### Features
- **Parser**: Extract theorem AST from Lean files with support for theorems, definitions, inductive types, structures, type classes, and namespaces
- **Generator**: Create natural language explanations with multiple styles (step-by-step, ELI5, mathematical)
- **Animator**: Generate synchronized animations with MCP server integration and fallback static generation
- **Exporter**: Multiple output formats with responsive design and template caching

### Security
- Input validation and safe subprocess execution
- Resource limits enforcement
- Security scanning in CI/CD pipeline (Bandit, Safety, Semgrep)

### Performance
- Processes ~1.1 theorems per second
- Efficient caching and parallel batch processing
- Memory-aware resource management
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