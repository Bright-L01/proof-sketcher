# Proof Sketcher Project

## Overview
Proof Sketcher transforms Lean 4 theorems into natural language explanations with synchronized mathematical animations. It integrates with mathlib4 and doc-gen4 to enhance Lean documentation.

## Architecture
- **Parser**: Extracts theorem AST from Lean files using subprocess
- **Generator**: Uses Claude API to create natural language explanations  
- **Animator**: Creates Manim animations via MCP server
- **Exporter**: Generates HTML, Markdown, PDF, and Jupyter outputs

## Key Design Decisions
1. Python implementation for accessibility
2. Claude Code CLI integration (no API costs for users)
3. Progressive enhancement with graceful degradation
4. Dynamic animation duration (30s + 15s per proof step, max 12min)
5. Multiple output formats for different use cases

## Current Phase
Phase 0: Foundation (Days 1-3)
- Set up CLI scaffold with Click
- Implement basic Lean file parsing
- Create JSON serialization for theorem AST

## Development Guidelines
- Use type hints throughout
- Follow black/ruff formatting
- Maintain 95%+ test coverage  
- Document all public APIs
- Handle errors gracefully

## Project Structure
src/proof_sketcher/
├── init.py
├── cli.py              # Click CLI entry point
├── parser/
│   ├── lean_parser.py  # Lean AST extraction
│   └── models.py       # Pydantic models
├── generator/
│   ├── claude.py       # Claude integration
│   └── prompts.py      # Prompt templates
├── animator/
│   ├── manim_mcp.py    # Manim MCP client
│   └── scenes.py       # Animation generators
└── exporter/
├── html.py         # HTML generation
├── markdown.py     # Markdown generation
├── pdf.py          # LaTeX/PDF generation
└── jupyter.py      # Notebook generation
