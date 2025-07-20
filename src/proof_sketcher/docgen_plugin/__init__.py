"""Doc-gen4 Educational Plugin System.

This module provides a plugin system for enhancing doc-gen4 generated documentation
with progressive educational explanations. It integrates seamlessly with the
existing doc-gen4 pipeline while adding educational value.

Key Components:
    ModuleProcessor: Enhances doc-gen4 JSON with educational content
    ContentGenerator: Creates progressive explanations for theorems
    TemplateEngine: Renders educational HTML templates
    LakeFacet: Integrates with Lake build system

Features:
    - Progressive educational explanations (beginner/intermediate/advanced)
    - Interactive learning elements and visualizations
    - Seamless integration with existing doc-gen4 workflow
    - Community tool compatibility (LeanExplore, ProofWidgets)
    - Performance optimization for large mathlib builds

Example:
    >>> from proof_sketcher.docgen_plugin import ModuleProcessor
    >>>
    >>> # Process doc-gen4 module JSON
    >>> processor = ModuleProcessor()
    >>> enhanced_json = processor.enhance_module_json(module_json)
    >>>
    >>> # Generate educational HTML
    >>> html = processor.render_educational_html(enhanced_json)

Architecture:
    doc-gen4 Module JSON → Educational Analysis → Progressive Content → Enhanced JSON
"""

from __future__ import annotations

from .content_generator import EducationalContentGenerator
from .module_processor import ModuleProcessor
from .template_engine import EducationalTemplateEngine

__all__ = [
    "EducationalContentGenerator",
    "EducationalTemplateEngine",
    "ModuleProcessor",
]
