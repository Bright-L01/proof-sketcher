"""Sphinx configuration for Proof Sketcher API documentation.

⚠️ WARNING: This documents alpha software with significant limitations.
Many documented features may not work as described.
"""

import os
import sys
from pathlib import Path

# Add source path
sys.path.insert(0, os.path.abspath('../src'))

# Project information
project = 'Proof Sketcher'
copyright = '2025, Proof Sketcher Contributors'
author = 'Proof Sketcher Contributors'
version = '0.1.0-alpha'
release = '0.1.0-alpha'

# Extensions
extensions = [
    'sphinx.ext.autodoc',
    'sphinx.ext.napoleon',
    'sphinx.ext.viewcode',
    'sphinx.ext.intersphinx',
    'sphinx.ext.todo',
]

# Source file suffixes
source_suffix = {
    '.rst': None,
}

# Root document
master_doc = 'index'

# Language
language = 'en'

# Exclude patterns
exclude_patterns = [
    '_build',
    'Thumbs.db',
    '.DS_Store',
    '__pycache__',
]

# HTML theme
html_theme = 'sphinx_rtd_theme'
html_theme_options = {
    'navigation_depth': 4,
    'collapse_navigation': False,
    'sticky_navigation': True,
    'includehidden': True,
    'titles_only': False,
}

# HTML options
html_title = f"{project} {version} (Alpha)"
html_short_title = "Proof Sketcher API"
html_show_sourcelink = True
html_show_sphinx = True
html_show_copyright = True

# Static files
html_static_path = ['_static']

# Custom CSS
html_css_files = [
    'custom.css',
]

# AutoDoc options
autodoc_default_options = {
    'members': True,
    'member-order': 'bysource',
    'special-members': '__init__',
    'undoc-members': True,
    'exclude-members': '__weakref__',
    'show-inheritance': True,
}

# Napoleon settings (for Google/NumPy docstrings)
napoleon_google_docstring = True
napoleon_numpy_docstring = True
napoleon_include_init_with_doc = False
napoleon_include_private_with_doc = False
napoleon_include_special_with_doc = True
napoleon_use_admonition_for_examples = False
napoleon_use_admonition_for_notes = False
napoleon_use_admonition_for_references = False
napoleon_use_ivar = False
napoleon_use_param = True
napoleon_use_rtype = True

# Intersphinx mapping
intersphinx_mapping = {
    'python': ('https://docs.python.org/3', None),
    'pydantic': ('https://docs.pydantic.dev/latest/', None),
}

# Todo extension
todo_include_todos = True

# Custom warning for alpha software
rst_prolog = """
.. warning::
   This documentation covers **alpha software** with significant limitations.
   Many features described may not work as intended. See the 
   `Production Readiness Assessment <../PRODUCTION_READINESS_ASSESSMENT.md>`_ 
   for current status.
"""