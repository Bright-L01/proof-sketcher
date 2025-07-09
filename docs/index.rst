Proof Sketcher API Documentation
================================

.. warning::
   **Alpha Software Warning**: This documentation covers experimental software
   with significant limitations. See :doc:`production-status` for details.

Welcome to Proof Sketcher's API documentation. This covers the internal
architecture and programming interfaces for the proof explanation system.

Current Status
--------------

**Development Phase**: Alpha (0.1.0-alpha)

**Production Ready**: ❌ No

**Test Coverage**: 11% (Target: 70%+)

**Security Status**: ⚠️ 69 known vulnerabilities

Quick Links
-----------

- :doc:`user-guide` - Getting started (with limitations)
- :doc:`api/core` - Core modules (partially functional)
- :doc:`api/parser` - Lean parsing (limited functionality)
- :doc:`api/generator` - Content generation (offline only)
- :doc:`api/exporter` - Output generation (basic functionality)
- :doc:`production-status` - Current limitations and roadmap

What Actually Works
-------------------

✅ **Basic CLI Interface**
   The command-line interface is functional for basic operations.

✅ **File Processing**
   Can read Lean files and attempt parsing (with limitations).

✅ **Template Output**
   Generates HTML, Markdown, and Jupyter outputs using templates.

✅ **Offline Mode**
   Works without external dependencies (recommended mode).

What Doesn't Work Yet
---------------------

❌ **AI Integration**
   Claude API integration is incomplete. Use offline mode only.

❌ **Theorem Parsing**
   Often produces empty theorem statements due to parser issues.

❌ **Animations**
   Manim integration is broken. No working animations.

❌ **Content Quality**
   Generates generic templates, not theorem-specific explanations.

API Overview
------------

.. toctree::
   :maxdepth: 2
   :caption: User Documentation:

   user-guide
   production-status

.. toctree::
   :maxdepth: 3
   :caption: API Reference:

   api/core
   api/parser
   api/generator
   api/exporter
   api/animator
   api/batch

.. toctree::
   :maxdepth: 1
   :caption: Development:

   development
   contributing
   testing

Core Architecture
-----------------

The system is organized into several modules:

**Core** (`proof_sketcher.core`)
   Foundational utilities, exceptions, and interfaces.

   - Status: ⚠️ Partially functional
   - Test Coverage: 11%
   - Issues: 69 security vulnerabilities

**Parser** (`proof_sketcher.parser`)
   Lean 4 file parsing and theorem extraction.

   - Status: ⚠️ Limited functionality
   - Issues: Often produces empty statements
   - Fallback: Basic text parsing when Lean extractor fails

**Generator** (`proof_sketcher.generator`)
   Natural language explanation generation.

   - Status: ⚠️ Offline mode only
   - AI Integration: ❌ Not functional
   - Output: Generic templates only

**Exporter** (`proof_sketcher.exporter`)
   Multi-format output generation.

   - Status: ✅ Basic functionality works
   - Formats: HTML, Markdown, Jupyter
   - Quality: Template-based output

**Animator** (`proof_sketcher.animator`)
   Mathematical animation generation.

   - Status: ❌ Not functional
   - Issues: Manim integration broken
   - Fallback: None available

Installation for Development
-----------------------------

.. code-block:: bash

   git clone https://github.com/yourusername/proof-sketcher
   cd proof-sketcher
   pip install -e ".[dev]"

Basic Usage Example
-------------------

.. code-block:: python

   # ⚠️ This example shows the intended API, but many features don't work yet

   from proof_sketcher.parser import LeanParser
   from proof_sketcher.generator import OfflineGenerator  # Only working generator
   from proof_sketcher.exporter import HTMLExporter

   # Parse Lean file (may produce empty results)
   parser = LeanParser()
   result = parser.parse_file("theorem.lean")

   if result.success and result.theorems:
       # Generate explanations (offline mode only)
       generator = OfflineGenerator()
       sketch = generator.generate_proof_sketch(result.theorems[0])

       # Export to HTML (this part works)
       exporter = HTMLExporter()
       export_result = exporter.export_single(sketch)

       if export_result.success:
           print(f"Generated: {export_result.output_files}")
   else:
       print("⚠️ Parsing failed - common issue in current version")

Contributing
------------

We welcome contributions! Priority areas:

1. **Security Fixes** - Address 69 vulnerabilities
2. **Core Parsing** - Fix empty theorem statement issue
3. **Test Coverage** - Expand from 11% to 70%+
4. **Code Quality** - Fix 3,625 linting violations

See :doc:`contributing` for guidelines.

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
