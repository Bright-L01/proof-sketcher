Proof Sketcher API Documentation
=================================

Transform Lean 4 theorems into natural language explanations with synchronized mathematical animations.

.. image:: https://img.shields.io/badge/python-3.9+-blue.svg
   :target: https://www.python.org/downloads/
   :alt: Python 3.9+

.. image:: https://img.shields.io/badge/License-MIT-yellow.svg
   :target: https://opensource.org/licenses/MIT
   :alt: MIT License

.. image:: https://img.shields.io/badge/code%20style-black-000000.svg
   :target: https://github.com/psf/black
   :alt: Code style: black

Overview
--------

Proof Sketcher bridges the gap between formal mathematical proofs and human understanding by:

* **Natural Language Generation**: Converts Lean 4 proofs into clear, accessible explanations
* **Mathematical Animations**: Creates synchronized Manim visualizations of proof steps  
* **Multi-Format Export**: Produces HTML, Markdown, PDF, and Jupyter notebooks
* **Seamless Integration**: Works with mathlib4, doc-gen4, and existing Lean projects
* **Claude Code Integration**: Uses Claude Code CLI for free AI-powered explanations
* **Smart Caching**: Optimizes performance with intelligent caching

Quick Start
-----------

Installation
~~~~~~~~~~~~

.. code-block:: bash

   # Clone and install
   git clone https://github.com/Bright-L01/proof-sketcher.git
   cd proof-sketcher
   pip install -e .

   # Install Claude CLI (required)
   curl -fsSL https://claude.ai/install.sh | sh

Basic Usage
~~~~~~~~~~~

.. code-block:: bash

   # List theorems in a file
   python -m proof_sketcher list-theorems examples/group_theory.lean

   # Generate explanations
   python -m proof_sketcher prove file.lean --format markdown

   # Generate with animations
   python -m proof_sketcher prove file.lean --animate --format html

Python API
~~~~~~~~~~

.. code-block:: python

   from proof_sketcher import LeanParser, AIGenerator, ProofSketcherConfig

   # Configure the system
   config = ProofSketcherConfig.load("config.yaml")

   # Parse Lean file
   parser = LeanParser(config.parser)
   result = parser.parse_file("theorems.lean")

   # Generate explanations
   generator = AIGenerator(config.generator)
   for theorem in result.theorems:
       response = generator.generate_proof_sketch(theorem)
       print(f"✓ {theorem.name}: {response.content.introduction}")

API Reference
=============

Core Modules
------------

Parser Module
~~~~~~~~~~~~~

.. automodule:: proof_sketcher.parser
   :members:
   :undoc-members:
   :show-inheritance:

.. autoclass:: proof_sketcher.parser.LeanParser
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: proof_sketcher.parser.models
   :members:
   :undoc-members:
   :show-inheritance:

Generator Module
~~~~~~~~~~~~~~~~

.. automodule:: proof_sketcher.generator
   :members:
   :undoc-members:
   :show-inheritance:

.. autoclass:: proof_sketcher.generator.AIGenerator
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: proof_sketcher.generator.models
   :members:
   :undoc-members:
   :show-inheritance:

Animator Module
~~~~~~~~~~~~~~~

.. automodule:: proof_sketcher.animator
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: proof_sketcher.animator.models
   :members:
   :undoc-members:
   :show-inheritance:

Exporter Module
~~~~~~~~~~~~~~~

.. automodule:: proof_sketcher.exporter
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: proof_sketcher.exporter.models
   :members:
   :undoc-members:
   :show-inheritance:

Configuration Module
~~~~~~~~~~~~~~~~~~~~

.. automodule:: proof_sketcher.config
   :members:
   :undoc-members:
   :show-inheritance:

.. autoclass:: proof_sketcher.config.ProofSketcherConfig
   :members:
   :undoc-members:
   :show-inheritance:

Core Utilities
~~~~~~~~~~~~~~

.. automodule:: proof_sketcher.core
   :members:
   :undoc-members:
   :show-inheritance:

Classical Mathematics Examples
==============================

Group Theory
-------------

Proof Sketcher excels at explaining group theory concepts:

* **Identity Uniqueness**: Proof that every group has exactly one identity element
* **Inverse Properties**: Demonstration of unique inverses for group elements
* **Cancellation Laws**: Left and right cancellation in groups
* **Subgroup Criteria**: Conditions for subset to form a subgroup

Real Analysis  
-------------

Mathematical analysis theorems are clearly explained:

* **Supremum Property**: Completeness of real numbers
* **Squeeze Theorem**: Fundamental limit theorem with visual proof
* **Intermediate Value Theorem**: Continuity properties with graphical intuition
* **Bolzano-Weierstrass**: Compactness in metric spaces

Point Set Topology
-------------------

Topological concepts made accessible:

* **Open Sets**: Definition and properties of topological spaces
* **Hausdorff Separation**: T2 separation axioms with examples
* **Compactness**: Finite subcover property and preservation theorems
* **Connectedness**: Path-connected vs connected spaces

Configuration Guide
===================

YAML Configuration
------------------

Create ``.proof-sketcher.yaml`` in your project:

.. code-block:: yaml

   # Natural language generation
   generator:
     model: claude-3-5-sonnet-20241022
     temperature: 0.7
     max_tokens: 4000
     verbosity: detailed

   # Animation settings  
   animator:
     quality: high
     fps: 60
     style: modern
     background_color: "#1a1a1a"

   # Export options
   export:
     output_dir: docs/
     html_theme: doc-gen4
     pdf_engine: pdflatex

   # Caching
   cache:
     enabled: true
     ttl_hours: 24
     max_size_mb: 500

Environment Variables
---------------------

Override settings with environment variables:

.. code-block:: bash

   export PROOF_SKETCHER_DEBUG=true
   export PROOF_SKETCHER_GENERATOR_MODEL=claude-3-opus
   export PROOF_SKETCHER_CACHE_ENABLED=false

Troubleshooting
===============

Common Issues
-------------

**"No theorems found in file"**
   Check Lean syntax and ensure proper imports:

   .. code-block:: lean

      import Mathlib.Data.Nat.Basic
      import Mathlib.Algebra.Group.Defs

      theorem add_zero (n : ℕ) : n + 0 = n := by simp

**"Claude command failed"**
   Install and configure Claude CLI:

   .. code-block:: bash

      curl -fsSL https://claude.ai/install.sh | sh
      claude --version

**"Animation generation failed"**
   Install Manim MCP server:

   .. code-block:: bash

      npm install -g @manim-mcp/server

Debug Mode
----------

Enable verbose logging for troubleshooting:

.. code-block:: bash

   export PROOF_SKETCHER_DEBUG=true
   python -m proof_sketcher prove file.lean --verbose

See the `Troubleshooting Guide <../TROUBLESHOOTING.md>`_ for comprehensive solutions.

Contributing
============

We welcome contributions! See the `Contributing Guide <../CONTRIBUTING.md>`_ for:

* Development setup instructions
* Code style guidelines
* Testing requirements
* Pull request process

Development Setup
-----------------

.. code-block:: bash

   # Clone and setup development environment
   git clone https://github.com/Bright-L01/proof-sketcher.git
   cd proof-sketcher

   # Install in development mode
   pip install -e ".[dev]"

   # Run tests
   pytest

   # Code formatting
   black src/ tests/
   ruff check src/ tests/

Links and Resources
===================

* **GitHub Repository**: https://github.com/Bright-L01/proof-sketcher
* **User Guide**: `docs/USER_GUIDE.md <../USER_GUIDE.md>`_
* **Quick Start**: `docs/QUICKSTART_GUIDE.md <../QUICKSTART_GUIDE.md>`_
* **Examples**: `examples/ <../examples/>`_
* **Issue Tracker**: https://github.com/Bright-L01/proof-sketcher/issues

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`