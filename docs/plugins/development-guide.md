# Plugin Development Guide

## 🔌 Overview

Proof Sketcher's plugin architecture allows developers to extend functionality with custom parsers, generators, exporters, and animators. This guide covers creating, testing, and distributing plugins.

## 🏗️ Plugin Architecture

### Plugin Types

1. **Parser Plugins**: Support new languages or Lean constructs
2. **Generator Plugins**: Custom explanation generation methods
3. **Exporter Plugins**: New output formats
4. **Animator Plugins**: Custom visualization styles
5. **Hybrid Plugins**: Combinations of the above

### Plugin Interface

```python
from abc import ABC, abstractmethod
from typing import List, Optional
from proof_sketcher.core.interfaces import (
    ParserExtension, GeneratorExtension, 
    ExporterExtension, AnimatorExtension
)

class ProofSketcherPlugin(ABC):
    """Base class for all Proof Sketcher plugins."""
    
    @property
    @abstractmethod
    def name(self) -> str:
        """Plugin name."""
        pass
    
    @property 
    @abstractmethod
    def version(self) -> str:
        """Plugin version."""
        pass
    
    @property
    def description(self) -> str:
        """Plugin description."""
        return ""
    
    def register_parsers(self) -> List[ParserExtension]:
        """Register custom parser extensions."""
        return []
    
    def register_generators(self) -> List[GeneratorExtension]:
        """Register custom explanation generators."""
        return []
    
    def register_exporters(self) -> List[ExporterExtension]:
        """Register custom export formats."""
        return []
    
    def register_animators(self) -> List[AnimatorExtension]:
        """Register custom animation generators."""
        return []
    
    def initialize(self) -> None:
        """Initialize plugin resources."""
        pass
    
    def cleanup(self) -> None:
        """Cleanup plugin resources."""
        pass
```

## 🔍 Creating Parser Plugins

### Basic Parser Extension

```python
from proof_sketcher.parser.interfaces import ParserExtension
from proof_sketcher.parser.models import TheoremInfo, ParseResult
from pathlib import Path
from typing import List, Optional

class CoqParserExtension(ParserExtension):
    """Parser extension for Coq proof assistant."""
    
    @property
    def name(self) -> str:
        return "coq_parser"
    
    @property
    def supported_extensions(self) -> List[str]:
        return [".v"]
    
    def can_parse(self, file_path: Path) -> bool:
        """Check if this parser can handle the file."""
        return file_path.suffix == ".v"
    
    def parse_file(self, file_path: Path) -> ParseResult:
        """Parse a Coq file and extract theorems."""
        theorems = []
        errors = []
        
        try:
            content = file_path.read_text()
            theorems = self._extract_coq_theorems(content)
        except Exception as e:
            errors.append(f"Failed to parse {file_path}: {e}")
        
        return ParseResult(
            file_path=file_path,
            theorems=theorems,
            errors=errors,
            metadata={"parser": "coq", "language": "Coq"}
        )
    
    def _extract_coq_theorems(self, content: str) -> List[TheoremInfo]:
        """Extract theorem information from Coq content."""
        theorems = []
        
        # Basic regex-based extraction (simplified)
        import re
        theorem_pattern = r'Theorem\s+(\w+).*?:(.*?)(?:Proof|:=)'
        
        for match in re.finditer(theorem_pattern, content, re.DOTALL):
            name = match.group(1)
            statement = match.group(2).strip()
            
            theorems.append(TheoremInfo(
                name=name,
                statement=statement,
                proof=None,  # Would need more sophisticated parsing
                docstring=None,
                dependencies=[],
                line_number=content[:match.start()].count('\n') + 1,
                namespace=None,
                theorem_type="theorem"
            ))
        
        return theorems
```

### Advanced Parser with Dependencies

```python
class AdvancedLeanParser(ParserExtension):
    """Enhanced Lean parser with dependency analysis."""
    
    def __init__(self):
        self.dependency_graph = {}
        self.import_resolver = ImportResolver()
    
    def parse_file(self, file_path: Path) -> ParseResult:
        """Parse with comprehensive dependency tracking."""
        result = super().parse_file(file_path)
        
        # Enhance with dependency information
        for theorem in result.theorems:
            theorem.dependencies = self._resolve_dependencies(theorem)
            theorem.complexity_score = self._calculate_complexity(theorem)
        
        return result
    
    def _resolve_dependencies(self, theorem: TheoremInfo) -> List[str]:
        """Resolve theorem dependencies."""
        # Implementation depends on Lean's dependency system
        pass
    
    def _calculate_complexity(self, theorem: TheoremInfo) -> float:
        """Calculate theorem complexity score."""
        # Custom complexity metrics
        pass
```

## 🤖 Creating Generator Plugins

### Custom AI Generator

```python
from proof_sketcher.generator.interfaces import GeneratorExtension
from proof_sketcher.generator.models import ProofSketch, GenerationConfig

class LocalLLMGenerator(GeneratorExtension):
    """Generator using local LLM instead of Claude."""
    
    def __init__(self, model_path: str):
        self.model_path = model_path
        self.model = None
    
    @property
    def name(self) -> str:
        return "local_llm"
    
    def initialize(self) -> None:
        """Load the local model."""
        import torch
        from transformers import AutoModelForCausalLM, AutoTokenizer
        
        self.tokenizer = AutoTokenizer.from_pretrained(self.model_path)
        self.model = AutoModelForCausalLM.from_pretrained(self.model_path)
    
    def generate_proof_sketch(self, theorem: TheoremInfo, 
                            config: GenerationConfig) -> ProofSketch:
        """Generate explanation using local LLM."""
        prompt = self._create_prompt(theorem, config)
        
        # Generate with local model
        inputs = self.tokenizer(prompt, return_tensors="pt")
        with torch.no_grad():
            outputs = self.model.generate(
                inputs.input_ids,
                max_length=config.max_tokens,
                temperature=config.temperature,
                do_sample=True
            )
        
        response = self.tokenizer.decode(outputs[0], skip_special_tokens=True)
        
        # Parse response into ProofSketch
        return self._parse_response(response, theorem)
    
    def _create_prompt(self, theorem: TheoremInfo, 
                      config: GenerationConfig) -> str:
        """Create prompt for local LLM."""
        return f"""
        Explain the following mathematical theorem:
        
        Theorem: {theorem.name}
        Statement: {theorem.statement}
        
        Provide a clear, detailed explanation including:
        1. Mathematical significance
        2. Intuitive explanation
        3. Proof strategy
        4. Key steps
        """
    
    def _parse_response(self, response: str, 
                       theorem: TheoremInfo) -> ProofSketch:
        """Parse LLM response into structured ProofSketch."""
        # Implementation depends on response format
        pass
```

### Specialized Domain Generator

```python
class GroupTheoryGenerator(GeneratorExtension):
    """Specialized generator for group theory theorems."""
    
    @property
    def name(self) -> str:
        return "group_theory"
    
    def supports_theorem(self, theorem: TheoremInfo) -> bool:
        """Check if this generator handles the theorem."""
        # Check for group theory keywords
        group_keywords = ['Group', 'Subgroup', 'Homomorphism', 'Isomorphism']
        return any(keyword in theorem.statement for keyword in group_keywords)
    
    def generate_proof_sketch(self, theorem: TheoremInfo,
                            config: GenerationConfig) -> ProofSketch:
        """Generate group theory focused explanation."""
        # Use domain-specific templates and knowledge
        template = self._get_group_theory_template(theorem)
        context = self._build_group_theory_context(theorem)
        
        return template.render(theorem=theorem, context=context)
    
    def _get_group_theory_template(self, theorem: TheoremInfo):
        """Get specialized template for group theory."""
        if 'unique' in theorem.name.lower():
            return self.uniqueness_template
        elif 'homomorphism' in theorem.statement.lower():
            return self.homomorphism_template
        else:
            return self.general_group_template
    
    def _build_group_theory_context(self, theorem: TheoremInfo):
        """Build rich context for group theory explanations."""
        return {
            'related_theorems': self._find_related_theorems(theorem),
            'group_properties': self._extract_group_properties(theorem),
            'historical_context': self._get_historical_context(theorem)
        }
```

## 📤 Creating Exporter Plugins

### Custom Format Exporter

```python
from proof_sketcher.exporter.interfaces import ExporterExtension
from proof_sketcher.exporter.models import ExportContext, ExportResult

class ObsidianExporter(ExporterExtension):
    """Export theorems in Obsidian-compatible markdown."""
    
    @property
    def name(self) -> str:
        return "obsidian"
    
    @property
    def format_name(self) -> str:
        return "Obsidian Markdown"
    
    @property
    def file_extension(self) -> str:
        return ".md"
    
    def export_sketch(self, sketch: ProofSketch, 
                     context: ExportContext) -> ExportResult:
        """Export sketch in Obsidian format."""
        try:
            content = self._render_obsidian_markdown(sketch, context)
            output_file = context.output_dir / f"{sketch.theorem_name}.md"
            
            output_file.parent.mkdir(parents=True, exist_ok=True)
            output_file.write_text(content)
            
            return ExportResult(
                success=True,
                output_files=[output_file],
                errors=[]
            )
        except Exception as e:
            return ExportResult(
                success=False,
                output_files=[],
                errors=[str(e)]
            )
    
    def _render_obsidian_markdown(self, sketch: ProofSketch,
                                context: ExportContext) -> str:
        """Render in Obsidian-specific markdown format."""
        content = f"""# {sketch.theorem_name}

## Tags
#mathematics #theorem #formal-proof

## Statement
{sketch.theorem_statement}

## Intuitive Explanation
{sketch.intuitive_explanation}

## Mathematical Significance
{sketch.mathematical_significance}

## Proof Strategy
- **Approach**: {sketch.proof_strategy.approach}
- **Key Insight**: {sketch.proof_strategy.key_insight}

## Proof Steps
"""
        
        for i, step in enumerate(sketch.key_steps, 1):
            content += f"""
### Step {i}: {step.goal}
**Method**: {step.method}
**Details**: {step.mathematical_content}
**Intuition**: {step.intuition}

"""
        
        # Add backlinks and connections
        content += self._add_obsidian_connections(sketch)
        
        return content
    
    def _add_obsidian_connections(self, sketch: ProofSketch) -> str:
        """Add Obsidian-style connections and backlinks."""
        connections = "\n## Related Concepts\n"
        
        # Extract mathematical concepts for linking
        concepts = sketch.pedagogical_notes.mathematical_areas
        for concept in concepts:
            connections += f"- [[{concept}]]\n"
        
        return connections
```

### Interactive Web Exporter

```python
class InteractiveWebExporter(ExporterExtension):
    """Export with interactive features."""
    
    def __init__(self):
        self.template_env = self._setup_jinja_environment()
    
    def export_sketch(self, sketch: ProofSketch,
                     context: ExportContext) -> ExportResult:
        """Export interactive web page."""
        # Generate main HTML
        html_content = self._render_interactive_html(sketch, context)
        
        # Generate supporting files
        js_content = self._generate_javascript(sketch)
        css_content = self._generate_styles(context)
        
        # Write files
        base_name = sketch.theorem_name
        html_file = context.output_dir / f"{base_name}.html"
        js_file = context.output_dir / f"{base_name}.js"
        css_file = context.output_dir / f"{base_name}.css"
        
        html_file.write_text(html_content)
        js_file.write_text(js_content)
        css_file.write_text(css_content)
        
        return ExportResult(
            success=True,
            output_files=[html_file, js_file, css_file],
            errors=[]
        )
    
    def _generate_javascript(self, sketch: ProofSketch) -> str:
        """Generate interactive JavaScript."""
        return f"""
        class ProofExplorer {{
            constructor() {{
                this.currentStep = 0;
                this.totalSteps = {len(sketch.key_steps)};
                this.setupEventListeners();
            }}
            
            setupEventListeners() {{
                document.getElementById('nextStep').addEventListener('click', 
                    () => this.nextStep());
                document.getElementById('prevStep').addEventListener('click', 
                    () => this.prevStep());
            }}
            
            nextStep() {{
                if (this.currentStep < this.totalSteps - 1) {{
                    this.currentStep++;
                    this.updateDisplay();
                }}
            }}
            
            prevStep() {{
                if (this.currentStep > 0) {{
                    this.currentStep--;
                    this.updateDisplay();
                }}
            }}
            
            updateDisplay() {{
                // Update proof step display
                const steps = document.querySelectorAll('.proof-step');
                steps.forEach((step, index) => {{
                    step.style.display = index <= this.currentStep ? 'block' : 'none';
                }});
            }}
        }}
        
        document.addEventListener('DOMContentLoaded', () => {{
            new ProofExplorer();
        }});
        """
```

## 🎬 Creating Animator Plugins

### Custom Animation Style

```python
from proof_sketcher.animator.interfaces import AnimatorExtension
from proof_sketcher.animator.models import AnimationRequest, AnimationResponse

class MinimalAnimator(AnimatorExtension):
    """Minimalist animation style."""
    
    @property
    def name(self) -> str:
        return "minimal"
    
    @property
    def style_name(self) -> str:
        return "Minimal"
    
    async def render_animation(self, request: AnimationRequest) -> AnimationResponse:
        """Render minimalist animation."""
        try:
            # Create minimal scene with clean aesthetics
            scene_config = {
                'background_color': '#ffffff',
                'text_color': '#333333',
                'accent_color': '#007acc',
                'font_family': 'Computer Modern',
                'animation_style': 'fade'
            }
            
            # Generate animation with custom style
            output_path = await self._render_minimal_scene(request, scene_config)
            
            return AnimationResponse(
                success=True,
                video_path=output_path,
                error_message=None,
                duration=self._calculate_duration(request),
                file_size=output_path.stat().st_size
            )
        except Exception as e:
            return AnimationResponse(
                success=False,
                video_path=None,
                error_message=str(e),
                duration=0,
                file_size=0
            )
    
    async def _render_minimal_scene(self, request: AnimationRequest,
                                  config: dict) -> Path:
        """Render scene with minimal aesthetic."""
        # Implementation using Manim or other animation library
        pass
```

## 📦 Plugin Packaging

### Plugin Structure

```
my_plugin/
├── __init__.py
├── plugin.py          # Main plugin class
├── parsers/           # Parser extensions
│   ├── __init__.py
│   └── coq_parser.py
├── generators/        # Generator extensions
│   ├── __init__.py
│   └── local_llm.py
├── exporters/         # Exporter extensions
│   ├── __init__.py
│   └── obsidian.py
├── templates/         # Template files
│   ├── obsidian.md.j2
│   └── minimal.html.j2
├── tests/            # Plugin tests
│   ├── __init__.py
│   ├── test_parsers.py
│   ├── test_generators.py
│   └── test_exporters.py
├── setup.py          # Package setup
├── requirements.txt  # Dependencies
└── README.md        # Plugin documentation
```

### Main Plugin Class

```python
# my_plugin/plugin.py
from proof_sketcher.plugins import ProofSketcherPlugin
from .parsers.coq_parser import CoqParserExtension
from .generators.local_llm import LocalLLMGenerator
from .exporters.obsidian import ObsidianExporter

class MyPlugin(ProofSketcherPlugin):
    """My custom Proof Sketcher plugin."""
    
    @property
    def name(self) -> str:
        return "my_plugin"
    
    @property
    def version(self) -> str:
        return "1.0.0"
    
    @property
    def description(self) -> str:
        return "Custom extensions for Proof Sketcher"
    
    def register_parsers(self):
        return [CoqParserExtension()]
    
    def register_generators(self):
        return [LocalLLMGenerator("/path/to/model")]
    
    def register_exporters(self):
        return [ObsidianExporter()]
```

### Setup Configuration

```python
# setup.py
from setuptools import setup, find_packages

setup(
    name="proof-sketcher-my-plugin",
    version="1.0.0",
    description="Custom extensions for Proof Sketcher",
    author="Your Name",
    author_email="your.email@example.com",
    packages=find_packages(),
    install_requires=[
        "proof-sketcher>=0.1.0",
        "transformers>=4.21.0",  # for LocalLLMGenerator
        "torch>=1.12.0",         # for LocalLLMGenerator
    ],
    entry_points={
        "proof_sketcher.plugins": [
            "my_plugin = my_plugin.plugin:MyPlugin",
        ],
    },
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    python_requires=">=3.9",
)
```

## 🧪 Testing Plugins

### Unit Tests

```python
# tests/test_parsers.py
import pytest
from pathlib import Path
from my_plugin.parsers.coq_parser import CoqParserExtension

class TestCoqParser:
    def test_can_parse_coq_file(self):
        parser = CoqParserExtension()
        assert parser.can_parse(Path("theorem.v"))
        assert not parser.can_parse(Path("theorem.lean"))
    
    def test_parse_simple_theorem(self, tmp_path):
        parser = CoqParserExtension()
        
        # Create test file
        coq_file = tmp_path / "test.v"
        coq_file.write_text("""
        Theorem add_comm : forall n m : nat, n + m = m + n.
        Proof.
          intros n m.
          induction n.
          - simpl. rewrite <- plus_n_O. reflexivity.
          - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
        Qed.
        """)
        
        result = parser.parse_file(coq_file)
        
        assert len(result.theorems) == 1
        assert result.theorems[0].name == "add_comm"
        assert "forall n m : nat" in result.theorems[0].statement
```

### Integration Tests

```python
# tests/test_integration.py
import pytest
from proof_sketcher.core import ProofSketcherConfig
from proof_sketcher.plugins import load_plugin
from my_plugin.plugin import MyPlugin

class TestPluginIntegration:
    def test_plugin_registration(self):
        plugin = MyPlugin()
        
        parsers = plugin.register_parsers()
        generators = plugin.register_generators()
        exporters = plugin.register_exporters()
        
        assert len(parsers) > 0
        assert len(generators) > 0
        assert len(exporters) > 0
    
    def test_end_to_end_processing(self, tmp_path):
        # Test complete pipeline with plugin
        plugin = MyPlugin()
        
        # Create test Coq file
        coq_file = tmp_path / "test.v"
        coq_file.write_text("Theorem simple : True. Proof. exact I. Qed.")
        
        # Process with plugin
        config = ProofSketcherConfig()
        # ... implementation
```

## 🚀 Plugin Distribution

### Publishing to PyPI

```bash
# Build package
python setup.py sdist bdist_wheel

# Check package
twine check dist/*

# Upload to PyPI
twine upload dist/*
```

### Plugin Registry

Create a plugin entry in the community registry:

```yaml
# plugin-registry.yaml
name: my-plugin
version: 1.0.0
description: Custom extensions for Proof Sketcher
author: Your Name
repository: https://github.com/yourusername/proof-sketcher-my-plugin
pypi_package: proof-sketcher-my-plugin
compatibility:
  proof_sketcher: ">=0.1.0"
categories:
  - parsers
  - generators
  - exporters
keywords:
  - coq
  - local-llm
  - obsidian
```

## 📋 Best Practices

### Plugin Development

1. **Follow naming conventions**: Use descriptive, consistent names
2. **Handle errors gracefully**: Provide meaningful error messages
3. **Document thoroughly**: Include docstrings and usage examples
4. **Test comprehensively**: Unit tests, integration tests, edge cases
5. **Version carefully**: Follow semantic versioning

### Performance Considerations

1. **Lazy loading**: Load resources only when needed
2. **Caching**: Cache expensive computations
3. **Resource cleanup**: Implement proper cleanup methods
4. **Memory management**: Monitor memory usage in long-running operations
5. **Async support**: Use async/await for I/O operations

### Security Guidelines

1. **Input validation**: Validate all external inputs
2. **Sandboxing**: Isolate potentially dangerous operations
3. **Dependencies**: Keep dependencies minimal and updated
4. **Permissions**: Request minimal necessary permissions
5. **Code review**: Have security-focused code reviews

## 📚 Examples and Templates

### Starter Template

```bash
# Clone plugin template
git clone https://github.com/proof-sketcher/plugin-template.git my-plugin
cd my-plugin

# Customize template
./scripts/customize.sh

# Install development dependencies
pip install -e ".[dev]"

# Run tests
pytest

# Build and test plugin
python -m build
pip install dist/*.whl
```

### Community Examples

- **proof-sketcher-isabelle**: Isabelle/HOL parser
- **proof-sketcher-agda**: Agda parser and generator
- **proof-sketcher-tikz**: TikZ diagram exporter
- **proof-sketcher-beamer**: Beamer presentation exporter
- **proof-sketcher-anki**: Anki flashcard exporter

---

*This guide provides everything needed to create powerful Proof Sketcher plugins. For additional support, join the [developer community](https://github.com/proof-sketcher/community) and see the [plugin examples repository](https://github.com/proof-sketcher/plugins).*