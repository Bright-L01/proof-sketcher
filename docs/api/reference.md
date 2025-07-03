# API Reference

## 📖 Overview

Proof Sketcher provides both a command-line interface and a comprehensive Python API for programmatic access. This reference covers all public APIs, configuration options, and extension points.

## 🐍 Python API

### Core Classes

#### LeanParser

Parse Lean 4 files and extract theorem information.

```python
from proof_sketcher.parser import LeanParser
from proof_sketcher.config import ParserConfig

# Create parser with configuration
config = ParserConfig(
    lean_executable="lean",
    lean_timeout=30,
    lake_build_on_parse=True
)
parser = LeanParser(config)

# Parse a file
result = parser.parse_file(Path("theorems.lean"))
print(f"Found {len(result.theorems)} theorems")

# Handle errors
if result.errors:
    for error in result.errors:
        print(f"Error: {error}")
```

**Methods**:

- `parse_file(file_path: Path) -> ParseResult`
  - Parse a Lean file and return structured results
  - **Parameters**: `file_path` - Path to the Lean file
  - **Returns**: `ParseResult` with theorems and errors
  - **Raises**: `ParserError` for invalid files

- `parse_theorem(theorem_text: str) -> Optional[TheoremInfo]`
  - Parse a single theorem from text
  - **Parameters**: `theorem_text` - Lean theorem code
  - **Returns**: `TheoremInfo` or `None` if parsing fails

#### AIGenerator

Generate natural language explanations using Claude AI.

```python
from proof_sketcher.generator import AIGenerator
from proof_sketcher.config import GeneratorConfig

# Configure generator
config = GeneratorConfig(
    model="claude-3-5-sonnet-20241022",
    temperature=0.7,
    max_tokens=4000,
    verbosity="detailed"
)
generator = AIGenerator(config)

# Generate explanation
sketch = generator.generate_proof_sketch(theorem)
print(sketch.intuitive_explanation)

# Generate with custom type
context_sketch = generator.generate_mathematical_context(theorem)
print(context_sketch.historical_context)
```

**Methods**:

- `generate_proof_sketch(theorem: TheoremInfo) -> ProofSketch`
  - Generate comprehensive proof explanation
  - **Parameters**: `theorem` - Parsed theorem information
  - **Returns**: `ProofSketch` with detailed explanation
  - **Raises**: `GeneratorError` for API failures

- `generate_eli5_explanation(theorem: TheoremInfo) -> str`
  - Generate intuitive, beginner-friendly explanation
  - **Returns**: Simple string explanation with analogies

#### OfflineGenerator

Generate explanations without AI using AST analysis.

```python
from proof_sketcher.generator import OfflineGenerator

# Create offline generator
generator = OfflineGenerator(cache_dir=Path(".cache"))

# Generate basic explanation
sketch = generator.generate_proof_sketch(theorem)
print(sketch.introduction)
```

#### HTMLExporter

Export explanations to HTML format.

```python
from proof_sketcher.exporter import HTMLExporter, ExportOptions

# Configure HTML export
options = ExportOptions(
    output_dir=Path("docs/"),
    include_animations=True,
    create_index=True,
    theme="doc-gen4"
)
exporter = HTMLExporter(options)

# Export multiple theorems
context = ExportContext(
    format=ExportFormat.HTML,
    output_dir=Path("output/"),
    sketches=sketches,
    animations=animations,
    project_name="My Theorems"
)
result = exporter.export_multiple(sketches, context)

if result.success:
    print(f"Exported to {result.output_files}")
```

#### BatchProcessor

Process multiple files efficiently with parallel execution.

```python
from proof_sketcher.core import BatchProcessor

# Create batch processor
processor = BatchProcessor(
    max_workers=8,
    memory_limit_mb=2048,
    use_enhanced_parser=True,
    export_formats=[ExportFormat.HTML, ExportFormat.MARKDOWN]
)

# Add files to process
processor.add_directory(
    Path("./theorems/"),
    recursive=True,
    exclude_patterns=["**/test/**"]
)

# Process batch
import asyncio
stats = asyncio.run(processor.process_batch(Path("./output/")))
print(f"Processed {stats.successful_files} files")
```

### Data Models

#### TheoremInfo

Represents a parsed theorem with all relevant information.

```python
@dataclass
class TheoremInfo:
    name: str                    # Theorem name
    statement: str               # Lean statement
    proof: Optional[str]         # Proof text (if available)
    docstring: Optional[str]     # Documentation string
    dependencies: List[str]      # Required imports
    line_number: Optional[int]   # Location in file
    namespace: Optional[str]     # Lean namespace
    
    # Enhanced parser fields
    theorem_type: TheoremType    # theorem, lemma, def, etc.
    visibility: Visibility       # public, private, protected
    attributes: List[str]        # @[simp], @[instance], etc.
```

#### ProofSketch

Comprehensive explanation of a theorem.

```python
@dataclass
class ProofSketch:
    theorem_name: str
    mathematical_significance: str
    intuitive_explanation: str
    proof_strategy: ProofStrategy
    key_steps: List[ProofStep]
    mathematical_reflection: MathematicalReflection
    pedagogical_notes: PedagogicalNotes
    
    def to_markdown(self) -> str:
        """Convert to markdown format."""
        pass
    
    def to_html(self) -> str:
        """Convert to HTML format."""
        pass
```

#### AnimationRequest/Response

Animation generation interface.

```python
@dataclass
class AnimationRequest:
    theorem_name: str
    request_id: str
    segments: List[AnimationSegment]
    config: AnimationConfig
    
@dataclass 
class AnimationResponse:
    success: bool
    video_path: Optional[Path]
    error_message: Optional[str]
    duration: float
    file_size: int
```

### Configuration API

#### ProofSketcherConfig

Main configuration class with hierarchical structure.

```python
# Load from file
config = ProofSketcherConfig.load("config.yaml")

# Create programmatically
config = ProofSketcherConfig(
    parser=ParserConfig(lean_timeout=60),
    generator=GeneratorConfig(temperature=0.8),
    animator=AnimationConfig(quality="high"),
    export=ExportConfig(output_dir="docs/")
)

# Save configuration
config.save("my-config.yaml")

# Environment variable override
config = ProofSketcherConfig.from_env()
```

### Error Handling

#### Exception Hierarchy

```python
# Base exception
class ProofSketcherError(Exception):
    def __init__(self, message: str, details: Dict[str, Any] = None,
                 error_code: str = None):
        self.details = details or {}
        self.error_code = error_code
        super().__init__(message)

# Specific exceptions
class ParserError(ProofSketcherError):
    """Raised when Lean parsing fails."""
    pass

class GeneratorError(ProofSketcherError):
    """Raised when explanation generation fails."""
    pass

class AnimatorError(ProofSketcherError):
    """Raised when animation generation fails."""
    pass

class ExporterError(ProofSketcherError):
    """Raised when export fails."""
    pass
```

#### Error Handling Patterns

```python
try:
    result = parser.parse_file("theorems.lean")
except LeanSyntaxError as e:
    print(f"Syntax error at line {e.details.get('line_number')}: {e}")
    print(f"Suggestion: {e.details.get('suggestion')}")
except LeanTimeoutError as e:
    print(f"Parsing timeout after {e.details.get('timeout')}s")
except ParserError as e:
    print(f"Parser error [{e.error_code}]: {e}")
```

## 🖥️ Command-Line Interface

### Main Commands

#### `prove`

Process Lean files and generate explanations.

```bash
python -m proof_sketcher prove [OPTIONS] LEAN_FILE
```

**Options**:
- `--output, -o PATH`: Output directory
- `--format, -f [html|markdown|pdf|jupyter|all]`: Export format
- `--theorem, -t TEXT`: Process specific theorems (multiple)
- `--animate`: Generate animations
- `--offline`: Use offline mode (no AI)
- `--verbose, -v`: Enable verbose logging
- `--config, -c PATH`: Configuration file

**Examples**:
```bash
# Basic usage
python -m proof_sketcher prove theorems.lean

# Specific theorem with animation
python -m proof_sketcher prove file.lean -t "add_comm" --animate -f html

# Offline batch processing
python -m proof_sketcher prove *.lean --offline -f markdown
```

#### `batch`

Process multiple files with parallel execution.

```bash
python -m proof_sketcher batch [OPTIONS] INPUT_PATH
```

**Options**:
- `--output-dir, -o PATH`: Output directory
- `--workers, -w INTEGER`: Number of parallel workers
- `--memory-limit INTEGER`: Memory limit in MB
- `--formats, -f [html|markdown|all]`: Export formats (multiple)
- `--exclude TEXT`: Exclude patterns (multiple)
- `--enhanced/--basic`: Use enhanced parser
- `--recursive/--no-recursive`: Recursive directory search
- `--report PATH`: Save detailed JSON report

**Examples**:
```bash
# High-performance batch processing
python -m proof_sketcher batch ./project/ \
  --workers 16 \
  --memory-limit 4096 \
  --formats html markdown \
  --output-dir ./docs/

# With exclusions and reporting
python -m proof_sketcher batch ./src/ \
  --exclude "**/test/**" \
  --exclude "**/temp/**" \
  --report batch_report.json
```

#### `list-theorems`

Display theorems found in a Lean file.

```bash
python -m proof_sketcher list-theorems [OPTIONS] LEAN_FILE
```

**Examples**:
```bash
# Basic listing
python -m proof_sketcher list-theorems theorems.lean

# With verbose output
python -m proof_sketcher list-theorems theorems.lean --verbose
```

#### `config`

Manage configuration settings.

```bash
# Show current configuration
python -m proof_sketcher config show

# Save configuration to file
python -m proof_sketcher config save -o my-config.yaml
```

#### `cache`

Manage theorem and animation cache.

```bash
# Show cache status
python -m proof_sketcher cache status

# Clear cache
python -m proof_sketcher cache clear

# List cached items
python -m proof_sketcher cache list [PATTERN]
```

### Global Options

Available for all commands:

- `--verbose, -v`: Enable verbose logging
- `--config, -c PATH`: Specify configuration file
- `--version`: Show version information
- `--help`: Show help message

## 🔧 Configuration Reference

### Configuration File Format

```yaml
# Global settings
project_name: "My Project"
debug: false
log_level: "INFO"
cache_dir: ".cache"

# Parser configuration
parser:
  lean_executable: "lean"
  lean_timeout: 30
  lake_build_on_parse: true
  enhanced_parsing: true

# Generator configuration  
generator:
  model: "claude-3-5-sonnet-20241022"
  temperature: 0.7
  max_tokens: 4000
  verbosity: "detailed"
  include_reasoning: true

# Animation configuration
animator:
  quality: "high"  # low, medium, high, ultra
  fps: 60
  style: "modern"
  background_color: "#1a1a1a"
  timeout: 300

# Export configuration
export:
  output_dir: "output/"
  html_theme: "doc-gen4"
  markdown_flavor: "github"
  pdf_engine: "pdflatex"
  include_source: true

# Cache configuration  
cache:
  enabled: true
  ttl_hours: 24
  max_size_mb: 500
  cleanup_on_startup: false
```

### Environment Variables

Override configuration with environment variables:

```bash
# Global settings
export PROOF_SKETCHER_DEBUG=true
export PROOF_SKETCHER_LOG_LEVEL=DEBUG

# Parser settings
export PROOF_SKETCHER_LEAN_EXECUTABLE=/custom/lean
export PROOF_SKETCHER_LEAN_TIMEOUT=60

# Generator settings
export PROOF_SKETCHER_GENERATOR_MODEL=claude-3-5-sonnet-20241022
export PROOF_SKETCHER_GENERATOR_TEMPERATURE=0.8

# Animation settings
export PROOF_SKETCHER_ANIMATOR_QUALITY=ultra
export PROOF_SKETCHER_ANIMATOR_FPS=30

# Export settings
export PROOF_SKETCHER_EXPORT_OUTPUT_DIR=/custom/output
export PROOF_SKETCHER_EXPORT_HTML_THEME=custom
```

## 🔌 Plugin Development

### Creating Custom Generators

```python
from proof_sketcher.generator import GeneratorBase
from proof_sketcher.models import ProofSketch, TheoremInfo

class CustomGenerator(GeneratorBase):
    """Custom explanation generator."""
    
    def generate_proof_sketch(self, theorem: TheoremInfo) -> ProofSketch:
        # Custom generation logic
        return ProofSketch(
            theorem_name=theorem.name,
            mathematical_significance="Custom analysis...",
            # ... other fields
        )
    
    def supports_theorem(self, theorem: TheoremInfo) -> bool:
        """Check if this generator can handle the theorem."""
        return theorem.theorem_type == TheoremType.LEMMA

# Register plugin
from proof_sketcher.plugins import register_generator
register_generator("custom", CustomGenerator)
```

### Creating Custom Exporters

```python
from proof_sketcher.exporter import ExporterBase
from proof_sketcher.models import ProofSketch, ExportContext, ExportResult

class CustomExporter(ExporterBase):
    """Custom format exporter."""
    
    def export_sketch(self, sketch: ProofSketch, 
                     context: ExportContext) -> ExportResult:
        # Custom export logic
        output_file = context.output_dir / f"{sketch.theorem_name}.custom"
        
        # Generate custom format
        content = self.render_custom_format(sketch)
        output_file.write_text(content)
        
        return ExportResult(
            success=True,
            output_files=[output_file],
            errors=[]
        )
    
    def render_custom_format(self, sketch: ProofSketch) -> str:
        # Custom rendering logic
        return f"# {sketch.theorem_name}\n{sketch.intuitive_explanation}"

# Register plugin
from proof_sketcher.plugins import register_exporter
register_exporter("custom", CustomExporter)
```

## 📊 Performance Tuning

### Batch Processing Optimization

```python
# Optimal settings for different scenarios

# Small projects (< 100 files)
processor = BatchProcessor(max_workers=4, memory_limit_mb=1024)

# Medium projects (100-1000 files)
processor = BatchProcessor(max_workers=8, memory_limit_mb=2048)

# Large projects (1000+ files)
processor = BatchProcessor(max_workers=16, memory_limit_mb=4096)
```

### Caching Strategies

```python
# Aggressive caching for development
config = ProofSketcherConfig(
    cache=CacheConfig(
        enabled=True,
        ttl_hours=168,  # 1 week
        max_size_mb=2048
    )
)

# Conservative caching for production
config = ProofSketcherConfig(
    cache=CacheConfig(
        enabled=True,
        ttl_hours=24,   # 1 day
        max_size_mb=512
    )
)
```

## 🚨 Error Reference

### Common Error Codes

- `PARSER_FAILED`: Lean parsing failed
- `GENERATOR_TIMEOUT`: AI generation timeout
- `ANIMATOR_UNAVAILABLE`: Manim MCP server unavailable
- `EXPORT_FORMAT_UNSUPPORTED`: Unknown export format
- `BATCH_MEMORY_EXCEEDED`: Memory limit exceeded during batch processing
- `CONFIG_INVALID`: Configuration validation failed

### Recovery Strategies

```python
# Robust processing with fallbacks
try:
    # Try normal processing
    sketch = ai_generator.generate_proof_sketch(theorem)
except GeneratorError:
    # Fallback to offline mode
    sketch = offline_generator.generate_proof_sketch(theorem)

try:
    # Try with animations
    result = exporter.export_with_animations(sketch, animations)
except AnimatorError:
    # Fallback without animations
    result = exporter.export_sketch(sketch)
```

---

*This API reference provides comprehensive coverage of all Proof Sketcher functionality. For additional examples and tutorials, see the [examples directory](../../examples/) and [architecture overview](../architecture/overview.md).*