# Proof Sketcher API Documentation

This document provides a comprehensive overview of the Proof Sketcher API.

## Table of Contents

- [Core Modules](#core-modules)
- [Parser Module](#parser-module)
- [Generator Module](#generator-module)
- [Animator Module](#animator-module)
- [Configuration](#configuration)
- [CLI Reference](#cli-reference)

## Core Modules

### proof_sketcher

The main package providing high-level access to all functionality.

```python
from proof_sketcher import LeanParser, ClaudeGenerator, AnimationGenerator
```

## Parser Module

### LeanParser

Main class for parsing Lean 4 files and extracting theorem information.

```python
from proof_sketcher.parser import LeanParser, ParserConfig

# Create parser with configuration
config = ParserConfig(
    lean_executable="lean",
    lake_enabled=True,
    lean_timeout=30
)
parser = LeanParser(config)

# Parse a Lean file
result = parser.parse_file("example.lean")
for theorem in result.theorems:
    print(f"{theorem.name}: {theorem.statement}")
```

#### Methods

- `parse_file(file_path: Path) -> ParseResult`: Parse a single Lean file
- `parse_theorem(file_path: Path, theorem_name: str) -> Optional[TheoremInfo]`: Parse specific theorem
- `check_lean_available() -> bool`: Check if Lean executable is available

### TheoremInfo

Data model representing a Lean theorem.

```python
@dataclass
class TheoremInfo:
    name: str                     # Theorem name
    statement: str                # Theorem statement/type
    proof: Optional[str]          # Proof body
    dependencies: List[str]       # Import dependencies
    docstring: Optional[str]      # Documentation string
    source_location: Optional[str] # File location
```

### ParseResult

Container for parse results including theorems and errors.

```python
@dataclass
class ParseResult:
    theorems: List[TheoremInfo]
    errors: List[ParseError]
    metadata: Optional[FileMetadata]
    success: bool
    parse_time: float
```

## Generator Module

### ClaudeGenerator

Generates natural language explanations using Claude AI.

```python
from proof_sketcher.generator import ClaudeGenerator, GenerationConfig

# Create generator
config = GenerationConfig(
    model="claude-3-sonnet",
    temperature=0.7,
    max_tokens=2000
)
generator = ClaudeGenerator(config)

# Generate explanation
sketch = generator.generate_proof_sketch(
    theorem,
    mathematical_context="This uses basic number theory"
)
```

#### Methods

- `generate_proof_sketch(theorem, config, context) -> ProofSketch`: Generate full explanation
- `generate_concise_explanation(theorem) -> str`: Generate brief explanation
- `generate_tutorial(theorem, level) -> Tutorial`: Generate educational content
- `stream_generation(theorem) -> Iterator[str]`: Stream response tokens

### ProofSketch

Structured proof explanation with steps and insights.

```python
@dataclass
class ProofSketch:
    theorem_name: str
    theorem_statement: str
    explanation: str              # Natural language overview
    steps: List[ProofStep]        # Step-by-step breakdown
    key_insights: List[str]       # Important concepts
    visualization_hints: List[str] # Animation suggestions
```

### ProofStep

Individual step in a proof explanation.

```python
@dataclass
class ProofStep:
    description: str              # Natural language description
    mathematical_content: str     # LaTeX formulas
    reasoning: Optional[str]      # Why this step works
    prerequisites: List[str]      # Required knowledge
```

## Animator Module

### ManimAnimator

Creates mathematical animations using Manim.

```python
from proof_sketcher.animator import ManimAnimator, AnimationConfig

# Configure animation
config = AnimationConfig(
    quality="1080p",
    fps=60,
    style="modern",
    background_color="#0F0F0F"
)

# Create animator
animator = ManimAnimator(config)

# Generate animation
animation = await animator.create_animation(proof_sketch)
animation.save("output.mp4")
```

#### Methods

- `create_animation(sketch) -> AnimationResponse`: Create full animation
- `render_scene(scene_data) -> Path`: Render specific scene
- `preview_animation(sketch) -> Path`: Generate quick preview

### AnimationRequest

Request model for animation generation.

```python
@dataclass
class AnimationRequest:
    theorem_name: str
    theorem_statement: str
    explanation: str
    proof_steps: List[str]
    mathematical_content: List[str]
    duration: int = 60           # Target duration in seconds
    config: Optional[AnimationConfig] = None
```

### ManimMCPClient

Client for communicating with Manim MCP server.

```python
from proof_sketcher.animator import ManimMCPClient, ManimConfig

# Configure MCP server
config = ManimConfig(
    server_command="npx",
    server_args=["-y", "@moonshiner/manim_mcp@latest"],
    server_timeout=300
)

# Create client
client = ManimMCPClient(config)
await client.start_server()

# Render animation
response = await client.render_animation(request)
```

## Configuration

### ProofSketcherConfig

Main configuration class supporting multiple sources.

```python
from config import ProofSketcherConfig

# Load configuration
config = ProofSketcherConfig.load()  # Auto-detect config files

# Or load from specific file
config = ProofSketcherConfig.load("custom-config.yaml")

# Access settings
print(config.parser.lean_executable)
print(config.generator.model)
print(config.export.output_dir)

# Save configuration
config.save(".proof-sketcher.yaml")
```

### Configuration Sources

Configuration is loaded in priority order:

1. Environment variables (`PROOF_SKETCHER_*`)
2. Specified config file
3. `.proof-sketcher.yaml` in current directory
4. `pyproject.toml` [tool.proof-sketcher] section
5. Default values

### Environment Variables

```bash
# Global settings
export PROOF_SKETCHER_DEBUG=true
export PROOF_SKETCHER_LOG_LEVEL=DEBUG

# Component settings
export PROOF_SKETCHER_PARSER_LEAN_EXECUTABLE=/usr/local/bin/lean
export PROOF_SKETCHER_GENERATOR_MODEL=claude-3-opus
export PROOF_SKETCHER_ANIMATOR_QUALITY=1080p
```

## CLI Reference

### Basic Commands

```bash
# Process a Lean file
proof-sketcher prove example.lean --animate --format html

# Show configuration
proof-sketcher config show

# Save configuration
proof-sketcher config save -o my-config.yaml

# Cache management
proof-sketcher cache status
proof-sketcher cache clear
```

### Command Options

#### prove

Process a Lean file and generate explanations.

```bash
proof-sketcher prove [OPTIONS] LEAN_FILE

Options:
  -o, --output PATH     Output directory
  -f, --format FORMAT   Output format (html|markdown|pdf|jupyter|all)
  --animate            Generate animations
  --theorem NAME       Process specific theorem only
  --verbose           Enable verbose logging
```

#### config

Manage configuration settings.

```bash
proof-sketcher config COMMAND

Commands:
  show    Display current configuration
  save    Save configuration to file

Options:
  -o, --output PATH    Output file for save command
```

#### cache

Manage cached data.

```bash
proof-sketcher cache COMMAND

Commands:
  status    Show cache statistics
  clear     Clear all cached data
  list      List cached items

Options:
  --pattern PATTERN    Filter pattern for list command
```

## Error Handling

All modules use specific exception types for different error conditions:

```python
# Parser errors
from proof_sketcher.parser import LeanParserError, LeanExecutableError

# Generator errors
from proof_sketcher.generator import ClaudeError, ClaudeAPIError

# Animator errors
from proof_sketcher.animator import AnimationError, ManimServerError

# Handle errors appropriately
try:
    result = parser.parse_file("example.lean")
except LeanExecutableError:
    print("Lean is not installed")
except LeanParserError as e:
    print(f"Parse error: {e}")
```

## Best Practices

1. **Configuration Management**
   - Use configuration files for reproducible setups
   - Override specific settings with environment variables
   - Store project-specific configs in version control

2. **Error Handling**
   - Always handle specific exceptions
   - Check operation success before proceeding
   - Use logging for debugging

3. **Performance**
   - Enable caching for repeated operations
   - Use streaming for large responses
   - Batch process multiple theorems

4. **Resource Management**
   - Close MCP server connections properly
   - Clean up temporary files
   - Monitor cache size

## Examples

See the `examples/` directory for complete working examples:

- `basic_usage.py`: Simple theorem processing
- `batch_processing.py`: Process multiple files
- `custom_animation.py`: Advanced animation customization
- `web_integration.py`: Integration with web frameworks
