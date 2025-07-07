# Configuration Guide

Comprehensive guide to configuring Proof Sketcher for your needs.

## Configuration Files

### Configuration Hierarchy

Proof Sketcher looks for configuration in this order (later files override earlier ones):

1. **Default settings** (built-in)
2. **Global config**: `~/.proof-sketcher/config.yaml`
3. **Project config**: `./.proof-sketcher.yaml`
4. **Environment variables**: `PROOF_SKETCHER_*`
5. **Command-line flags**: `--config`, `--debug`, etc.

### File Locations

```bash
# Global configuration
~/.proof-sketcher/
├── config.yaml          # Main configuration
├── cache/               # Generated content cache
└── templates/           # Custom templates

# Project configuration
./
├── .proof-sketcher.yaml # Project-specific settings
├── .proof-sketcher/     # Project data
│   ├── cache/
│   └── exports/
└── lean-packages/       # Lean dependencies
```

## Configuration Format

### YAML Configuration

```yaml
# Basic settings
project_name: "My Lean Project"
version: "1.0.0"
debug: false
log_level: "INFO"

# Directories
cache_dir: "~/.proof-sketcher/cache"
data_dir: "~/.proof-sketcher/data"
export_dir: "./exports"

# Parser configuration
parser:
  lean_executable: "lean"
  lake_executable: "lake"
  lean_timeout: 30
  max_file_size: 10485760  # 10MB
  encoding: "utf-8"

# Generator configuration
generator:
  model: "claude-3-opus-20240229"
  temperature: 0.7
  max_tokens: 4096
  timeout: 60
  cache_responses: true
  offline_fallback: true

# Animation configuration
animator:
  animation_config:
    quality: "medium"
    style: "academic"
    duration_per_step: 2.0
    transition_time: 0.5
    background_color: "#ffffff"
    text_color: "#000000"
    accent_color: "#0066cc"
    width: 1920
    height: 1080

# Export configuration
export:
  default_format: "html"
  include_source: true
  include_animations: true
  template_theme: "default"
  math_renderer: "katex"
  syntax_highlighting: true

# MCP server configuration
manim:
  host: "localhost"
  port: 8000
  timeout: 300
  max_retries: 3
  temp_dir: "/tmp/manim"
```

### Environment Variables

```bash
# Global settings
export PROOF_SKETCHER_DEBUG=true
export PROOF_SKETCHER_LOG_LEVEL=DEBUG
export PROOF_SKETCHER_CACHE_DIR=/custom/cache

# Parser settings
export PROOF_SKETCHER_PARSER_LEAN_TIMEOUT=60
export PROOF_SKETCHER_PARSER_LEAN_EXECUTABLE=/custom/lean

# Generator settings
export PROOF_SKETCHER_GENERATOR_MODEL=claude-3-haiku-20240307
export PROOF_SKETCHER_GENERATOR_TEMPERATURE=0.5

# Animation settings
export PROOF_SKETCHER_ANIMATOR_QUALITY=high
export PROOF_SKETCHER_ANIMATOR_STYLE=modern
```

## Configuration Sections

### Parser Configuration

Controls how Lean files are parsed and processed.

```yaml
parser:
  # Lean executable path
  lean_executable: "lean"
  lake_executable: "lake"
  
  # Timeouts and limits
  lean_timeout: 30           # Seconds
  max_file_size: 10485760   # Bytes (10MB)
  max_theorems_per_file: 100
  
  # Processing options
  encoding: "utf-8"
  ignore_errors: false
  extract_docstrings: true
  parse_tactics: true
  
  # File patterns
  include_patterns:
    - "*.lean"
    - "**/*.lean"
  exclude_patterns:
    - "build/**"
    - ".lake/**"
    - "**/test/**"
```

### Generator Configuration

Controls natural language generation.

```yaml
generator:
  # Model selection
  model: "claude-3-opus-20240229"
  
  # Generation parameters
  temperature: 0.7
  max_tokens: 4096
  top_p: 0.9
  frequency_penalty: 0.0
  
  # Timeouts and retries
  timeout: 60
  max_retries: 3
  retry_delay: 1.0
  
  # Caching
  cache_responses: true
  cache_ttl: 86400  # 24 hours
  
  # Fallback options
  offline_fallback: true
  template_fallback: true
  
  # Content options
  difficulty_levels:
    - "beginner"
    - "intermediate" 
    - "advanced"
  mathematical_areas:
    - "algebra"
    - "analysis"
    - "topology"
    - "logic"
```

### Animation Configuration

Controls mathematical animations.

```yaml
animator:
  animation_config:
    # Quality settings
    quality: "medium"         # low, medium, high, ultra
    fps: 30
    
    # Visual style
    style: "academic"         # academic, modern, minimal
    background_color: "#ffffff"
    text_color: "#000000"
    accent_color: "#0066cc"
    
    # Dimensions
    width: 1920
    height: 1080
    
    # Timing
    duration_per_step: 2.0
    transition_time: 0.5
    pause_time: 1.0
    
    # Features
    show_step_numbers: true
    highlight_changes: true
    include_narration: false
    chapter_markers: true
    
    # Limits
    max_memory_mb: 2048
    max_processing_time: 300
```

### Export Configuration

Controls output format and styling.

```yaml
export:
  # Default settings
  default_format: "html"
  output_dir: "./exports"
  
  # Content inclusion
  include_source: true
  include_animations: true
  include_metadata: true
  include_toc: true
  
  # Styling
  template_theme: "default"   # default, mathlib, modern, minimal
  math_renderer: "katex"      # katex, mathjax, plain
  syntax_highlighting: true
  
  # HTML-specific
  html:
    responsive: true
    dark_mode: true
    print_friendly: true
    embed_assets: false
    
  # Markdown-specific  
  markdown:
    flavor: "github"          # github, commonmark, pandoc
    include_yaml_header: true
    relative_links: true
    
  # PDF-specific
  pdf:
    paper_size: "A4"
    margins: "2cm"
    font_family: "Computer Modern"
```

## Advanced Configuration

### Custom Templates

Create custom export templates:

```yaml
export:
  template_paths:
    - "~/.proof-sketcher/templates"
    - "./templates"
  
  custom_templates:
    academic_paper:
      base: "html"
      template: "academic.html.j2"
      styles: ["academic.css"]
    
    blog_post:
      base: "markdown"
      template: "blog.md.j2"
      frontmatter: true
```

### Integrations

#### IDE Integration

```yaml
integrations:
  vscode:
    enabled: true
    auto_export: true
    preview_mode: "side"
    
  emacs:
    enabled: false
    lean_mode_integration: true
    
  vim:
    enabled: false
    syntax_highlighting: true
```

#### CI/CD Integration

```yaml
ci_cd:
  github_actions:
    auto_export: true
    upload_artifacts: true
    
  gitlab_ci:
    enabled: false
    pages_deploy: true
```

### Performance Tuning

```yaml
performance:
  # Concurrency
  max_concurrent_files: 4
  max_concurrent_theorems: 8
  
  # Memory management
  memory_limit_mb: 4096
  cache_size_mb: 512
  gc_frequency: 100
  
  # Timeouts
  global_timeout: 3600      # 1 hour
  per_file_timeout: 300     # 5 minutes
  per_theorem_timeout: 60   # 1 minute
```

## Configuration Validation

### Validate Configuration

```bash
# Check current configuration
proof-sketcher config validate

# Validate specific file
proof-sketcher config validate --file config.yaml

# Show effective configuration
proof-sketcher config show --resolved
```

### Configuration Schema

The configuration follows a JSON schema for validation:

```yaml
# Schema validation
schema_version: "1.0"
required_fields:
  - project_name
  - parser.lean_executable
  
field_types:
  debug: boolean
  parser.lean_timeout: integer
  generator.temperature: number
  
constraints:
  generator.temperature:
    min: 0.0
    max: 2.0
  parser.lean_timeout:
    min: 1
    max: 3600
```

## Configuration Examples

### Academic Research

```yaml
project_name: "Category Theory Research"
generator:
  model: "claude-3-opus-20240229"
  temperature: 0.3  # More precise
  
export:
  template_theme: "academic"
  include_source: true
  
animator:
  animation_config:
    style: "academic"
    quality: "high"
```

### Teaching Materials

```yaml
project_name: "Linear Algebra Course"
generator:
  model: "claude-3-sonnet-20240229"
  temperature: 0.8  # More creative
  
export:
  template_theme: "educational"
  include_animations: true
  
animator:
  animation_config:
    style: "friendly"
    show_step_numbers: true
    include_narration: true
```

### Production Documentation

```yaml
project_name: "Mathlib Documentation"
parser:
  lean_timeout: 120
  max_theorems_per_file: 1000
  
generator:
  cache_responses: true
  offline_fallback: true
  
export:
  default_format: "html"
  template_theme: "mathlib"
  
performance:
  max_concurrent_files: 8
  memory_limit_mb: 8192
```

## Troubleshooting Configuration

### Common Issues

1. **Configuration not loading**
   ```bash
   # Check file permissions
   ls -la ~/.proof-sketcher/config.yaml
   
   # Validate YAML syntax
   proof-sketcher config validate
   ```

2. **Environment variables not working**
   ```bash
   # Check environment
   env | grep PROOF_SKETCHER
   
   # Test override
   PROOF_SKETCHER_DEBUG=true proof-sketcher config show
   ```

3. **Template not found**
   ```bash
   # List available templates
   proof-sketcher templates list
   
   # Check template paths
   proof-sketcher config show | grep template_paths
   ```

For more troubleshooting, see the [Troubleshooting Guide](troubleshooting.md).