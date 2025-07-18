# CLI Reference

Complete reference for all Proof Sketcher command-line interface commands.

## Global Options

```bash
proof-sketcher [OPTIONS] COMMAND [ARGS]...
```

### Options

- `--version` - Show version and exit
- `-v, --verbose` - Enable verbose logging
- `-c, --config PATH` - Path to configuration file
- `--help` - Show help message and exit

## Commands

### `prove`

Generate natural language explanation for a Lean theorem.

```bash
proof-sketcher prove [OPTIONS] FILE_PATH
```

#### Arguments

- `FILE_PATH` - Path to Lean file containing theorems

#### Options

- `-t, --theorem TEXT` - Specific theorem name to explain
- `-f, --format [html|markdown|all]` - Output format (default: html)
- `-o, --output PATH` - Output file path
- `--show-proof` - Include formal proof in output
- `--show-source` - Include source code in output
- `--style [concise|normal|detailed]` - Explanation style
- `--template PATH` - Custom template file

#### Examples

```bash
# Basic usage
proof-sketcher prove example.lean --theorem add_comm

# Export as markdown
proof-sketcher prove example.lean --theorem add_comm --format markdown

# Detailed explanation with source
proof-sketcher prove example.lean -t add_comm --style detailed --show-source
```

### `list-theorems`

List all theorems and lemmas in a Lean file.

```bash
proof-sketcher list-theorems [OPTIONS] FILE_PATH
```

#### Options

- `--json` - Output as JSON
- `--filter TEXT` - Filter theorem names by pattern
- `--sort [name|line|type]` - Sort order

#### Examples

```bash
# List all theorems
proof-sketcher list-theorems mathlib/algebra/basic.lean

# Filter by pattern
proof-sketcher list-theorems file.lean --filter "add_*"

# JSON output for scripting
proof-sketcher list-theorems file.lean --json
```

### `batch`

Process multiple Lean files in batch.

```bash
proof-sketcher batch [OPTIONS] [FILES]...
```

#### Arguments

- `FILES` - Lean files to process (supports wildcards)

#### Options

- `-o, --output-dir PATH` - Output directory
- `-f, --format [html|markdown|all]` - Output format
- `--parallel` - Process files in parallel
- `--continue-on-error` - Don't stop on errors

#### Examples

```bash
# Process all Lean files in directory
proof-sketcher batch *.lean --output-dir proofs/

# Process specific files
proof-sketcher batch file1.lean file2.lean file3.lean

# Parallel processing
proof-sketcher batch **/*.lean --parallel --continue-on-error
```

### `config`

Manage Proof Sketcher configuration.

```bash
proof-sketcher config [OPTIONS] COMMAND
```

#### Subcommands

##### `config show`

Display current configuration

```bash
proof-sketcher config show
```

##### `config validate`

Validate configuration file

```bash
proof-sketcher config validate config.yaml
```

##### `config generate`

Generate default configuration

```bash
proof-sketcher config generate > .proof-sketcher.yaml
```

### `cache`

Manage parsing and generation cache.

```bash
proof-sketcher cache [OPTIONS] COMMAND
```

#### Subcommands

##### `cache clear`

Clear all cached data

```bash
proof-sketcher cache clear
```

##### `cache stats`

Show cache statistics

```bash
proof-sketcher cache stats
```

##### `cache prune`

Remove old cache entries

```bash
proof-sketcher cache prune --older-than 30d
```

### `formats`

Show supported input and output formats.

```bash
proof-sketcher formats
```

Output:

```
Input formats:
  - Lean 4 (.lean)

Output formats:
  - HTML (.html) - Interactive web page
  - Markdown (.md) - Plain text with formatting
```

### `version`

Show detailed version information.

```bash
proof-sketcher version
```

Output includes:

- Proof Sketcher version
- Python version
- Platform information
- Alpha status warning

## Configuration File

Proof Sketcher looks for configuration in this order:

1. Command line `--config` option
2. `.proof-sketcher.yaml` in current directory
3. `~/.proof-sketcher.yaml` in home directory
4. Default configuration

### Configuration Schema

```yaml
# Parser settings
parser:
  timeout: 30              # Parsing timeout in seconds
  max_file_size: 1048576  # Max file size in bytes
  encoding: utf-8         # File encoding

# Generator settings
generator:
  style: normal           # concise, normal, detailed
  include_tactics: false  # Include tactic details
  max_depth: 10          # Max recursion depth

# Exporter settings
exporter:
  theme: light           # light, dark
  highlight_code: true   # Syntax highlighting
  mathjax: true         # Enable MathJax

# Cache settings
cache:
  enabled: true
  directory: ~/.proof-sketcher/cache
  max_size: 1073741824  # 1GB
  ttl: 604800           # 7 days

# Logging
logging:
  level: INFO           # DEBUG, INFO, WARNING, ERROR
  format: "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
```

## Environment Variables

- `PROOF_SKETCHER_CONFIG` - Configuration file path
- `PROOF_SKETCHER_CACHE_DIR` - Cache directory
- `PROOF_SKETCHER_LOG_LEVEL` - Logging level
- `PROOF_SKETCHER_TIMEOUT` - Global timeout

## Exit Codes

- `0` - Success
- `1` - General error
- `2` - Invalid arguments
- `3` - File not found
- `4` - Parser error
- `5` - Generator error
- `6` - Configuration error

## Alpha Limitations

Some commands may not work as expected:

- `enhance` - Not implemented
- `optimize` - Not implemented
- AI features - Not available in alpha

See [ALPHA_STATUS.md](../ALPHA_STATUS.md) for details.
