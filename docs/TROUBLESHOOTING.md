# Troubleshooting Guide

Solutions for common issues when using Proof Sketcher.

## Quick Diagnosis

Before diving into specific issues, run these diagnostic commands:

```bash
# Check installation
python -m proof_sketcher --version

# Test basic functionality
python -m proof_sketcher list-theorems examples/classical/simple_examples.lean

# Check system dependencies
claude --version  # Should show Claude CLI version
python --version  # Should be 3.9+
```

## Installation Issues

### Problem: "No module named proof_sketcher"

**Symptoms:**
```
ModuleNotFoundError: No module named 'proof_sketcher'
```

**Solutions:**

1. **Install in development mode**:
   ```bash
   cd proof-sketcher
   pip install -e .
   ```

2. **Check Python path**:
   ```bash
   python -c "import sys; print(sys.path)"
   # Should include proof-sketcher directory
   ```

3. **Use virtual environment**:
   ```bash
   python -m venv venv
   source venv/bin/activate  # On Windows: venv\Scripts\activate
   pip install -e .
   ```

### Problem: "No module named proof_sketcher.__main__"

**Symptoms:**
```
python: No module named proof_sketcher.__main__; 'proof_sketcher' is a package and cannot be directly executed
```

**Solution:**
Create missing `__main__.py` file:
```bash
echo 'from .cli import cli; cli()' > src/proof_sketcher/__main__.py
```

### Problem: Dependencies not found

**Symptoms:**
```
ImportError: No module named 'click'
ImportError: No module named 'pydantic'
```

**Solution:**
```bash
# Install with all dependencies
pip install -e ".[dev]"

# Or install missing packages manually
pip install click pydantic rich pathlib
```

## Command Line Issues

### Problem: "No such command 'generate'"

**Symptoms:**
```
Error: No such command 'generate'.
```

**Solution:**
Use the correct command name:
```bash
# Wrong
python -m proof_sketcher generate file.lean

# Correct
python -m proof_sketcher prove file.lean
```

### Problem: "No such option: --output-format"

**Symptoms:**
```
Error: No such option: --output-format
```

**Solution:**
Use correct option names:
```bash
# Wrong
--output-format markdown
--output-dir docs/

# Correct
--format markdown
--output docs/
```

### Problem: "Path does not exist"

**Symptoms:**
```
Error: Invalid value for 'LEAN_FILE': Path 'examples/file.lean' does not exist.
```

**Solutions:**

1. **Check current directory**:
   ```bash
   pwd
   ls examples/classical/
   ```

2. **Use absolute paths**:
   ```bash
   python -m proof_sketcher prove "$(pwd)/examples/classical/simple_examples.lean"
   ```

3. **Create missing directories**:
   ```bash
   mkdir -p examples/classical
   ```

## Parsing Issues

### Problem: "No theorems found in file"

**Symptoms:**
- File exists but no theorems are listed
- Empty output from `list-theorems`

**Diagnosis:**
```bash
# Check file content
head -20 examples/classical/your_file.lean

# Test Lean syntax (if Lean is installed)
lean --check examples/classical/your_file.lean

# Check with verbose output
python -m proof_sketcher list-theorems examples/classical/your_file.lean --verbose
```

**Common Causes:**

1. **Missing imports**:
   ```lean
   -- Add required imports at the top
   import Mathlib.Data.Nat.Basic
   import Mathlib.Algebra.Group.Defs
   ```

2. **Syntax errors**:
   ```lean
   -- Wrong: Missing theorem keyword
   unique_identity (G : Type*) [Group G] : ∃! e : G, ... := by

   -- Correct: Include theorem keyword
   theorem unique_identity (G : Type*) [Group G] : ∃! e : G, ... := by
   ```

3. **Incomplete proofs**:
   ```lean
   -- These may not be parsed correctly
   theorem incomplete_theorem : P := by
     sorry  -- Incomplete proof
   ```

### Problem: "Failed to parse Lean file"

**Symptoms:**
- Parser error messages
- Unexpected parsing failures

**Solutions:**

1. **Check file encoding**:
   ```bash
   file examples/classical/your_file.lean
   # Should show UTF-8 encoding
   ```

2. **Validate Lean syntax**:
   ```bash
   # If you have Lean installed
   lean --check your_file.lean
   ```

3. **Simplify the file**:
   ```lean
   -- Start with minimal example
   import Mathlib.Data.Nat.Basic
   
   theorem simple_test (n : ℕ) : n + 0 = n := by simp
   ```

4. **Check for Unicode issues**:
   ```bash
   # Look for problematic characters
   grep -P '[^\x00-\x7F]' your_file.lean
   ```

## Generation Issues

### Problem: "Claude command failed: unknown option '-m'"

**Symptoms:**
```
Failed to generate proof sketch: Claude command failed: error: unknown option '-m'
```

**Diagnosis:**
```bash
# Check Claude CLI version
claude --version

# Test Claude directly
echo "Hello" | claude
```

**Solutions:**

1. **Update Claude CLI**:
   ```bash
   # Reinstall latest version
   curl -fsSL https://claude.ai/install.sh | sh
   
   # Verify installation
   which claude
   claude --version
   ```

2. **Check PATH**:
   ```bash
   echo $PATH
   # Should include Claude installation directory
   ```

3. **Manual Claude test**:
   ```bash
   # Test basic functionality
   claude --help
   ```

### Problem: "Claude command failed: command not found"

**Symptoms:**
```
claude: command not found
```

**Solutions:**

1. **Install Claude CLI**:
   ```bash
   curl -fsSL https://claude.ai/install.sh | sh
   ```

2. **Add to PATH** (if needed):
   ```bash
   # Add to ~/.bashrc or ~/.zshrc
   export PATH="$HOME/.local/bin:$PATH"
   
   # Reload shell
   source ~/.bashrc
   ```

3. **Use alternative installation**:
   ```bash
   # Using npm (if available)
   npm install -g claude-cli
   ```

### Problem: "AI call timed out"

**Symptoms:**
```
AITimeoutError: AI call timed out after 30 seconds
```

**Solutions:**

1. **Increase timeout**:
   ```yaml
   # In config file
   generator:
     timeout: 60  # Increase to 60 seconds
   ```

2. **Simplify the theorem**:
   ```bash
   # Try with simpler theorems first
   python -m proof_sketcher prove examples/classical/simple_examples.lean \
     --theorem add_zero
   ```

3. **Check network connection**:
   ```bash
   # Test internet connectivity
   ping google.com
   curl -I https://api.anthropic.com
   ```

## Animation Issues

### Problem: "Animation generation failed"

**Symptoms:**
```
Failed to generate animation: MCP server not available
```

**Solutions:**

1. **Install Manim MCP server**:
   ```bash
   npm install -g @manim-mcp/server
   ```

2. **Start MCP server**:
   ```bash
   # Start server manually
   manim-mcp-server --port 3000
   
   # Test connection
   curl http://localhost:3000/health
   ```

3. **Skip animations for now**:
   ```bash
   # Generate without animations
   python -m proof_sketcher prove file.lean --format markdown
   ```

### Problem: "Node.js not found"

**Symptoms:**
```
node: command not found
npm: command not found
```

**Solutions:**

1. **Install Node.js**:
   ```bash
   # Using package manager (Ubuntu/Debian)
   sudo apt install nodejs npm
   
   # Using Homebrew (macOS)
   brew install node
   
   # Or download from nodejs.org
   ```

2. **Use animations without Node.js**:
   - Skip `--animate` flag for now
   - Focus on text-based explanations

## Output and Export Issues

### Problem: "Permission denied" writing to output directory

**Symptoms:**
```
PermissionError: [Errno 13] Permission denied: 'output/theorem.md'
```

**Solutions:**

1. **Check directory permissions**:
   ```bash
   ls -la output/
   ```

2. **Create output directory with proper permissions**:
   ```bash
   mkdir -p output/docs
   chmod 755 output/docs
   ```

3. **Use different output directory**:
   ```bash
   python -m proof_sketcher prove file.lean --output ~/Documents/proofs
   ```

4. **Run with appropriate permissions**:
   ```bash
   # Change ownership (if needed)
   sudo chown $USER:$USER output/
   ```

### Problem: "LaTeX not found" for PDF export

**Symptoms:**
```
FileNotFoundError: pdflatex not found
```

**Solutions:**

1. **Install LaTeX distribution**:
   ```bash
   # Ubuntu/Debian
   sudo apt install texlive-full
   
   # macOS with Homebrew
   brew install --cask mactex
   
   # Or install minimal distribution
   sudo apt install texlive-latex-base texlive-latex-recommended
   ```

2. **Use alternative formats**:
   ```bash
   # Skip PDF for now, use HTML or Markdown
   python -m proof_sketcher prove file.lean --format html
   ```

3. **Check LaTeX installation**:
   ```bash
   which pdflatex
   pdflatex --version
   ```

## Configuration Issues

### Problem: "Configuration file not found"

**Symptoms:**
```
FileNotFoundError: config.yaml not found
```

**Solutions:**

1. **Create configuration file**:
   ```bash
   python -m proof_sketcher config init
   ```

2. **Use absolute path**:
   ```bash
   python -m proof_sketcher prove file.lean --config $(pwd)/config.yaml
   ```

3. **Use default configuration**:
   ```bash
   # Run without --config flag
   python -m proof_sketcher prove file.lean
   ```

### Problem: "Invalid configuration format"

**Symptoms:**
```
yaml.parser.ParserError: Invalid YAML syntax
```

**Solutions:**

1. **Validate YAML syntax**:
   ```bash
   # Check syntax online at yaml-online-parser.appspot.com
   # Or use Python
   python -c "import yaml; yaml.safe_load(open('config.yaml'))"
   ```

2. **Fix common YAML issues**:
   ```yaml
   # Wrong: Mixed indentation
   generator:
     model: claude-3-5-sonnet
       temperature: 0.7
   
   # Correct: Consistent indentation
   generator:
     model: claude-3-5-sonnet
     temperature: 0.7
   ```

3. **Use sample configuration**:
   ```bash
   cp examples/config/basic.yaml .proof-sketcher.yaml
   ```

## Performance Issues

### Problem: "Generation is very slow"

**Symptoms:**
- Long processing times
- High CPU/memory usage

**Solutions:**

1. **Enable caching**:
   ```yaml
   cache:
     enabled: true
     ttl_hours: 24
   ```

2. **Process fewer theorems**:
   ```bash
   # Process specific theorems only
   python -m proof_sketcher prove file.lean --theorem specific_theorem
   ```

3. **Use parallel processing**:
   ```yaml
   performance:
     parallel_processing: true
     max_workers: 4
   ```

4. **Optimize configuration**:
   ```yaml
   generator:
     max_tokens: 2000  # Reduce from 4000
     temperature: 0.5  # Lower for faster generation
   ```

### Problem: "Memory usage too high"

**Solutions:**

1. **Limit cache size**:
   ```yaml
   cache:
     max_size_mb: 100  # Reduce from default
   ```

2. **Process files individually**:
   ```bash
   # Instead of processing all at once
   for file in src/*.lean; do
     python -m proof_sketcher prove "$file"
   done
   ```

3. **Monitor memory usage**:
   ```bash
   # Watch memory while running
   top -p $(pgrep -f "proof_sketcher")
   ```

## Debug Mode

When troubleshooting, enable debug mode for detailed information:

```bash
# Environment variable
export PROOF_SKETCHER_DEBUG=true

# Command line flag
python -m proof_sketcher prove file.lean --verbose

# Check log files
tail -f ~/.proof-sketcher/logs/proof_sketcher.log
```

## Getting Help

### Gather Information

When reporting issues, include:

1. **System information**:
   ```bash
   python --version
   python -m proof_sketcher --version
   uname -a  # On Unix systems
   ```

2. **Error messages**:
   ```bash
   # Full command and error output
   python -m proof_sketcher prove file.lean --verbose 2>&1 | tee error.log
   ```

3. **Configuration**:
   ```bash
   # Sanitized configuration (remove sensitive data)
   python -m proof_sketcher config show
   ```

4. **Sample files**:
   - Minimal Lean file that reproduces the issue
   - Configuration file (if relevant)

### Where to Get Help

- **GitHub Issues**: [Report bugs](https://github.com/Bright-L01/proof-sketcher/issues)
- **Discussions**: [Ask questions](https://github.com/Bright-L01/proof-sketcher/discussions)
- **Documentation**: Browse `docs/` directory
- **Examples**: Check `examples/` for working configurations

### Before Reporting

1. **Search existing issues**: Check if the problem is already reported
2. **Try minimal reproduction**: Use simplest possible example
3. **Check recent changes**: Ensure you're using the latest version
4. **Test with examples**: Verify our provided examples work

## Common Workarounds

### Temporary Solutions

1. **Skip problematic theorems**:
   ```bash
   # Process only working theorems
   python -m proof_sketcher prove file.lean --theorem working_theorem
   ```

2. **Use different output formats**:
   ```bash
   # If PDF fails, try Markdown
   python -m proof_sketcher prove file.lean --format markdown
   ```

3. **Disable features causing issues**:
   ```yaml
   cache:
     enabled: false  # If caching causes problems
   
   animator:
     enabled: false  # If animations cause problems
   ```

4. **Process files individually**:
   ```bash
   # If batch processing fails
   for file in *.lean; do
     python -m proof_sketcher prove "$file" || echo "Failed: $file"
   done
   ```

Remember: Most issues are configuration or environment related. Start with the simplest possible setup and gradually add complexity.