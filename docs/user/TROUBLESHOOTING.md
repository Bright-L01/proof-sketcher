# Troubleshooting Guide

Common issues and solutions for Proof Sketcher users.

## Installation Issues

### "command not found: proof-sketcher"

**Symptoms:**

```bash
$ proof-sketcher --version
bash: proof-sketcher: command not found
```

**Solutions:**

1. **Check if installed correctly:**

   ```bash
   pip show proof-sketcher
   ```

2. **Verify pip installation path:**

   ```bash
   pip show -f proof-sketcher | grep Location
   ```

3. **Add to PATH if needed:**

   ```bash
   # For bash/zsh
   export PATH="$HOME/.local/bin:$PATH"

   # Make permanent
   echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.bashrc
   source ~/.bashrc
   ```

4. **Reinstall with user flag:**

   ```bash
   pip install --user proof-sketcher
   ```

5. **Use pipx (recommended):**

   ```bash
   pipx install proof-sketcher
   ```

### Python Version Incompatibility

**Symptoms:**

```
ERROR: proof-sketcher requires Python >=3.10
```

**Solutions:**

1. **Check Python version:**

   ```bash
   python --version
   python3 --version
   ```

2. **Install compatible Python:**

   ```bash
   # macOS with Homebrew
   brew install python@3.12

   # Ubuntu/Debian
   sudo apt update
   sudo apt install python3.12 python3.12-pip

   # Using pyenv
   pyenv install 3.12.0
   pyenv global 3.12.0
   ```

3. **Use virtual environment:**

   ```bash
   python3.12 -m venv proof-sketcher-env
   source proof-sketcher-env/bin/activate
   pip install proof-sketcher
   ```

### Dependency Conflicts

**Symptoms:**

```
ERROR: pip's dependency resolver does not currently consider pre-releases
```

**Solutions:**

1. **Update pip:**

   ```bash
   pip install --upgrade pip
   ```

2. **Use clean virtual environment:**

   ```bash
   python -m venv clean-env
   source clean-env/bin/activate
   pip install proof-sketcher
   ```

3. **Install with no-deps and resolve manually:**

   ```bash
   pip install --no-deps proof-sketcher
   pip install -r requirements.txt
   ```

## Lean 4 Integration Issues

### "Lean executable not found"

**Symptoms:**

```
Error: Cannot find Lean executable. Please ensure Lean 4 is installed.
```

**Solutions:**

1. **Check Lean installation:**

   ```bash
   which lean
   lean --version
   ```

2. **Install Lean 4 via elan:**

   ```bash
   curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
   source ~/.elan/env
   ```

3. **Verify PATH includes Lean:**

   ```bash
   echo $PATH | grep -o elan
   export PATH="$HOME/.elan/bin:$PATH"
   ```

4. **Configure custom Lean path:**

   ```yaml
   # .proof-sketcher.yaml
   parser:
     lean_executable: "/custom/path/to/lean"
     lake_executable: "/custom/path/to/lake"
   ```

### Lake Project Not Found

**Symptoms:**

```
Warning: No lakefile.lean found. Proceeding without project context.
```

**Solutions:**

1. **Initialize Lake project:**

   ```bash
   lake init MyProject
   cd MyProject
   proof-sketcher prove Main.lean
   ```

2. **Navigate to project root:**

   ```bash
   # Find lakefile.lean
   find . -name "lakefile.lean" -type f
   cd /path/to/project/root
   ```

3. **Disable Lake integration:**

   ```bash
   proof-sketcher prove myfile.lean --no-lake
   ```

### Mathlib Dependencies

**Symptoms:**

```
Error: Unknown identifier 'Mathlib.Data.Nat.Basic'
```

**Solutions:**

1. **Update dependencies:**

   ```bash
   lake update
   lake build
   ```

2. **Check dependency versions:**

   ```bash
   lake env lean --version
   cat lake-manifest.json | grep mathlib
   ```

3. **Clean and rebuild:**

   ```bash
   lake clean
   lake build
   ```

## Parsing Issues

### No Theorems Found

**Symptoms:**

```
Warning: No theorems found in file.lean
```

**Solutions:**

1. **Check file syntax:**

   ```bash
   lean --check yourfile.lean
   ```

2. **Verify theorem structure:**

   ```lean
   -- Correct format
   theorem my_theorem : 1 = 1 := by
     rfl

   -- Common mistakes to avoid
   def my_function : Nat := 1  -- This is a definition, not a theorem
   #check 1 = 1               -- This is a command, not a theorem
   ```

3. **Check file encoding:**

   ```bash
   file --mime-encoding yourfile.lean
   # Should output: text/plain; charset=utf-8
   ```

4. **Increase parser timeout:**

   ```bash
   proof-sketcher prove yourfile.lean --parser-timeout 60
   ```

### Parsing Timeout

**Symptoms:**

```
Error: Parser timeout after 30 seconds
```

**Solutions:**

1. **Increase timeout:**

   ```yaml
   # .proof-sketcher.yaml
   parser:
     lean_timeout: 120  # seconds
   ```

2. **Split large files:**

   ```bash
   # Process files individually
   proof-sketcher batch ./src/ --chunk-size 1
   ```

3. **Check file complexity:**

   ```bash
   wc -l *.lean  # Count lines
   grep -c "theorem\|lemma\|def" *.lean  # Count definitions
   ```

### Unicode Issues

**Symptoms:**

```
Error: Invalid character in Lean file
```

**Solutions:**

1. **Check file encoding:**

   ```bash
   file --mime-encoding yourfile.lean
   iconv -f utf-8 -t utf-8 yourfile.lean > temp.lean
   mv temp.lean yourfile.lean
   ```

2. **Handle BOM (Byte Order Mark):**

   ```bash
   # Remove BOM if present
   sed -i '1s/^\xEF\xBB\xBF//' yourfile.lean
   ```

3. **Validate Unicode:**

   ```bash
   python3 -c "
   with open('yourfile.lean', 'r', encoding='utf-8') as f:
       content = f.read()
       print('File is valid UTF-8')
   "
   ```

## Generation Issues

### Claude API Errors

**Symptoms:**

```
Error: Claude API rate limit exceeded
Error: Claude API authentication failed
```

**Solutions:**

1. **Use offline mode:**

   ```bash
   proof-sketcher prove yourfile.lean --offline
   ```

2. **Configure retry settings:**

   ```yaml
   # .proof-sketcher.yaml
   generator:
     max_retries: 5
     retry_delay: 2.0
     timeout: 120
   ```

3. **Check Claude CLI installation:**

   ```bash
   which claude
   claude --version
   ```

4. **Use cached responses:**

   ```yaml
   generator:
     cache_responses: true
     cache_ttl: 86400  # 24 hours
   ```

### Generation Timeout

**Symptoms:**

```
Error: Generation timeout after 60 seconds
```

**Solutions:**

1. **Increase timeout:**

   ```bash
   proof-sketcher prove yourfile.lean --timeout 180
   ```

2. **Use simpler model:**

   ```yaml
   generator:
     model: "claude-3-haiku-20240307"  # Faster model
     temperature: 0.5
   ```

3. **Process smaller theorems:**

   ```bash
   # Filter by complexity
   proof-sketcher batch ./src/ --max-proof-length 50
   ```

### Poor Quality Output

**Symptoms:**

- Generic explanations
- Missing mathematical content
- Incorrect step descriptions

**Solutions:**

1. **Adjust model parameters:**

   ```yaml
   generator:
     model: "claude-3-opus-20240229"  # Higher quality
     temperature: 0.3  # More focused
     max_tokens: 4096  # Longer responses
   ```

2. **Provide better context:**

   ```lean
   /--
   This theorem proves the fundamental property of addition
   that adding zero to any natural number leaves it unchanged.

   This is proved by mathematical induction on the natural number.
   -/
   theorem add_zero (n : Nat) : n + 0 = n := by
     induction n with
     | zero => rfl
     | succ n ih => rw [Nat.add_succ, ih]
   ```

3. **Use difficulty-appropriate prompts:**

   ```bash
   proof-sketcher prove advanced.lean --difficulty advanced
   proof-sketcher prove intro.lean --difficulty beginner
   ```

## Animation Issues

### MCP Server Connection Failed

**Symptoms:**

```
Error: Cannot connect to Manim MCP server
```

**Solutions:**

1. **Check server status:**

   ```bash
   # Start server manually
   manim-mcp-server --port 8000

   # Test connection
   curl http://localhost:8000/health
   ```

2. **Configure server settings:**

   ```yaml
   # .proof-sketcher.yaml
   manim:
     host: "localhost"
     port: 8000
     timeout: 300
     max_retries: 3
   ```

3. **Use fallback mode:**

   ```bash
   proof-sketcher prove yourfile.lean --no-animation
   ```

4. **Check dependencies:**

   ```bash
   pip install manim
   ffmpeg -version
   ```

### Animation Rendering Failed

**Symptoms:**

```
Error: Animation rendering failed with exit code 1
```

**Solutions:**

1. **Check video codecs:**

   ```bash
   # macOS
   brew install ffmpeg

   # Ubuntu/Debian
   sudo apt install ffmpeg

   # Test rendering
   ffmpeg -f lavfi -i testsrc=duration=1:size=320x240:rate=1 test.mp4
   ```

2. **Reduce animation quality:**

   ```yaml
   animator:
     animation_config:
       quality: "low"
       fps: 15
       width: 720
       height: 480
   ```

3. **Check disk space:**

   ```bash
   df -h /tmp
   df -h .
   ```

4. **Use alternative temp directory:**

   ```yaml
   manim:
     temp_dir: "/path/to/writable/temp"
   ```

## Performance Issues

### High Memory Usage

**Symptoms:**

```
Error: MemoryError - insufficient memory
Process killed (OOM)
```

**Solutions:**

1. **Limit memory usage:**

   ```yaml
   # .proof-sketcher.yaml
   performance:
     memory_limit_mb: 2048
     cache_size_mb: 256
   ```

2. **Process in smaller batches:**

   ```bash
   proof-sketcher batch ./src/ --chunk-size 10 --max-workers 2
   ```

3. **Clear cache regularly:**

   ```bash
   proof-sketcher cache clear --older-than 24h
   ```

4. **Use streaming mode:**

   ```bash
   proof-sketcher batch ./src/ --stream --no-cache
   ```

### Slow Processing

**Symptoms:**

- Very slow batch processing
- Long waits between theorems
- High CPU usage

**Solutions:**

1. **Optimize concurrency:**

   ```bash
   # Use all CPU cores
   proof-sketcher batch ./src/ --max-workers $(nproc)

   # Conservative approach
   proof-sketcher batch ./src/ --max-workers 2
   ```

2. **Enable caching:**

   ```yaml
   generator:
     cache_responses: true
   ```

3. **Skip animations for speed:**

   ```bash
   proof-sketcher batch ./src/ --no-animation
   ```

4. **Use faster model:**

   ```yaml
   generator:
     model: "claude-3-haiku-20240307"
   ```

### Large File Issues

**Symptoms:**

```
Error: File too large (>10MB)
Error: Too many theorems in single file
```

**Solutions:**

1. **Increase limits:**

   ```yaml
   parser:
     max_file_size: 52428800  # 50MB
     max_theorems_per_file: 500
   ```

2. **Split large files:**

   ```python
   # split_lean_file.py
   import re

   def split_lean_file(filename, max_theorems=50):
       with open(filename) as f:
           content = f.read()

       theorems = re.findall(r'theorem .*?(?=theorem|\Z)', content, re.DOTALL)

       for i, chunk in enumerate([theorems[i:i+max_theorems]
                                 for i in range(0, len(theorems), max_theorems)]):
           with open(f'{filename}.part{i}.lean', 'w') as f:
               f.write(''.join(chunk))
   ```

3. **Process selectively:**

   ```bash
   # Process only specific theorems
   proof-sketcher prove largefile.lean --theorem-pattern "main_*"
   ```

## Export Issues

### HTML Export Errors

**Symptoms:**

```
Error: Template not found
Error: Asset file missing
```

**Solutions:**

1. **Check template paths:**

   ```bash
   proof-sketcher config show | grep template_paths
   ```

2. **Use built-in templates:**

   ```bash
   proof-sketcher prove yourfile.lean --template default
   ```

3. **Install missing dependencies:**

   ```bash
   pip install jinja2 markdown beautifulsoup4
   ```

4. **Verify output directory:**

   ```bash
   mkdir -p output/html
   chmod 755 output/html
   ```

### PDF Generation Issues

**Symptoms:**

```
Error: LaTeX not found
Error: PDF compilation failed
```

**Solutions:**

1. **Install LaTeX:**

   ```bash
   # macOS
   brew install mactex

   # Ubuntu/Debian
   sudo apt install texlive-full

   # Minimal install
   sudo apt install texlive-latex-base texlive-fonts-recommended
   ```

2. **Check LaTeX installation:**

   ```bash
   which pdflatex
   pdflatex --version
   ```

3. **Use alternative PDF method:**

   ```bash
   # Generate HTML then convert
   proof-sketcher prove yourfile.lean --format html
   wkhtmltopdf output.html output.pdf
   ```

## Configuration Issues

### Invalid Configuration

**Symptoms:**

```
Error: Invalid configuration file
YAML parsing error
```

**Solutions:**

1. **Validate YAML syntax:**

   ```bash
   python -c "import yaml; yaml.safe_load(open('.proof-sketcher.yaml'))"
   ```

2. **Use configuration validator:**

   ```bash
   proof-sketcher config validate
   proof-sketcher config validate --file myconfig.yaml
   ```

3. **Reset to defaults:**

   ```bash
   proof-sketcher config save --output .proof-sketcher.yaml --defaults
   ```

4. **Check for common YAML errors:**

   ```yaml
   # Correct indentation
   parser:
     lean_timeout: 30

   # Incorrect (mixing tabs and spaces)
   parser:
    lean_timeout: 30
   ```

### Environment Variables Not Working

**Symptoms:**

- Settings not applied
- Environment overrides ignored

**Solutions:**

1. **Check variable names:**

   ```bash
   # Correct format
   export PROOF_SKETCHER_DEBUG=true
   export PROOF_SKETCHER_PARSER_LEAN_TIMEOUT=60

   # Verify
   env | grep PROOF_SKETCHER
   ```

2. **Test override:**

   ```bash
   PROOF_SKETCHER_DEBUG=true proof-sketcher config show
   ```

3. **Check shell configuration:**

   ```bash
   # Make permanent
   echo 'export PROOF_SKETCHER_DEBUG=true' >> ~/.bashrc
   source ~/.bashrc
   ```

## Debugging Tools

### Verbose Output

```bash
# Enable debug logging
proof-sketcher prove yourfile.lean --debug

# Increase verbosity
proof-sketcher prove yourfile.lean -vvv

# Log to file
proof-sketcher prove yourfile.lean --debug --log-file debug.log
```

### Configuration Inspection

```bash
# Show effective configuration
proof-sketcher config show --resolved

# Show configuration sources
proof-sketcher config show --sources

# Validate configuration
proof-sketcher config validate --verbose
```

### Cache Inspection

```bash
# Show cache contents
proof-sketcher cache list

# Show cache statistics
proof-sketcher cache stats

# Clear specific entries
proof-sketcher cache clear --pattern "problematic_*"
```

### System Information

```bash
# Show system info
proof-sketcher info

# Check dependencies
proof-sketcher info --dependencies

# Test configuration
proof-sketcher test-config
```

## Getting Help

### Community Resources

1. **GitHub Issues**: <https://github.com/brightliu/proof-sketcher/issues>
2. **Documentation**: <https://proof-sketcher.readthedocs.io>
3. **Lean Zulip**: <https://leanprover.zulipchat.com>

### Creating Bug Reports

When filing an issue, include:

1. **System information:**

   ```bash
   proof-sketcher info > system-info.txt
   ```

2. **Error logs:**

   ```bash
   proof-sketcher prove problematic.lean --debug --log-file error.log 2>&1
   ```

3. **Minimal example:**

   ```lean
   -- Simplest file that reproduces the issue
   theorem simple_issue : 1 = 1 := by rfl
   ```

4. **Configuration:**

   ```bash
   proof-sketcher config show --anonymized > config.yaml
   ```

### Self-Diagnosis Checklist

Before reporting issues:

- [ ] Updated to latest version: `pip install --upgrade proof-sketcher`
- [ ] Checked [known issues](https://github.com/brightliu/proof-sketcher/issues)
- [ ] Tried with minimal configuration
- [ ] Tested with simple example file
- [ ] Verified Lean 4 installation
- [ ] Checked disk space and permissions
- [ ] Reviewed this troubleshooting guide

### Emergency Recovery

If Proof Sketcher is completely broken:

1. **Reset everything:**

   ```bash
   pip uninstall proof-sketcher
   rm -rf ~/.proof-sketcher/
   pip install proof-sketcher
   proof-sketcher config init
   ```

2. **Use Docker alternative:**

   ```bash
   docker run --rm -v $(pwd):/workspace proof-sketcher/cli prove /workspace/yourfile.lean
   ```

3. **Manual processing:**

   ```bash
   # Use Lean directly for parsing
   lean --json yourfile.lean > ast.json

   # Use Claude CLI directly for generation
   claude "Explain this Lean theorem: $(cat yourfile.lean)"
   ```

Remember: Most issues have simple solutions. Start with the basics (installation, file syntax, permissions) before diving into complex debugging.
