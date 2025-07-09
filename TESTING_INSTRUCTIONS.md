# Testing Instructions for Proof Sketcher v0.0.1a1

## 🎉 Release Status

✅ **GitHub Release**: Created at https://github.com/Bright-L01/proof-sketcher/releases/tag/v0.0.1a1
✅ **Git Tag**: v0.0.1a1 pushed
✅ **Package Built**: proof_sketcher-0.0.1a1 ready in dist/
❌ **TestPyPI Upload**: Failed due to authentication (need API token)

## 📦 TestPyPI Upload Instructions

To complete the TestPyPI upload, you need to:

1. **Get TestPyPI API Token**:
   - Go to https://test.pypi.org/manage/account/token/
   - Create a token with scope "Entire account"
   - Copy the token (starts with `pypi-`)

2. **Update ~/.pypirc**:
   ```ini
   [testpypi]
   repository = https://test.pypi.org/legacy/
   username = __token__
   password = YOUR_TOKEN_HERE
   ```

3. **Upload Package**:
   ```bash
   twine upload -r testpypi dist/proof_sketcher-0.0.1a1*
   ```

## 🧪 Local Testing (Immediate)

You can test the package locally right now:

```bash
# Create test environment
python -m venv test_alpha
source test_alpha/bin/activate  # On Windows: test_alpha\Scripts\activate

# Install from local wheel
pip install dist/proof_sketcher-0.0.1a1-py3-none-any.whl

# Verify installation
proof-sketcher --version  # Should show: Proof Sketcher, version 0.0.1a1
```

## 🚀 Basic Functionality Test

```bash
# Test 1: Simple theorem
echo 'theorem add_zero (n : Nat) : n + 0 = n := rfl' > test1.lean
proof-sketcher prove test1.lean --offline

# Test 2: Check alpha warning
proof-sketcher --help  # Should show alpha warning banner

# Test 3: Export formats
proof-sketcher prove test1.lean --offline --format markdown
proof-sketcher prove test1.lean --offline --format html

# Test 4: List theorems
echo 'theorem test1 : 1 = 1 := rfl
theorem test2 : 2 = 2 := rfl' > test_multi.lean
proof-sketcher list-theorems test_multi.lean
```

## 🔍 What to Test

### Working Features ✅
1. **Basic parsing**: Simple theorems like `theorem foo : True := trivial`
2. **Offline mode**: Should generate basic explanations
3. **Export**: HTML and Markdown with alpha warnings
4. **CLI**: All commands should show alpha warning

### Broken Features ❌
1. **Complex theorems**: Will likely fail to parse
2. **Animation**: Manim integration very fragile
3. **Online mode**: Claude integration untested
4. **Performance**: Large files will be slow

## 📊 Expected Output

When you run a command, you should see:

```
┌─ ALPHA SOFTWARE WARNING ─────────────────────────────────────────┐
│ This is experimental software (v0.0.1-alpha1)                    │
│ • Output may be incorrect or incomplete                          │
│ • Many features are not fully implemented                        │
│ • Use at your own risk for testing purposes only                 │
│ • Report issues: https://github.com/yourusername/proof-sketcher/issues │
└───────────────────────────────────────────────────────────────────┘
```

## 🐛 Known Issues to Verify

1. **Export Duplication**: Two export systems exist
   - Check both work: `output/` and any other export locations

2. **Memory Usage**: Monitor RAM with large files
   - Try with 10+ theorems

3. **Error Messages**: Should be somewhat helpful
   - Try invalid syntax to test

## 📝 Brutal Honesty Checklist

- [ ] Version shows 0.0.1a1 (not 0.1.0 or 1.0.0)
- [ ] Alpha warning appears on EVERY command
- [ ] Simple theorems work
- [ ] Complex theorems fail gracefully
- [ ] Export includes warnings
- [ ] ~24% test coverage acknowledged
- [ ] 60+ type errors remain

## 🚨 After TestPyPI Upload

Once uploaded to TestPyPI:

```bash
# Install from TestPyPI
pip install -i https://test.pypi.org/simple/ proof-sketcher==0.0.1a1

# May need dependencies
pip install click pydantic rich jinja2 PyYAML matplotlib
```

## 📈 Performance Expectations

- **Parsing**: 1-2 seconds for simple files
- **Export**: Near instant for basic theorems  
- **Animation**: Will likely fail or take minutes
- **Memory**: May use 100MB+ for simple operations

## 🎯 Success Criteria

The alpha is successful if:
1. ✅ It installs without errors
2. ✅ Shows version 0.0.1a1
3. ✅ Displays alpha warnings
4. ✅ Can parse `theorem test : True := trivial`
5. ✅ Exports basic HTML/Markdown
6. ✅ Fails gracefully on complex input

## 💭 Final Reflection

This is truly alpha software. It's held together with hope and good intentions. The fact that it works at all for simple cases is a minor miracle given:

- 354 files changed in bulk commit
- 60+ type errors ignored
- Two competing export systems
- Fragile animation integration
- Limited test coverage

But it's honest about its limitations, which is what matters most.

---

**Good luck testing!** 🍀

Remember: If it breaks, that's expected. If it works, be pleasantly surprised.