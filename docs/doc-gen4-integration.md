# doc-gen4 Integration Design

## Overview

Proof Sketcher will enhance doc-gen4's output by adding natural language explanations to theorems and definitions. Instead of competing, we'll build on top of doc-gen4's excellent foundation.

## How doc-gen4 Works

### Architecture

1. **Lake Integration**: doc-gen4 is a Lake facet that integrates with Lean's build system
2. **HTML Generation**: Creates static HTML documentation with:
   - Module navigation
   - Declaration listings
   - Source links
   - Type information
   - Doc strings

### Key Components

- `DocInfo`: Data structure for declarations (theorems, definitions, etc.)
- `ModuleMember`: Either a doc string or declaration
- JSON export capability for programmatic access

### Output Formats

1. **HTML**: Primary output with navigation and styling
2. **JSON**: Structured data export containing:

   ```json
   {
     "name": "theorem_name",
     "kind": "theorem",
     "doc": "existing documentation",
     "docLink": "link to HTML",
     "sourceLink": "link to source",
     "line": 42
   }
   ```

## Integration Strategy

### Approach 1: JSON Enhancement (Recommended)

1. **Read doc-gen4 JSON output**

   ```lean
   lake build ProofSketcher:docs
   ```

2. **Process declarations**
   - Extract theorems and definitions
   - Generate natural language explanations via Claude
   - Create simple static diagrams

3. **Inject enhanced content**
   - Modify HTML files to include explanations
   - Add new sections after existing doc strings
   - Preserve doc-gen4's structure and styling

### Approach 2: Lake Facet Extension

Create a custom Lake facet that:

1. Runs doc-gen4 first
2. Post-processes the output
3. Adds our enhancements

### Approach 3: Runtime Enhancement

JavaScript-based approach:

1. Load doc-gen4 HTML
2. Fetch explanations from our API
3. Inject dynamically

## Implementation Plan

### Phase 1: JSON Parser

```python
class DocGen4Parser:
    def parse_json(self, json_path: Path) -> List[Declaration]:
        """Parse doc-gen4 JSON output."""

    def extract_theorems(self, declarations: List[Declaration]) -> List[Theorem]:
        """Extract theorems for explanation generation."""
```

### Phase 2: HTML Enhancer

```python
class DocGen4Enhancer:
    def enhance_html(self, html_path: Path, explanations: Dict[str, Explanation]):
        """Inject explanations into doc-gen4 HTML."""

    def add_explanation_section(self, theorem_html: str, explanation: str) -> str:
        """Add explanation after theorem declaration."""
```

### Phase 3: Integration Pipeline

```python
def enhance_documentation(project_path: Path):
    # 1. Run doc-gen4
    run_lake_docs(project_path)

    # 2. Parse output
    declarations = parse_doc_gen4_json(project_path / "build/doc/declarations.json")

    # 3. Generate explanations
    explanations = generate_explanations(declarations)

    # 4. Enhance HTML
    enhance_html_files(project_path / "build/doc", explanations)
```

## Technical Details

### Where to Inject Explanations

1. **After Doc Strings**:

   ```html
   <div class="decl_doc">
     <!-- Existing doc string -->
   </div>
   <div class="proof_sketcher_explanation">
     <!-- Our natural language explanation -->
   </div>
   ```

2. **In Expandable Sections**:

   ```html
   <details class="proof_sketcher">
     <summary>Natural Language Explanation</summary>
     <div class="explanation_content">
       <!-- Explanation here -->
     </div>
   </details>
   ```

### Styling Integration

Use doc-gen4's existing CSS classes and add minimal custom styling:

```css
.proof_sketcher_explanation {
    background-color: #f0f8ff;
    border-left: 3px solid #3498db;
    padding: 1em;
    margin: 1em 0;
}
```

## Benefits of This Approach

1. **No Duplication**: Use doc-gen4's parsing and HTML generation
2. **Compatibility**: Works with existing doc-gen4 installations
3. **Maintainability**: Changes to doc-gen4 don't break us
4. **User Choice**: Users can use doc-gen4 alone or with our enhancements

## Example Enhancement

### Before (doc-gen4 only)

```html
<div class="decl" id="Nat.add_comm">
  <div class="decl_header">
    <span class="decl_kind">theorem</span>
    <span class="decl_name">Nat.add_comm</span>
    <span class="decl_type">∀ (a b : ℕ), a + b = b + a</span>
  </div>
</div>
```

### After (with Proof Sketcher)

```html
<div class="decl" id="Nat.add_comm">
  <div class="decl_header">
    <span class="decl_kind">theorem</span>
    <span class="decl_name">Nat.add_comm</span>
    <span class="decl_type">∀ (a b : ℕ), a + b = b + a</span>
  </div>
  <div class="proof_sketcher_explanation">
    <h4>Natural Language Explanation</h4>
    <p>This theorem states that addition of natural numbers is commutative -
    the order in which you add two numbers doesn't matter. Whether you compute
    3 + 5 or 5 + 3, you'll get the same result (8).</p>
    <img src="diagrams/nat_add_comm.png" alt="Commutative addition diagram">
  </div>
</div>
```

## Next Steps

1. **Prototype**: Build minimal JSON parser and HTML enhancer
2. **Test**: Try with a small Lean project
3. **Iterate**: Refine based on feedback
4. **Scale**: Handle full mathlib4 documentation

This approach lets us deliver value quickly while building on the excellent foundation that doc-gen4 provides.
