"""HTML enhancer for doc-gen4 output."""

import re
from pathlib import Path
from typing import Dict, List, Optional

from bs4 import BeautifulSoup, Tag

from ..core.exceptions import ProofSketcherError
from .models import DocGen4Declaration, EnhancedDeclaration


class DocGen4Enhancer:
    """Enhance doc-gen4 HTML with natural language explanations."""

    def __init__(self):
        """Initialize the enhancer."""
        self.enhanced_count = 0
        self.error_count = 0

    def enhance_html_file(
        self,
        html_path: Path,
        explanations: Dict[str, EnhancedDeclaration],
        backup: bool = True,
    ) -> None:
        """Enhance a single HTML file with explanations.

        Args:
            html_path: Path to doc-gen4 HTML file
            explanations: Map of theorem names to enhanced declarations
            backup: Whether to create backup of original file

        Raises:
            ProofSketcherError: If enhancement fails
        """
        if not html_path.exists():
            raise ProofSketcherError(f"HTML file not found: {html_path}")

        # Create backup if requested
        if backup:
            backup_path = html_path.with_suffix(".html.backup")
            backup_path.write_bytes(html_path.read_bytes())

        try:
            # Parse HTML
            with open(html_path, "r", encoding="utf-8") as f:
                soup = BeautifulSoup(f.read(), "html.parser")

            # Find and enhance declarations
            for decl_div in soup.find_all("div", class_="decl"):
                decl_id = decl_div.get("id")
                if decl_id and decl_id in explanations:
                    self._inject_explanation(decl_div, explanations[decl_id])
                    self.enhanced_count += 1

            # Add our CSS if not already present
            if not soup.find("style", id="proof-sketcher-styles"):
                self._inject_css(soup)

            # Write enhanced HTML
            with open(html_path, "w", encoding="utf-8") as f:
                f.write(str(soup))

        except Exception as e:
            self.error_count += 1
            raise ProofSketcherError(f"Failed to enhance {html_path}: {e}")

    def enhance_documentation(
        self,
        doc_dir: Path,
        explanations: Dict[str, EnhancedDeclaration],
        module_filter: Optional[str] = None,
    ) -> Dict[str, int]:
        """Enhance all documentation in a directory.

        Args:
            doc_dir: doc-gen4 output directory
            explanations: Map of theorem names to enhanced declarations
            module_filter: Optional module name pattern to filter files

        Returns:
            Statistics about enhancement process
        """
        self.enhanced_count = 0
        self.error_count = 0
        processed_files = 0

        # Find all HTML files
        pattern = f"{module_filter}*.html" if module_filter else "*.html"
        html_files = list(doc_dir.rglob(pattern))

        for html_file in html_files:
            # Skip index and nav files
            if html_file.name in ["index.html", "nav.html", "search.html"]:
                continue

            try:
                self.enhance_html_file(html_file, explanations)
                processed_files += 1
            except ProofSketcherError as e:
                print(f"Warning: {e}")

        return {
            "files_processed": processed_files,
            "declarations_enhanced": self.enhanced_count,
            "errors": self.error_count,
        }

    def _inject_explanation(self, decl_div: Tag, enhanced: EnhancedDeclaration) -> None:
        """Inject explanation into declaration div.

        Args:
            decl_div: BeautifulSoup tag for declaration
            enhanced: Enhanced declaration with explanation
        """
        # Create explanation div
        explanation_div = Tag(name="div")
        explanation_div["class"] = ["proof-sketcher-explanation"]

        # Add header
        header = Tag(name="h4")
        header.string = "Natural Language Explanation"
        explanation_div.append(header)

        # Add explanation text
        explanation_p = Tag(name="p")
        explanation_p.string = enhanced.explanation
        explanation_div.append(explanation_p)

        # Add diagram if available
        if enhanced.has_diagram:
            img = Tag(name="img")
            img["src"] = f"diagrams/{enhanced.diagram_path.name}"
            img["alt"] = f"Diagram for {enhanced.declaration.name}"
            img["class"] = ["proof-sketcher-diagram"]
            explanation_div.append(img)

        # Add examples if available
        if enhanced.examples:
            examples_div = Tag(name="div")
            examples_div["class"] = ["proof-sketcher-examples"]

            examples_header = Tag(name="h5")
            examples_header.string = "Examples"
            examples_div.append(examples_header)

            examples_list = Tag(name="ul")
            for example in enhanced.examples:
                li = Tag(name="li")
                li.string = example
                examples_list.append(li)
            examples_div.append(examples_list)

            explanation_div.append(examples_div)

        # Find where to insert (after decl_header or decl_doc)
        insert_after = decl_div.find("div", class_="decl_doc")
        if not insert_after:
            insert_after = decl_div.find("div", class_="decl_header")

        if insert_after:
            insert_after.insert_after(explanation_div)

    def _inject_css(self, soup: BeautifulSoup) -> None:
        """Inject our CSS styles into the document.

        Args:
            soup: BeautifulSoup document
        """
        style = Tag(name="style")
        style["id"] = "proof-sketcher-styles"
        style.string = """
/* Proof Sketcher Styles */
.proof-sketcher-explanation {
    background-color: #f0f8ff;
    border-left: 3px solid #3498db;
    padding: 1em;
    margin: 1em 0;
    border-radius: 0 4px 4px 0;
}

.proof-sketcher-explanation h4 {
    margin-top: 0;
    color: #2c3e50;
    font-size: 1.1em;
}

.proof-sketcher-explanation p {
    line-height: 1.6;
    color: #34495e;
}

.proof-sketcher-diagram {
    max-width: 100%;
    margin: 1em 0;
    border: 1px solid #ddd;
    border-radius: 4px;
}

.proof-sketcher-examples {
    margin-top: 1em;
}

.proof-sketcher-examples h5 {
    color: #2c3e50;
    font-size: 1em;
    margin-bottom: 0.5em;
}

.proof-sketcher-examples ul {
    margin-top: 0.5em;
}

/* Dark mode support */
@media (prefers-color-scheme: dark) {
    .proof-sketcher-explanation {
        background-color: #1a2332;
        border-left-color: #3498db;
    }

    .proof-sketcher-explanation h4,
    .proof-sketcher-explanation h5 {
        color: #ecf0f1;
    }

    .proof-sketcher-explanation p {
        color: #bdc3c7;
    }

    .proof-sketcher-diagram {
        border-color: #34495e;
    }
}
"""

        # Add to head
        head = soup.find("head")
        if head:
            head.append(style)
