"""Main integration pipeline for doc-gen4 enhancement."""

import json
import subprocess
from pathlib import Path
from typing import Dict, List, Optional

from ..core.exceptions import ProofSketcherError
from ..generator import ClaudeGenerator
from .enhancer import DocGen4Enhancer
from .models import DocGen4Declaration, EnhancedDeclaration
from .parser import DocGen4Parser


class DocGen4Integration:
    """Orchestrate the doc-gen4 enhancement process."""

    def __init__(self, generator: Optional[ClaudeGenerator] = None):
        """Initialize integration.

        Args:
            generator: Optional Claude generator for explanations
        """
        self.parser = DocGen4Parser()
        self.enhancer = DocGen4Enhancer()
        self.generator = generator

    def enhance_project(
        self,
        project_path: Path,
        output_dir: Optional[Path] = None,
        module_filter: Optional[str] = None,
        limit: Optional[int] = None,
        offline: bool = False,
    ) -> Dict[str, int]:
        """Enhance a Lean project's documentation.

        Args:
            project_path: Path to Lean project root
            output_dir: Optional output directory (defaults to build/doc)
            module_filter: Optional module name filter
            limit: Maximum number of theorems to process
            offline: Whether to use offline mode (no Claude API)

        Returns:
            Statistics about the enhancement process
        """
        # Verify project
        if not project_path.exists():
            raise ProofSketcherError(f"Project not found: {project_path}")

        lakefile = project_path / "lakefile.lean"
        if not lakefile.exists():
            raise ProofSketcherError(
                f"Not a Lean project (no lakefile.lean): {project_path}"
            )

        # Step 1: Run doc-gen4 if needed
        doc_dir = output_dir or project_path / "build" / "doc"
        if not doc_dir.exists():
            print("Running doc-gen4...")
            self._run_docgen4(project_path)

        # Step 2: Parse doc-gen4 output
        print("Parsing doc-gen4 output...")
        declarations_json = doc_dir / "declarations.json"
        if not declarations_json.exists():
            # Try alternate locations
            index_json = doc_dir / "index.json"
            if index_json.exists():
                index = self.parser.parse_index(index_json)
                theorems = self.parser.extract_theorems_for_explanation(
                    index, module_filter, limit
                )
            else:
                raise ProofSketcherError(
                    f"No doc-gen4 output found. Run: lake build <project>:docs"
                )
        else:
            declarations = self.parser.parse_declarations_json(declarations_json)
            theorems = [d for d in declarations if d.needs_explanation]
            if module_filter:
                theorems = [t for t in theorems if module_filter in t.name]
            if limit:
                theorems = theorems[:limit]

        print(f"Found {len(theorems)} theorems to enhance")

        # Step 3: Generate explanations
        print("Generating explanations...")
        explanations = self._generate_explanations(theorems, offline)

        # Step 4: Enhance HTML
        print("Enhancing HTML documentation...")
        stats = self.enhancer.enhance_documentation(
            doc_dir, explanations, module_filter
        )

        return stats

    def _run_docgen4(self, project_path: Path) -> None:
        """Run doc-gen4 on the project.

        Args:
            project_path: Path to Lean project

        Raises:
            ProofSketcherError: If doc-gen4 fails
        """
        try:
            # Try to find the docs target
            result = subprocess.run(
                ["lake", "build", "--help"],
                cwd=project_path,
                capture_output=True,
                text=True,
            )

            # Common patterns for docs targets
            docs_targets = [":docs", ":doc", "docs", "doc"]

            for target in docs_targets:
                cmd = ["lake", "build", target]
                result = subprocess.run(
                    cmd, cwd=project_path, capture_output=True, text=True
                )

                if result.returncode == 0:
                    return

            # If no standard target, inform user
            raise ProofSketcherError(
                "Could not find doc-gen4 target. " "Please run doc-gen4 manually first."
            )

        except subprocess.SubprocessError as e:
            raise ProofSketcherError(f"Failed to run doc-gen4: {e}")

    def _generate_explanations(
        self, theorems: List[DocGen4Declaration], offline: bool
    ) -> Dict[str, EnhancedDeclaration]:
        """Generate natural language explanations.

        Args:
            theorems: List of theorems to explain
            offline: Whether to use offline mode

        Returns:
            Map of theorem names to enhanced declarations
        """
        explanations = {}

        for theorem in theorems:
            if offline:
                # Use placeholder in offline mode
                explanation = self._generate_offline_explanation(theorem)
            else:
                # Use Claude API
                if self.generator:
                    # Convert DocGen4Declaration to TheoremInfo
                    from ..parser.models import TheoremInfo

                    theorem_info = TheoremInfo(
                        name=theorem.name,
                        statement=theorem.type or "",
                        docstring=theorem.doc,
                        line_number=theorem.line,
                    )
                    proof_sketch = self.generator.generate_proof_sketch(theorem_info)
                    explanation = proof_sketch.introduction
                else:
                    explanation = self._generate_offline_explanation(theorem)

            enhanced = EnhancedDeclaration(declaration=theorem, explanation=explanation)

            explanations[theorem.name] = enhanced

        return explanations

    def _generate_offline_explanation(self, theorem: DocGen4Declaration) -> str:
        """Generate placeholder explanation in offline mode.

        Args:
            theorem: Theorem to explain

        Returns:
            Placeholder explanation text
        """
        if theorem.doc:
            # Use existing doc string as base
            return f"{theorem.doc}\n\n[Natural language explanation would be generated here by Claude API]"
        else:
            # Generic placeholder
            return (
                f"This {theorem.kind} '{theorem.name}' defines important mathematical properties. "
                f"A natural language explanation would be generated here by the Claude API, "
                f"making the concept accessible to newcomers."
            )
