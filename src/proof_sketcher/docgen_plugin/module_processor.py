"""Module processor for enhancing doc-gen4 JSON with educational content."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any

from ..generator.progressive_generator import ProgressiveGenerator, ProgressiveSketch
from ..parser.models import TheoremInfo
from .content_generator import EducationalContentGenerator


@dataclass
class DocgenModuleInfo:
    """Information about a module from doc-gen4 JSON."""

    name: str
    doc: str | None = None
    declarations: list[dict[str, Any]] = None

    def __post_init__(self):
        if self.declarations is None:
            self.declarations = []


@dataclass
class EducationalDeclaration:
    """Enhanced declaration with educational content."""

    name: str
    kind: str  # theorem, lemma, def, etc.
    doc: str | None = None
    type: str | None = None
    original_data: dict[str, Any] = None
    educational_content: ProgressiveSketch | None = None

    def __post_init__(self):
        if self.original_data is None:
            self.original_data = {}


class ModuleProcessor:
    """Processes doc-gen4 module JSON and enhances it with educational content."""

    def __init__(self):
        """Initialize the module processor."""
        self.content_generator = EducationalContentGenerator()
        self.progressive_generator = ProgressiveGenerator()

    def enhance_module_json(self, module_json: str | dict[str, Any]) -> dict[str, Any]:
        """Enhance a doc-gen4 module JSON with educational content.

        Args:
            module_json: Either JSON string or parsed JSON dict from doc-gen4

        Returns:
            Enhanced JSON with educational content
        """
        if isinstance(module_json, str):
            data = json.loads(module_json)
        else:
            data = module_json.copy()

        # Parse module information
        module_info = self._parse_module_info(data)

        # Enhance declarations with educational content
        enhanced_declarations = []
        for decl in module_info.declarations:
            enhanced_decl = self._enhance_declaration(decl)
            enhanced_declarations.append(enhanced_decl)

        # Update the JSON data
        data["declarations"] = [asdict(decl) for decl in enhanced_declarations]
        data["educational_metadata"] = {
            "generated_at": datetime.now().isoformat(),
            "total_declarations": len(enhanced_declarations),
            "educational_declarations": len(
                [d for d in enhanced_declarations if d.educational_content]
            ),
            "generator_version": "1.0.0",
        }

        return data

    def _parse_module_info(self, data: dict[str, Any]) -> DocgenModuleInfo:
        """Parse doc-gen4 module JSON into structured info.

        Args:
            data: Raw doc-gen4 JSON data

        Returns:
            Parsed module information
        """
        return DocgenModuleInfo(
            name=data.get("name", "Unknown"),
            doc=data.get("doc"),
            declarations=data.get("declarations", []),
        )

    def _enhance_declaration(self, decl: dict[str, Any]) -> EducationalDeclaration:
        """Enhance a single declaration with educational content.

        Args:
            decl: Declaration data from doc-gen4

        Returns:
            Enhanced declaration with educational content
        """
        name = decl.get("name", "")
        kind = decl.get("kind", "")
        doc = decl.get("doc")
        type_info = decl.get("type")

        # Create enhanced declaration
        enhanced_decl = EducationalDeclaration(
            name=name, kind=kind, doc=doc, type=type_info, original_data=decl.copy()
        )

        # Generate educational content for theorems and lemmas
        if kind in ["theorem", "lemma"] and type_info:
            educational_content = self._generate_educational_content(
                name=name,
                statement=type_info,
                proof=decl.get("proof", ""),
                docstring=doc,
            )
            enhanced_decl.educational_content = educational_content

        return enhanced_decl

    def _generate_educational_content(
        self,
        name: str,
        statement: str,
        proof: str = "",
        docstring: str | None = None,
    ) -> ProgressiveSketch | None:
        """Generate educational content for a theorem or lemma.

        Args:
            name: Name of the theorem/lemma
            statement: Type/statement of the theorem
            proof: Proof term or tactic proof
            docstring: Optional documentation string

        Returns:
            Progressive educational content
        """
        try:
            # Create a basic TheoremInfo object
            theorem_info = TheoremInfo(
                name=name,
                statement=statement,
                proof=proof,
                docstring=docstring,
                dependencies=[],
                line_number=None,
                namespace=None,
                visibility="public",
                tactics=[],
                is_axiom=False,
                file_path=None,
                start_line=None,
                end_line=None,
            )

            # Generate progressive educational content
            progressive_content = (
                self.progressive_generator.generate_progressive_explanation(
                    theorem_info
                )
            )

            return progressive_content

        except Exception as e:
            # Log error but don't fail the entire process
            print(f"Warning: Could not generate educational content for {name}: {e}")
            return None

    def enhance_module_file(self, input_path: Path, output_path: Path) -> None:
        """Enhance a doc-gen4 module JSON file.

        Args:
            input_path: Path to input doc-gen4 JSON file
            output_path: Path to write enhanced JSON file
        """
        with open(input_path, encoding="utf-8") as f:
            module_json = json.load(f)

        enhanced_json = self.enhance_module_json(module_json)

        with open(output_path, "w", encoding="utf-8") as f:
            json.dump(enhanced_json, f, indent=2, ensure_ascii=False)

    def batch_enhance_modules(self, input_dir: Path, output_dir: Path) -> None:
        """Enhance all doc-gen4 JSON files in a directory.

        Args:
            input_dir: Directory containing doc-gen4 JSON files
            output_dir: Directory to write enhanced JSON files
        """
        output_dir.mkdir(parents=True, exist_ok=True)

        for json_file in input_dir.glob("*.json"):
            output_file = output_dir / json_file.name
            try:
                self.enhance_module_file(json_file, output_file)
                print(f"Enhanced: {json_file.name}")
            except Exception as e:
                print(f"Error enhancing {json_file.name}: {e}")

    def get_educational_stats(self, enhanced_json: dict[str, Any]) -> dict[str, Any]:
        """Get statistics about educational content generation.

        Args:
            enhanced_json: Enhanced module JSON

        Returns:
            Statistics about educational content
        """
        declarations = enhanced_json.get("declarations", [])

        total_declarations = len(declarations)
        educational_declarations = len(
            [d for d in declarations if d.get("educational_content") is not None]
        )

        theorem_count = len([d for d in declarations if d.get("kind") == "theorem"])
        lemma_count = len([d for d in declarations if d.get("kind") == "lemma"])

        return {
            "total_declarations": total_declarations,
            "educational_declarations": educational_declarations,
            "theorem_count": theorem_count,
            "lemma_count": lemma_count,
            "educational_coverage": (
                educational_declarations / total_declarations * 100
                if total_declarations > 0
                else 0
            ),
        }
