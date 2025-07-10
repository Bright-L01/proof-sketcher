"""Parser for doc-gen4 JSON output."""

import json
from pathlib import Path
from typing import Dict, List, Optional

from ..core.exceptions import ParserError
from .models import DocGen4Declaration, DocGen4Index, DocGen4Module


class DocGen4Parser:
    """Parse doc-gen4 JSON output."""

    def parse_index(self, json_path: Path) -> DocGen4Index:
        """Parse the main index.json file from doc-gen4.

        Args:
            json_path: Path to index.json

        Returns:
            Parsed index with all declarations and modules

        Raises:
            ParserError: If parsing fails
        """
        if not json_path.exists():
            raise ParserError(f"doc-gen4 index not found: {json_path}")

        try:
            with open(json_path, "r", encoding="utf-8") as f:
                data = json.load(f)

            return self._parse_index_data(data)

        except json.JSONDecodeError as e:
            raise ParserError(f"Invalid JSON in {json_path}: {e}")
        except Exception as e:
            raise ParserError(f"Failed to parse doc-gen4 index: {e}")

    def parse_declarations_json(self, json_path: Path) -> List[DocGen4Declaration]:
        """Parse declarations.json file.

        Args:
            json_path: Path to declarations.json

        Returns:
            List of declarations
        """
        if not json_path.exists():
            raise ParserError(f"Declarations file not found: {json_path}")

        try:
            with open(json_path, "r", encoding="utf-8") as f:
                data = json.load(f)

            declarations = []
            for item in data:
                if isinstance(item, dict):
                    decl = DocGen4Declaration.model_validate(item)
                    declarations.append(decl)

            return declarations

        except Exception as e:
            raise ParserError(f"Failed to parse declarations: {e}")

    def _parse_index_data(self, data: Dict) -> DocGen4Index:
        """Parse index data structure.

        Args:
            data: Raw JSON data

        Returns:
            Parsed index
        """
        index = DocGen4Index()

        # Parse declarations
        if "declarations" in data:
            for name, decl_data in data["declarations"].items():
                if isinstance(decl_data, dict):
                    decl_data["name"] = name  # Ensure name is set
                    decl = DocGen4Declaration.model_validate(decl_data)
                    index.declarations[name] = decl

        # Parse modules
        if "modules" in data:
            for module_name, module_data in data["modules"].items():
                if isinstance(module_data, dict):
                    module = self._parse_module(module_name, module_data)
                    index.modules[module_name] = module

        # Parse instances
        if "instances" in data:
            index.instances = data["instances"]

        return index

    def _parse_module(self, name: str, data: Dict) -> DocGen4Module:
        """Parse module data.

        Args:
            name: Module name
            data: Module data

        Returns:
            Parsed module
        """
        module = DocGen4Module(name=name)

        # Parse declarations in module
        if "declarations" in data:
            for decl_item in data["declarations"]:
                if isinstance(decl_item, dict):
                    decl = DocGen4Declaration.model_validate(decl_item)
                    module.declarations.append(decl)

        # Parse imports
        if "imports" in data:
            module.imports = data["imports"]

        # Parse instances
        if "instances" in data:
            # Parse instance data - format may vary
            pass

        return module

    def extract_theorems_for_explanation(
        self,
        index: DocGen4Index,
        module_filter: Optional[str] = None,
        limit: Optional[int] = None,
    ) -> List[DocGen4Declaration]:
        """Extract theorems that need explanations.

        Args:
            index: Parsed doc-gen4 index
            module_filter: Optional module name to filter by
            limit: Maximum number of theorems to return

        Returns:
            List of theorems for explanation generation
        """
        theorems = []

        if module_filter:
            theorems = index.get_module_theorems(module_filter)
        else:
            theorems = index.get_all_theorems()

        # Filter theorems that need explanations
        theorems = [t for t in theorems if t.needs_explanation]

        # Sort by name for consistency
        theorems.sort(key=lambda t: t.name)

        # Apply limit if specified
        if limit:
            theorems = theorems[:limit]

        return theorems
