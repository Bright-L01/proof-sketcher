"""Data models for doc-gen4 integration."""

from pathlib import Path
from typing import Dict, List, Optional

from pydantic import BaseModel, Field


class DocGen4Declaration(BaseModel):
    """Represents a declaration from doc-gen4 JSON output."""

    name: str = Field(..., description="Full name of the declaration")
    kind: str = Field(..., description="Type: theorem, def, inductive, etc.")
    doc: Optional[str] = Field(None, description="Documentation string")
    docLink: Optional[str] = Field(None, description="Link to HTML documentation")
    sourceLink: Optional[str] = Field(None, description="Link to source code")
    line: Optional[int] = Field(None, description="Line number in source")
    type: Optional[str] = Field(None, description="Type signature")

    @property
    def is_theorem(self) -> bool:
        """Check if this is a theorem."""
        return self.kind == "theorem"

    @property
    def is_definition(self) -> bool:
        """Check if this is a definition."""
        return self.kind in ["def", "definition"]

    @property
    def needs_explanation(self) -> bool:
        """Check if this declaration would benefit from explanation."""
        return self.is_theorem or self.is_definition


class DocGen4Instance(BaseModel):
    """Represents a type class instance."""

    name: str
    className: str
    type: Optional[str] = None


class DocGen4Module(BaseModel):
    """Represents a module from doc-gen4 JSON output."""

    name: str = Field(..., description="Module name")
    declarations: List[DocGen4Declaration] = Field(
        default_factory=list, description="Declarations in this module"
    )
    instances: List[DocGen4Instance] = Field(
        default_factory=list, description="Type class instances"
    )
    imports: List[str] = Field(default_factory=list, description="Imported modules")

    def get_theorems(self) -> List[DocGen4Declaration]:
        """Get all theorems in this module."""
        return [d for d in self.declarations if d.is_theorem]

    def get_definitions(self) -> List[DocGen4Declaration]:
        """Get all definitions in this module."""
        return [d for d in self.declarations if d.is_definition]


class DocGen4Index(BaseModel):
    """Represents the full doc-gen4 index."""

    declarations: Dict[str, DocGen4Declaration] = Field(
        default_factory=dict, description="All declarations indexed by name"
    )
    modules: Dict[str, DocGen4Module] = Field(
        default_factory=dict, description="All modules indexed by name"
    )
    instances: Dict[str, List[str]] = Field(
        default_factory=dict, description="Type class instances indexed by class name"
    )

    def get_all_theorems(self) -> List[DocGen4Declaration]:
        """Get all theorems across all modules."""
        return [d for d in self.declarations.values() if d.is_theorem]

    def get_module_theorems(self, module_name: str) -> List[DocGen4Declaration]:
        """Get theorems from a specific module."""
        if module_name in self.modules:
            return self.modules[module_name].get_theorems()
        return []


class EnhancedDeclaration(BaseModel):
    """Declaration with natural language explanation."""

    declaration: DocGen4Declaration
    explanation: str = Field(..., description="Natural language explanation")
    diagram_path: Optional[Path] = Field(None, description="Path to diagram")
    examples: List[str] = Field(
        default_factory=list, description="Example applications"
    )

    @property
    def has_diagram(self) -> bool:
        """Check if a diagram is available."""
        return self.diagram_path is not None and self.diagram_path.exists()
