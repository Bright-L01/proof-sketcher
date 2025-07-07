"""Base classes and utilities for prompt templates."""

from typing import List
from abc import ABC, abstractmethod

from jinja2 import BaseLoader, Environment, Template


class PromptBase(ABC):
    """Base class for prompt template providers."""
    
    def __init__(self) -> None:
        """Initialize with Jinja2 environment."""
        self.env = Environment(
            loader=BaseLoader(), 
            trim_blocks=True, 
            lstrip_blocks=True,
            autoescape=True  # Enable XSS protection
        )
        
        # Add custom filters
        self.env.filters["format_dependencies"] = self._format_dependencies
        self.env.filters["format_statement"] = self._format_statement
    
    def _format_dependencies(self, dependencies: List[str]) -> str:
        """Format dependencies list for display."""
        if not dependencies:
            return "None"
        if len(dependencies) <= 3:
            return ", ".join(dependencies)
        return f"{', '.join(dependencies[:3])}, and {len(dependencies) - 3} others"
    
    def _format_statement(self, statement: str) -> str:
        """Format theorem statement for better readability."""
        # Clean up common Lean syntax for natural language
        replacements = [
            ("∀", "for all"),
            ("∃", "there exists"),
            ("→", "implies"),
            ("↔", "if and only if"),
            ("¬", "not"),
            ("∧", "and"),
            ("∨", "or"),
        ]
        
        result = statement
        for lean_symbol, natural_text in replacements:
            result = result.replace(lean_symbol, natural_text)
        
        return result
    
    @abstractmethod
    def get_template_string(self) -> str:
        """Get the template string for this prompt type."""
        pass
    
    def get_template(self) -> Template:
        """Get compiled Jinja2 template."""
        return self.env.from_string(self.get_template_string())