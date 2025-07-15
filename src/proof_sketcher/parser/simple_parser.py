"""Simple Lean parser for MVP - extracts basic theorem information."""

import re
from pathlib import Path
from typing import List, Optional

from .models import ParseError, ParseResult, TheoremInfo


class SimpleLeanParser:
    """Minimal parser that extracts theorem names and statements from Lean files."""

    def parse_file(self, file_path: Path) -> ParseResult:
        """Parse a Lean file and extract theorem information.

        Args:
            file_path: Path to the Lean file

        Returns:
            ParseResult with extracted theorems
        """
        if isinstance(file_path, str):
            file_path = Path(file_path)

        # Validate file
        if not file_path.exists():
            return ParseResult(
                success=False,
                errors=[ParseError(message=f"File not found: {file_path}")],
            )

        if file_path.suffix != ".lean":
            return ParseResult(
                success=False,
                errors=[ParseError(message=f"Not a Lean file: {file_path}")],
            )

        try:
            content = file_path.read_text(encoding="utf-8")
            theorems = self._extract_theorems(content)

            return ParseResult(
                success=True, theorems=theorems, file_path=str(file_path)
            )

        except Exception as e:
            return ParseResult(
                success=False,
                errors=[ParseError(message=f"Failed to parse file: {str(e)}")],
            )

    def _extract_theorems(self, content: str) -> List[TheoremInfo]:
        """Extract theorems from Lean content using regex.

        Args:
            content: Lean file content

        Returns:
            List of extracted theorems
        """
        theorems = []

        # Simple regex to find theorem declarations
        # Matches: theorem name (params) : statement := proof
        theorem_pattern = (
            r"theorem\s+(\w+).*?:\s*([^:=]+):=\s*(.*?)(?=\n(?:theorem|lemma|def|end|$))"
        )

        matches = re.finditer(theorem_pattern, content, re.DOTALL | re.MULTILINE)

        for match in matches:
            name = match.group(1)
            statement = match.group(2).strip()
            proof = match.group(3).strip()

            # Clean up the statement
            statement = re.sub(r"\s+", " ", statement)

            # Create theorem info
            theorem = TheoremInfo(
                name=name,
                statement=statement,
                proof=proof if len(proof) < 200 else proof[:200] + "...",
            )
            theorems.append(theorem)

        # Also look for lemmas
        lemma_pattern = (
            r"lemma\s+(\w+).*?:\s*([^:=]+):=\s*(.*?)(?=\n(?:theorem|lemma|def|end|$))"
        )

        matches = re.finditer(lemma_pattern, content, re.DOTALL | re.MULTILINE)

        for match in matches:
            name = match.group(1)
            statement = match.group(2).strip()
            proof = match.group(3).strip()

            # Clean up the statement
            statement = re.sub(r"\s+", " ", statement)

            # Create theorem info
            theorem = TheoremInfo(
                name=name,
                statement=statement,
                proof=proof if len(proof) < 200 else proof[:200] + "...",
            )
            theorems.append(theorem)

        return theorems
