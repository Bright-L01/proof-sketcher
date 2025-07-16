"""Simple Lean parser for MVP - extracts basic theorem information."""

import re
from datetime import datetime
from pathlib import Path
from typing import List, Optional, Union

from .models import FileMetadata, ParseError, ParseResult, TheoremInfo


class SimpleLeanParser:
    """Minimal parser that extracts theorem names and statements from Lean files."""

    def parse_file(self, file_path: Union[Path, str]) -> ParseResult:
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
                errors=[
                    ParseError(
                        message=f"File not found: {file_path}",
                        line_number=None,
                        column=None,
                        error_type="file_not_found",
                        severity="error",
                    )
                ],
                theorems=[],
                metadata=None,
                parse_time_ms=0.0,
            )

        if file_path.suffix != ".lean":
            return ParseResult(
                success=False,
                errors=[
                    ParseError(
                        message=f"Not a Lean file: {file_path}",
                        line_number=None,
                        column=None,
                        error_type="invalid_file_type",
                        severity="error",
                    )
                ],
                theorems=[],
                metadata=None,
                parse_time_ms=0.0,
            )

        try:
            content = file_path.read_text(encoding="utf-8")
            theorems = self._extract_theorems(content)

            # Create file metadata
            stat = file_path.stat()
            metadata = FileMetadata(
                file_path=file_path,
                file_size=stat.st_size,
                last_modified=datetime.fromtimestamp(stat.st_mtime),
                total_lines=len(content.splitlines()),
                imports=[],  # Could be extracted later
                lean_version=None,
            )

            return ParseResult(
                success=True,
                theorems=theorems,
                errors=[],
                metadata=metadata,
                parse_time_ms=0.0,
            )

        except Exception as e:
            return ParseResult(
                success=False,
                errors=[
                    ParseError(
                        message=f"Failed to parse file: {str(e)}",
                        line_number=None,
                        column=None,
                        error_type="parse_exception",
                        severity="error",
                    )
                ],
                theorems=[],
                metadata=None,
                parse_time_ms=0.0,
            )

    def _extract_theorems(self, content: str) -> List[TheoremInfo]:
        """Extract theorems from Lean content using regex.

        Args:
            content: Lean file content

        Returns:
            List of extracted theorems
        """
        theorems = []

        # Extract both theorems and lemmas with better regex patterns
        # Pattern handles: theorem name (params) : statement := by tactics...
        # Use ^ to match at start of line to avoid matching in comments
        patterns = [
            (r"^theorem\s+(\w+)", "theorem"),
            (r"^lemma\s+(\w+)", "lemma"),
        ]

        for pattern_start, _theorem_type in patterns:
            # Find all theorem/lemma declarations at start of line
            for match in re.finditer(pattern_start, content, re.MULTILINE):
                name = match.group(1)
                start_pos = match.start()

                # Find the complete theorem declaration
                theorem_info = self._extract_complete_theorem(content, start_pos, name)
                if theorem_info:
                    theorems.append(theorem_info)

        return theorems

    def _extract_complete_theorem(
        self, content: str, start_pos: int, name: str
    ) -> Optional[TheoremInfo]:
        """Extract complete theorem including statement and proof.

        Args:
            content: Full file content
            start_pos: Start position of theorem/lemma keyword
            name: Name of the theorem

        Returns:
            TheoremInfo if successfully parsed, None otherwise
        """
        # Find the end of this theorem (start of next theorem/lemma/def or end of file)
        end_patterns = [
            r"\ntheorem\s+",
            r"\nlemma\s+",
            r"\ndef\s+",
            r"\nend\s+",
            r"\n\n(?=\w)",  # Double newline followed by word (likely new declaration)
        ]

        end_pos = len(content)
        for pattern in end_patterns:
            match = re.search(pattern, content[start_pos + 1 :])
            if match:
                potential_end = start_pos + 1 + match.start()
                if potential_end < end_pos:
                    end_pos = potential_end

        # Extract the complete theorem text
        theorem_text = content[start_pos:end_pos].strip()

        # Parse statement and proof using more flexible regex
        # Handles patterns like: theorem name (params) : statement := by ... or := proof_term
        pattern = r"(?:theorem|lemma)\s+\w+(?:\s*\([^)]*\))?\s*:\s*([^:]+?)\s*:=\s*(.*)"
        match = re.search(pattern, theorem_text, re.DOTALL)

        if not match:
            return None

        statement = match.group(1).strip()
        proof = match.group(2).strip()

        # Clean up statement (remove extra whitespace)
        statement = re.sub(r"\s+", " ", statement)

        # Truncate very long proofs for readability
        if len(proof) > 300:
            proof = proof[:300] + "..."

        return TheoremInfo(
            name=name,
            statement=statement,
            proof=proof,
            dependencies=[],
            line_number=None,
            docstring=None,
            namespace=None,
            visibility="public",
            tactics=[],
            is_axiom=False,
            file_path=None,
            start_line=None,
            end_line=None,
        )
