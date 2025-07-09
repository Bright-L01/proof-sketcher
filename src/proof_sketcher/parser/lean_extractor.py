"""
Lean 4 Extractor Integration

This module provides a Python interface to the Lean 4 theorem extractor.
It handles building and running the Lean extractor program to extract
theorem information from Lean files.
"""

import json
import logging
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Union

from ..core.exceptions import ParserError
from ..utils.security import validate_file_path, validate_theorem_name
from .models import TheoremInfo


class LeanExtractorError(ParserError):
    """Errors related to Lean extractor execution."""

    pass


class LeanExtractor:
    """Extract theorem information using Lean 4 program."""

    def __init__(
        self, extractor_path: Optional[Path] = None, lean_executable: str = "lean"
    ):
        """Initialize the Lean extractor.

        Args:
            extractor_path: Path to the built extractor executable
            lean_executable: Path to lean executable
        """
        self.lean_executable = lean_executable
        self.extractor = extractor_path or self._find_extractor()
        self.logger = logging.getLogger(__name__)

        # Try to build extractor if it doesn't exist
        if not self.extractor or not self.extractor.exists():
            self._try_build_extractor()

    def _find_extractor(self) -> Optional[Path]:
        """Find the built extractor executable."""
        # Look in several possible locations
        possible_paths = [
            Path(__file__).parent
            / "../../.."
            / "lean_extractor"
            / ".lake"
            / "build"
            / "bin"
            / "extract",
            Path(__file__).parent / "ExtractTheorem",
            Path(__file__).parent / ".lake" / "build" / "bin" / "extract",
            Path.cwd() / "lean_extractor" / ".lake" / "build" / "bin" / "extract",
        ]

        for path in possible_paths:
            if path.exists():
                return path.resolve()

        return None

    def _try_build_extractor(self) -> None:
        """Try to build the Lean extractor if source is available."""
        # Look for lean extractor source
        lean_source_dirs = [
            Path(__file__).parent / "../../.." / "lean_extractor",
            Path.cwd() / "lean_extractor",
        ]

        for source_dir in lean_source_dirs:
            if source_dir.exists() and (source_dir / "lakefile.lean").exists():
                try:
                    self.logger.info(f"Building Lean extractor in {source_dir}")
                    result = subprocess.run(
                        ["lake", "build"],
                        cwd=source_dir,
                        capture_output=True,
                        text=True,
                        timeout=300,  # 5 minutes timeout
                    )

                    if result.returncode == 0:
                        self.extractor = (
                            source_dir / ".lake" / "build" / "bin" / "extract"
                        )
                        if self.extractor.exists():
                            self.logger.info("Successfully built Lean extractor")
                            return
                    else:
                        self.logger.warning(
                            f"Failed to build extractor: {
                                result.stderr}"
                        )

                except (subprocess.SubprocessError, subprocess.TimeoutExpired) as e:
                    self.logger.warning(f"Error building extractor: {e}")
                    continue

        # If we can't build, try to use the Lean script directly
        lean_script = Path(__file__).parent / "ExtractTheorem.lean"
        if lean_script.exists():
            self.extractor = lean_script
            self.logger.info("Using Lean script directly")

    def extract_file(
        self, lean_file: Path, base_dir: Optional[Path] = None
    ) -> List[Dict]:
        """Extract all theorems from a Lean file.

        Args:
            lean_file: Path to the Lean file
            base_dir: Base directory for security validation

        Returns:
            List of theorem dictionaries

        Raises:
            LeanExtractorError: If extraction fails
        """
        # Validate file path for security
        if base_dir:
            try:
                validate_file_path(lean_file, base_dir)
            except Exception as e:
                raise LeanExtractorError(f"File validation failed: {e}")

        if not lean_file.exists():
            raise LeanExtractorError(f"Lean file not found: {lean_file}")

        if not self.extractor:
            raise LeanExtractorError(
                "Lean extractor not available. Please build it first."
            )

        try:
            # Use the extractor to extract all theorems
            if self.extractor.suffix == ".lean":
                # Run Lean script directly
                cmd = [
                    self.lean_executable,
                    str(self.extractor),
                    "--",
                    "--file",
                    str(lean_file),
                    "--all",
                ]
            else:
                # Run built executable
                cmd = [str(self.extractor), "--file", str(lean_file), "--all"]

            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=60,  # 1 minute timeout
                cwd=lean_file.parent,
            )

            if result.returncode != 0:
                error_msg = result.stderr.strip() or "Unknown error"
                raise LeanExtractorError(f"Extractor failed: {error_msg}")

            # Parse JSON output
            try:
                return json.loads(result.stdout)
            except json.JSONDecodeError as e:
                # Try to extract JSON from mixed output
                lines = result.stdout.strip().split("\n")
                for line in lines:
                    try:
                        return json.loads(line)
                    except json.JSONDecodeError:
                        continue
                raise LeanExtractorError(f"Failed to parse JSON output: {e}")

        except subprocess.TimeoutExpired:
            raise LeanExtractorError("Extractor timed out")
        except subprocess.SubprocessError as e:
            raise LeanExtractorError(f"Failed to run extractor: {e}")

    def extract_theorem(
        self, lean_file: Path, theorem_name: str, base_dir: Optional[Path] = None
    ) -> Optional[Dict]:
        """Extract specific theorem from a Lean file.

        Args:
            lean_file: Path to the Lean file
            theorem_name: Name of the theorem to extract
            base_dir: Base directory for security validation

        Returns:
            Theorem dictionary or None if not found

        Raises:
            LeanExtractorError: If extraction fails
        """
        # Validate inputs
        if base_dir:
            try:
                validate_file_path(lean_file, base_dir)
            except Exception as e:
                raise LeanExtractorError(f"File validation failed: {e}")

        try:
            validate_theorem_name(theorem_name)
        except Exception as e:
            raise LeanExtractorError(f"Invalid theorem name: {e}")

        if not lean_file.exists():
            raise LeanExtractorError(f"Lean file not found: {lean_file}")

        if not self.extractor:
            raise LeanExtractorError("Lean extractor not available")

        try:
            # Use the extractor for specific theorem
            if self.extractor.suffix == ".lean":
                # Run Lean script directly
                cmd = [
                    self.lean_executable,
                    str(self.extractor),
                    "--",
                    "--file",
                    str(lean_file),
                    "--theorem",
                    theorem_name,
                ]
            else:
                # Run built executable
                cmd = [
                    str(self.extractor),
                    "--file",
                    str(lean_file),
                    "--theorem",
                    theorem_name,
                ]

            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=60, cwd=lean_file.parent
            )

            if result.returncode != 0:
                # Check if it's a "not found" error vs other errors
                error_msg = result.stderr.strip()
                if "not found" in error_msg.lower():
                    return None  # Theorem doesn't exist
                raise LeanExtractorError(f"Extractor failed: {error_msg}")

            # Parse JSON output
            try:
                return json.loads(result.stdout)
            except json.JSONDecodeError as e:
                # Try to extract JSON from mixed output
                lines = result.stdout.strip().split("\n")
                for line in lines:
                    try:
                        return json.loads(line)
                    except json.JSONDecodeError:
                        continue
                raise LeanExtractorError(f"Failed to parse JSON output: {e}")

        except subprocess.TimeoutExpired:
            raise LeanExtractorError("Extractor timed out")
        except subprocess.SubprocessError as e:
            raise LeanExtractorError(f"Failed to run extractor: {e}")

    def extract_to_theorem_info(
        self, lean_file: Path, theorem_name: str, base_dir: Optional[Path] = None
    ) -> Optional[TheoremInfo]:
        """Extract theorem and convert to TheoremInfo model.

        Args:
            lean_file: Path to the Lean file
            theorem_name: Name of the theorem to extract
            base_dir: Base directory for security validation

        Returns:
            TheoremInfo object or None if not found
        """
        theorem_data = self.extract_theorem(lean_file, theorem_name, base_dir)
        if not theorem_data:
            return None

        # Convert to TheoremInfo model
        return TheoremInfo(
            name=theorem_data.get("name", theorem_name),
            statement=theorem_data.get("statement", theorem_data.get("type", "")),
            proof=theorem_data.get("value"),
            dependencies=theorem_data.get("dependencies", []),
            line_number=theorem_data.get("lineNumber"),
            docstring=theorem_data.get("docString"),
            tactics=theorem_data.get("tactics", []),
            is_axiom=theorem_data.get("isAxiom", False),
        )

    def is_available(self) -> bool:
        """Check if the extractor is available and working.

        Returns:
            True if extractor can be used, False otherwise
        """
        if not self.extractor:
            return False

        try:
            # Test with a simple temporary file
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".lean", delete=False
            ) as f:
                f.write("theorem test : True := trivial\n")
                temp_file = Path(f.name)

            try:
                result = self.extract_theorem(temp_file, "test")
                return result is not None
            finally:
                temp_file.unlink()  # Clean up

        except Exception:
            return False

    def get_version_info(self) -> Dict[str, str]:
        """Get version information about the extractor and Lean.

        Returns:
            Dictionary with version information
        """
        info = {
            "extractor_path": str(self.extractor) if self.extractor else "Not found",
            "extractor_available": self.is_available(),
        }

        # Get Lean version
        try:
            result = subprocess.run(
                [self.lean_executable, "--version"],
                capture_output=True,
                text=True,
                timeout=10,
            )
            if result.returncode == 0:
                info["lean_version"] = result.stdout.strip()
            else:
                info["lean_version"] = "Unknown"
        except Exception:
            info["lean_version"] = "Not available"

        return info


# Global instance for reuse
_global_extractor: Optional[LeanExtractor] = None


def get_lean_extractor() -> LeanExtractor:
    """Get a global instance of the Lean extractor.

    Returns:
        LeanExtractor instance
    """
    global _global_extractor
    if _global_extractor is None:
        _global_extractor = LeanExtractor()
    return _global_extractor
