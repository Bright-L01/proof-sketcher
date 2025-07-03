"""Lean AST extraction using subprocess calls to Lean compiler."""

import json
import logging
import re
import subprocess
import time
from datetime import datetime
from pathlib import Path
from typing import List, Optional, Tuple

from ..core.exceptions import (
    ConfigValidationError,
    LeanTimeoutError,
    ParserError,
)
from ..core.interfaces import IParser
from .config import ParserConfig
from .models import FileMetadata, ParseError, ParseResult, TheoremInfo
from .enhanced_parser import EnhancedLeanParser


class LeanParser(IParser):
    """Parser for extracting theorem information from Lean files."""

    def __init__(self, config: Optional[ParserConfig] = None) -> None:
        """Initialize the Lean parser.

        Args:
            config: Parser configuration. Uses default if None.
        """
        self.config = config or ParserConfig.default()
        self.logger = logging.getLogger(__name__)
        self.extractor_path = Path(__file__).parent / "ExtractTheorem.lean"
        self.enhanced_parser = EnhancedLeanParser()

        # Validate configuration
        config_errors = self.config.validate()
        if config_errors:
            raise ConfigValidationError(
                message=f"Invalid parser configuration: {', '.join(config_errors)}",
                details={"errors": config_errors},
                error_code="parser_config_invalid",
            )

    def parse_file(self, file_path: Path) -> ParseResult:
        """Parse a Lean file and extract all theorem information.

        Args:
            file_path: Path to the Lean file to parse

        Returns:
            ParseResult containing theorems, errors, and metadata
        """
        start_time = time.time()

        try:
            # Validate file exists and is readable
            if not file_path.exists():
                return ParseResult(
                    success=False,
                    errors=[ParseError(message=f"File not found: {file_path}")],
                )

            if not file_path.suffix == ".lean":
                return ParseResult(
                    success=False,
                    errors=[
                        ParseError(message=f"File is not a Lean file: {file_path}")
                    ],
                )

            # Read file content for metadata and fallback parsing
            content = file_path.read_text(encoding="utf-8")
            metadata = self._create_metadata(file_path, content)

            # Detect and setup Lake project if needed
            lake_setup_errors = []
            if self.config.auto_detect_lake:
                lake_errors = self._setup_lake_project(file_path)
                lake_setup_errors.extend(lake_errors)

            # Extract theorems using enhanced parser first
            enhanced_declarations = self.enhanced_parser.parse_content_enhanced(content)
            enhanced_theorems = self.enhanced_parser.get_theorems_for_proof_sketcher(enhanced_declarations)
            
            # Fall back to basic parsing if enhanced parsing fails or returns no results
            basic_theorems = []
            if not enhanced_theorems:
                basic_theorems = self._extract_theorems_basic(content)

            # Enhance with Lean extractor if available and we have theorems
            extraction_errors = []
            final_theorems = enhanced_theorems or basic_theorems
            
            if final_theorems and self._can_use_lean_extractor():
                lean_enhanced_theorems, extraction_errors = (
                    self._extract_all_theorems_with_lean(file_path, final_theorems)
                )
                if lean_enhanced_theorems:
                    final_theorems = lean_enhanced_theorems

            # Combine all errors
            all_errors = lake_setup_errors + extraction_errors

            parse_time = (time.time() - start_time) * 1000

            return ParseResult(
                theorems=final_theorems,
                errors=all_errors,
                metadata=metadata,
                parse_time_ms=parse_time,
                success=True,
            )

        except Exception as e:
            self.logger.exception(f"Failed to parse file {file_path}")
            parser_error = ParserError(
                message=f"Parsing failed: {str(e)}",
                details={"file_path": str(file_path)},
                error_code="parse_failed",
            )
            return ParseResult(
                success=False,
                errors=[ParseError.from_exception(parser_error)],
                parse_time_ms=(time.time() - start_time) * 1000,
            )

    def parse_theorem(
        self, file_path: Path, theorem_name: str
    ) -> Optional[TheoremInfo]:
        """Extract information for a single theorem using Lean extractor.

        Args:
            file_path: Path to the Lean file
            theorem_name: Name of the theorem to extract

        Returns:
            TheoremInfo if successful, None otherwise
        """
        if not self._can_use_lean_extractor():
            self.logger.warning(
                "Cannot use Lean extractor, falling back to basic parsing"
            )
            # Fall back to basic parsing for single theorem
            content = file_path.read_text(encoding="utf-8")
            basic_theorems = self._extract_theorems_basic(content)
            for theorem in basic_theorems:
                if theorem.name == theorem_name:
                    return theorem
            return None

        # Setup Lake project if needed
        if self.config.auto_detect_lake:
            self._setup_lake_project(file_path)

        # Extract using Lean with retry logic
        for attempt in range(self.config.retry_config.max_attempts):
            try:
                theorem_info = self._extract_single_theorem_with_lean(
                    file_path, theorem_name
                )
                if theorem_info:
                    return theorem_info

            except subprocess.TimeoutExpired:
                if attempt < self.config.retry_config.max_attempts - 1:
                    delay = self.config.retry_config.get_delay(attempt)
                    self.logger.warning(
                        f"Timeout extracting {theorem_name}, retrying in {delay}s..."
                    )
                    time.sleep(delay)
                else:
                    self.logger.error(f"Final timeout extracting {theorem_name}")
                    raise LeanTimeoutError(
                        message=f"Lean extraction timed out for theorem {theorem_name}",
                        details={
                            "theorem": theorem_name,
                            "file_path": str(file_path),
                            "timeout": self.config.lean_timeout,
                            "attempts": self.config.retry_config.max_attempts,
                        },
                        error_code="lean_timeout",
                    ) from None

            except Exception as e:
                if attempt < self.config.retry_config.max_attempts - 1:
                    delay = self.config.retry_config.get_delay(attempt)
                    self.logger.warning(
                        f"Error extracting {theorem_name}: {e}, retrying in {delay}s..."
                    )
                    time.sleep(delay)
                else:
                    self.logger.error(f"Final error extracting {theorem_name}: {e}")

        return None

    def validate_lean_setup(self) -> bool:
        """Validate that Lean and Lake are properly set up.

        Returns:
            True if setup is valid, False otherwise
        """
        try:
            # Check Lean executable
            if not self.check_lean_available():
                self.logger.error(
                    f"Lean executable not found: {self.config.lean_executable}"
                )
                return False

            # Check Lake executable if auto-detection is enabled
            if self.config.auto_detect_lake and not self.check_lake_available():
                self.logger.warning(
                    f"Lake executable not found: {self.config.lake_executable}"
                )
                # This is a warning, not an error, as Lake is optional

            # Check extractor script
            if not self.extractor_path.exists():
                self.logger.error(
                    f"Lean extractor script not found: {self.extractor_path}"
                )
                return False

            # Test basic Lean functionality
            try:
                result = subprocess.run(
                    [self.config.lean_executable, "--version"],
                    capture_output=True,
                    text=True,
                    timeout=self.config.version_check_timeout,
                )

                if result.returncode != 0:
                    self.logger.error(f"Lean version check failed: {result.stderr}")
                    return False

                self.logger.info(f"Lean version: {result.stdout.strip()}")

            except subprocess.TimeoutExpired:
                self.logger.error("Lean version check timed out")
                return False

            return True

        except Exception as e:
            self.logger.error(f"Setup validation failed: {e}")
            return False

    def _can_use_lean_extractor(self) -> bool:
        """Check if Lean extractor can be used."""
        return self.check_lean_available() and self.extractor_path.exists()

    def _setup_lake_project(self, file_path: Path) -> List[ParseError]:
        """Setup Lake project if one is detected.

        Args:
            file_path: Path to the Lean file

        Returns:
            List of errors encountered during setup
        """
        errors = []

        try:
            # Look for lakefile.lean in current directory and parents
            current_dir = file_path.parent
            lakefile_path = None

            for parent in [current_dir] + list(current_dir.parents):
                potential_lakefile = parent / "lakefile.lean"
                if potential_lakefile.exists():
                    lakefile_path = potential_lakefile
                    break

            if not lakefile_path:
                self.logger.debug("No Lake project detected")
                return errors

            self.logger.info(f"Lake project detected at {lakefile_path.parent}")

            # Check if Lake is available
            if not self.check_lake_available():
                errors.append(
                    ParseError(
                        message=f"Lake project detected but Lake executable not available: {self.config.lake_executable}",
                        error_type="lake_error",
                        severity="warning",
                    )
                )
                return errors

            # Build project if configured to do so
            if self.config.lake_build_on_parse:
                self.logger.info("Building Lake project...")

                try:
                    result = subprocess.run(
                        [self.config.lake_executable, "build"],
                        cwd=lakefile_path.parent,
                        capture_output=True,
                        text=True,
                        timeout=self.config.lake_timeout,
                    )

                    if result.returncode != 0:
                        errors.append(
                            ParseError(
                                message=f"Lake build failed: {result.stderr}",
                                error_type="lake_build_error",
                                severity="warning",
                            )
                        )
                    else:
                        self.logger.info("Lake build completed successfully")

                except subprocess.TimeoutExpired:
                    errors.append(
                        ParseError(
                            message="Lake build timed out",
                            error_type="lake_timeout",
                            severity="warning",
                        )
                    )

        except Exception as e:
            errors.append(
                ParseError(
                    message=f"Lake setup failed: {e}",
                    error_type="lake_setup_error",
                    severity="warning",
                )
            )

        return errors

    def _extract_all_theorems_with_lean(
        self, file_path: Path, basic_theorems: List[TheoremInfo]
    ) -> Tuple[List[TheoremInfo], List[ParseError]]:
        """Extract all theorems using Lean extractor with retry logic.

        Args:
            file_path: Path to the Lean file
            basic_theorems: Basic theorems from regex parsing

        Returns:
            Tuple of (enhanced_theorems, errors)
        """
        enhanced_theorems = []
        errors = []

        for basic_theorem in basic_theorems:
            enhanced = None

            # Try to enhance with Lean extractor
            for attempt in range(self.config.retry_config.max_attempts):
                try:
                    enhanced = self._extract_single_theorem_with_lean(
                        file_path, basic_theorem.name
                    )
                    if enhanced:
                        # Preserve some info from basic parsing
                        enhanced.line_number = basic_theorem.line_number
                        enhanced.proof = basic_theorem.proof
                        break

                except subprocess.TimeoutExpired:
                    if attempt < self.config.retry_config.max_attempts - 1:
                        delay = self.config.retry_config.get_delay(attempt)
                        time.sleep(delay)
                    else:
                        errors.append(
                            ParseError(
                                message=f"Timeout extracting {basic_theorem.name}",
                                error_type="lean_timeout",
                            )
                        )

                except Exception as e:
                    if attempt < self.config.retry_config.max_attempts - 1:
                        delay = self.config.retry_config.get_delay(attempt)
                        time.sleep(delay)
                    else:
                        errors.append(
                            ParseError(
                                message=f"Failed to extract {basic_theorem.name}: {e}",
                                error_type="lean_extraction_error",
                            )
                        )

            # Use enhanced if available, otherwise basic
            enhanced_theorems.append(enhanced if enhanced else basic_theorem)

        return enhanced_theorems, errors

    def _extract_single_theorem_with_lean(
        self, file_path: Path, theorem_name: str
    ) -> Optional[TheoremInfo]:
        """Extract single theorem using Lean extractor."""
        working_dir = self.config.working_dir or file_path.parent

        # Check if we're in a Lake project
        lake_project = self._find_lake_project(file_path)

        if lake_project and self.check_lake_available():
            # Use lake env to run with proper imports
            result = subprocess.run(
                [
                    self.config.lake_executable,
                    "env",
                    self.config.lean_executable,
                    str(self.extractor_path),
                    "--",
                    "--file",
                    str(file_path),
                    "--theorem",
                    theorem_name,
                ],
                cwd=lake_project,
                capture_output=True,
                text=True,
                timeout=self.config.lean_timeout,
            )
        else:
            # Run directly
            result = subprocess.run(
                [
                    self.config.lean_executable,
                    str(self.extractor_path),
                    "--",
                    "--file",
                    str(file_path),
                    "--theorem",
                    theorem_name,
                ],
                cwd=working_dir,
                capture_output=True,
                text=True,
                timeout=self.config.lean_timeout,
            )

        if result.returncode == 0 and result.stdout.strip():
            try:
                json_output = json.loads(result.stdout.strip())

                # Check if we got valid theorem data
                if json_output.get("name") and json_output.get("type"):
                    return TheoremInfo(
                        name=json_output["name"],
                        statement=json_output["type"],
                        dependencies=json_output.get("dependencies", []),
                        docstring=json_output.get("docString"),
                        visibility="public",
                        tactics=json_output.get("tactics", []),
                        proof=json_output.get("value", ""),
                    )
                else:
                    self.logger.warning(
                        f"Incomplete theorem data for {theorem_name}: {json_output}"
                    )
            except json.JSONDecodeError as e:
                self.logger.warning(
                    f"Failed to parse JSON output for {theorem_name}: {e}"
                )

        return None

    def _create_metadata(self, file_path: Path, content: str) -> FileMetadata:
        """Create metadata for the parsed file."""
        stat = file_path.stat()
        imports = self._extract_imports(content)

        return FileMetadata(
            file_path=file_path,
            file_size=stat.st_size,
            last_modified=datetime.fromtimestamp(stat.st_mtime),
            imports=imports,
            total_lines=len(content.splitlines()),
        )

    def _find_lake_project(self, file_path: Path) -> Optional[Path]:
        """Find the Lake project root for a given file."""
        current = file_path.parent
        while current != current.parent:
            if (current / "lakefile.lean").exists():
                return current
            current = current.parent
        return None

    def _extract_imports(self, content: str) -> List[str]:
        """Extract import statements from Lean content."""
        imports = []
        for line in content.splitlines():
            line = line.strip()
            if line.startswith("import "):
                import_name = line[7:].strip()
                imports.append(import_name)
        return imports

    def _extract_theorems_basic(self, content: str) -> List[TheoremInfo]:
        """Basic theorem extraction using regex patterns (fallback)."""
        theorems = []
        lines = content.splitlines()

        theorem_pattern = re.compile(r"^(theorem|lemma)\s+(\w+)(?:\s*[:\(]|$)")

        for line_num, line in enumerate(lines, 1):
            line = line.strip()

            if not line or line.startswith("--"):
                continue

            match = theorem_pattern.match(line)
            if match:
                theorem_name = match.group(2)
                statement = self._extract_statement(lines, line_num - 1)
                proof = self._extract_proof(lines, line_num - 1)

                theorem = TheoremInfo(
                    name=theorem_name,
                    statement=statement,
                    proof=proof,
                    line_number=line_num,
                    visibility="public",
                )

                theorems.append(theorem)

        return theorems

    def _extract_statement(self, lines: List[str], start_line: int) -> str:
        """Extract theorem statement from lines starting at given position."""
        statement_parts = []
        current_line = start_line

        while current_line < len(lines):
            line = lines[current_line].strip()

            if current_line == start_line:
                # Extract everything after theorem declaration
                # Look for the main type annotation colon (after parameters)
                match = re.match(r"^(theorem|lemma)\s+(\w+)\s*(.*)$", line)
                if match:
                    rest = match.group(3).strip()

                    # If there are parameters, include them in the statement
                    if rest.startswith("("):
                        paren_count = 0
                        idx = 0
                        for i, char in enumerate(rest):
                            if char == "(":
                                paren_count += 1
                            elif char == ")":
                                paren_count -= 1
                                if paren_count == 0:
                                    idx = i + 1
                                    break

                        # Include parameters and everything after the type annotation colon
                        params = rest[:idx].strip()
                        after_params = rest[idx:].strip()
                        if after_params.startswith(":"):
                            # Include parameters in statement
                            line = params + " : " + after_params[1:].strip()
                        else:
                            line = rest
                    elif ":" in rest:
                        # No parameters, just split on first colon
                        line = rest.split(":", 1)[1].strip()
                    else:
                        line = rest

            statement_parts.append(line)

            if ":=" in line:
                statement_parts[-1] = line.split(":=", 1)[0].strip()
                break

            current_line += 1

            if current_line - start_line > 20:
                break

        return " ".join(statement_parts).strip()

    def _extract_proof(self, lines: List[str], start_line: int) -> Optional[str]:
        """Extract proof body if available."""
        proof_parts = []
        current_line = start_line
        found_proof_start = False
        brace_count = 0

        while current_line < len(lines):
            line = lines[current_line].strip()

            if ":=" in line and not found_proof_start:
                found_proof_start = True
                proof_start = line.split(":=", 1)[1].strip()
                if proof_start:
                    proof_parts.append(proof_start)
                    brace_count += proof_start.count("{") - proof_start.count("}")
            elif found_proof_start:
                proof_parts.append(line)
                brace_count += line.count("{") - line.count("}")

                if brace_count <= 0 and (
                    not line or line.startswith(("theorem", "lemma"))
                ):
                    if not line:
                        proof_parts.pop()
                    break

            current_line += 1

            if current_line - start_line > 50:
                break

        if proof_parts:
            return " ".join(proof_parts).strip()
        return None

    def check_lean_available(self) -> bool:
        """Check if Lean executable is available."""
        try:
            result = subprocess.run(
                [self.config.lean_executable, "--version"],
                capture_output=True,
                text=True,
                timeout=self.config.version_check_timeout,
            )
            return result.returncode == 0
        except (subprocess.SubprocessError, FileNotFoundError):
            return False

    def check_lake_available(self) -> bool:
        """Check if Lake executable is available."""
        try:
            result = subprocess.run(
                [self.config.lake_executable, "--version"],
                capture_output=True,
                text=True,
                timeout=self.config.version_check_timeout,
            )
            return result.returncode == 0
        except (subprocess.SubprocessError, FileNotFoundError):
            return False

    def get_lean_version(self) -> Optional[str]:
        """Get the version of the Lean executable."""
        try:
            result = subprocess.run(
                [self.config.lean_executable, "--version"],
                capture_output=True,
                text=True,
                timeout=self.config.version_check_timeout,
            )
            if result.returncode == 0:
                return result.stdout.strip()
        except (subprocess.SubprocessError, FileNotFoundError):
            pass
        return None

    def get_lake_version(self) -> Optional[str]:
        """Get the version of the Lake executable."""
        try:
            result = subprocess.run(
                [self.config.lake_executable, "--version"],
                capture_output=True,
                text=True,
                timeout=self.config.version_check_timeout,
            )
            if result.returncode == 0:
                return result.stdout.strip()
        except (subprocess.SubprocessError, FileNotFoundError):
            pass
        return None
    
    def parse_file_enhanced(self, file_path: Path) -> dict:
        """Parse a Lean file and extract all language constructs using enhanced parser.
        
        Returns:
            Dictionary mapping construct types to lists of declarations
        """
        try:
            return self.enhanced_parser.parse_file_enhanced(file_path)
        except Exception as e:
            self.logger.error(f"Enhanced parsing failed for {file_path}: {e}")
            return {}
    
    def get_supported_constructs(self) -> List[str]:
        """Get list of supported Lean 4 constructs.
        
        Returns:
            List of supported construct names
        """
        from .enhanced_parser import LeanConstruct
        return [construct.value for construct in LeanConstruct]
    
    def get_parsing_statistics(self, file_path: Path) -> dict:
        """Get detailed parsing statistics for a file.
        
        Returns:
            Dictionary with parsing statistics and construct counts
        """
        try:
            declarations = self.parse_file_enhanced(file_path)
            
            stats = {
                "total_constructs": 0,
                "construct_counts": {},
                "parsing_method": "enhanced"
            }
            
            for construct_type, construct_list in declarations.items():
                count = len(construct_list)
                stats["construct_counts"][construct_type] = count
                stats["total_constructs"] += count
            
            # Also get basic theorem count for comparison
            basic_result = self.parse_file(file_path)
            stats["theorem_count_basic"] = len(basic_result.theorems)
            stats["theorem_count_enhanced"] = stats["construct_counts"].get("theorem", 0) + stats["construct_counts"].get("lemma", 0)
            
            return stats
            
        except Exception as e:
            self.logger.error(f"Failed to get parsing statistics for {file_path}: {e}")
            return {"error": str(e)}
