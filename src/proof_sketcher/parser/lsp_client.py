"""Lean 4 LSP client for semantic analysis of theorems and proofs.

DEPRECATED: This LSP client is non-functional and has been deprecated.
Performance testing showed it is 1000x slower than the simple parser and
extracts 0 theorems. DO NOT USE THIS MODULE.

Use SimpleLeanParser instead for all parsing needs.

This module was intended to provide LSP-based semantic analysis but has
proven to be broken and unusable. It is kept in the codebase only for
historical reference and potential future fixes.

Known issues:
- Extracts 0 theorems from any file
- 1000x slower than simple regex parser
- LSP communication appears to be broken
- No working implementation found

Original intended features (non-functional):
- Full Lean 4 LSP integration
- Semantic analysis of proof steps
- Tactic sequence extraction
- Proof state evolution tracking
- Dependency analysis
- Mathematical context detection
- Progressive difficulty assessment
"""

from __future__ import annotations

import asyncio
import json
import logging
import os
import shlex
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Any

from pydantic import BaseModel, Field

from ..core.error_handling import error_context, setup_error_logger
from ..core.exceptions import FileParseError, LSPConnectionError, LSPTimeoutError
from ..core.resource_limits import (
    RateLimiter,
    ResourceMonitor,
    TimeoutError,
    async_timeout,
)
from .models import FileMetadata, ParseError, ParseResult, TheoremInfo


class ProofState(BaseModel):
    """Represents a proof state at a specific point in the proof."""

    goals: list[str] = Field(default_factory=list)
    hypotheses: list[str] = Field(default_factory=list)
    tactic_applied: str | None = None
    line_number: int | None = None
    column: int | None = None


class TacticInfo(BaseModel):
    """Information about a specific tactic application."""

    name: str
    arguments: list[str] = Field(default_factory=list)
    line_number: int
    column: int
    before_state: ProofState | None = None
    after_state: ProofState | None = None
    error_message: str | None = None


class SemanticTheoremInfo(TheoremInfo):
    """Enhanced theorem info with semantic analysis from LSP."""

    # Semantic analysis fields
    proof_states: list[ProofState] = Field(default_factory=list)
    tactic_sequence: list[TacticInfo] = Field(default_factory=list)
    semantic_dependencies: list[str] = Field(default_factory=list)
    mathematical_entities: list[str] = Field(default_factory=list)
    complexity_score: float = Field(default=0.0)
    proof_method: str = Field(default="unknown")

    # LSP-specific metadata
    definition_location: tuple[int, int] | None = None
    type_signature: str | None = None
    hover_info: str | None = None


class LeanLSPClient:
    """Lean 4 Language Server Protocol client for semantic analysis."""

    def __init__(
        self,
        lean_executable: str = "lean",
        timeout: float = 30.0,
        max_memory_mb: int = 500,
        rate_limit_calls: int = 100,
        rate_limit_window: float = 60.0,
    ):
        """Initialize the LSP client.

        DEPRECATED: This LSP client is non-functional. Use SimpleLeanParser instead.

        Args:
            lean_executable: Path to Lean 4 executable
            timeout: Timeout for LSP operations in seconds
            max_memory_mb: Maximum memory usage in MB
            rate_limit_calls: Maximum LSP calls allowed
            rate_limit_window: Time window for rate limiting (seconds)
        """
        import warnings

        warnings.warn(
            "LeanLSPClient is deprecated and non-functional. "
            "It extracts 0 theorems and is 1000x slower than SimpleLeanParser. "
            "Use SimpleLeanParser instead.",
            DeprecationWarning,
            stacklevel=2,
        )

        # Validate and sanitize the executable path
        self.lean_executable = self._validate_executable(lean_executable)
        self.timeout = timeout
        self.logger = setup_error_logger(__name__)
        self._process: subprocess.Popen | None = None
        self._request_id = 0

        # Resource limits
        self.resource_monitor = ResourceMonitor(max_memory_mb=max_memory_mb)
        self.rate_limiter = RateLimiter(
            max_calls=rate_limit_calls, time_window=rate_limit_window
        )

    def _validate_executable(self, executable_path: str) -> str:
        """Validate and sanitize the executable path for security.

        Args:
            executable_path: Path to the executable

        Returns:
            Validated and sanitized executable path

        Raises:
            ValueError: If the executable path is invalid or insecure
        """
        # Validate against shell injection characters first
        if any(
            char in executable_path
            for char in [
                ";",
                "&",
                "|",
                "`",
                "$",
                "(",
                ")",
                "<",
                ">",
                "\n",
                "\r",
                '"',
                "'",
            ]
        ):
            raise ValueError(
                f"Invalid characters in executable path: {executable_path}"
            )

        # Check if it's a simple command name (no path separators)
        if (
            os.sep not in executable_path
            and "/" not in executable_path
            and "\\" not in executable_path
        ):
            # It's just a command name like "lean", check if it's allowed
            allowed_commands = ["lean", "lean4", "lean.exe", "lean4.exe"]
            if executable_path not in allowed_commands:
                raise ValueError(
                    f"Command must be one of {allowed_commands}, got: {executable_path}"
                )

            # Try to find it in PATH
            import shutil

            full_path = shutil.which(executable_path)
            if not full_path:
                raise ValueError(f"Executable '{executable_path}' not found in PATH")

            # Use the full path for additional validation
            path = Path(full_path).resolve()
        else:
            # It's a path, validate it
            path = Path(executable_path).resolve()

            # Security checks
            if not path.exists():
                raise ValueError(f"Executable not found: {executable_path}")

            if not path.is_file():
                raise ValueError(f"Executable path is not a file: {executable_path}")

            # Check if executable
            if not os.access(str(path), os.X_OK):
                raise ValueError(f"File is not executable: {executable_path}")

            # Only allow specific executable names for Lean
            allowed_names = ["lean", "lean4", "lean.exe", "lean4.exe"]
            if path.name not in allowed_names:
                raise ValueError(
                    f"Executable must be one of {allowed_names}, got: {path.name}"
                )

        # Return the validated path as string
        return str(path)

    async def parse_file(self, file_path: Path | str) -> ParseResult:
        """Parse a Lean file using LSP for semantic analysis.

        Args:
            file_path: Path to the Lean file

        Returns:
            ParseResult with semantically analyzed theorems
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
            import time

            start_time = time.time()

            # Apply rate limiting
            await self.rate_limiter.acquire()

            # Monitor resources during LSP operations
            async def lsp_operations():
                # Start LSP server and analyze file
                await self._start_lsp_server()

                # Initialize the file with LSP
                await self._initialize_file(file_path)

                # Extract theorem information using LSP
                return await self._extract_theorems_semantic(file_path)

            # Run with timeout and resource monitoring
            try:
                theorems = await self.resource_monitor.monitor_async(
                    async_timeout(lsp_operations(), self.timeout)
                )
            except asyncio.TimeoutError:
                raise LSPTimeoutError(
                    f"LSP parsing timed out after {self.timeout} seconds"
                )

            end_time = time.time()
            parse_time_ms = (end_time - start_time) * 1000

            # Create file metadata
            stat = file_path.stat()
            content = file_path.read_text(encoding="utf-8")
            metadata = FileMetadata(
                file_path=file_path,
                file_size=stat.st_size,
                last_modified=datetime.fromtimestamp(stat.st_mtime),
                total_lines=len(content.splitlines()),
                imports=[],  # Could be extracted from LSP
                lean_version=await self._get_lean_version(),
            )

            return ParseResult(
                success=True,
                theorems=theorems,
                errors=[],
                metadata=metadata,
                parse_time_ms=parse_time_ms,
            )

        except (LSPTimeoutError, LSPConnectionError, FileParseError) as e:
            # Handle our custom exceptions
            self.logger.error(
                f"LSP parsing failed: {e}", extra={"details": getattr(e, "details", {})}
            )
            return ParseResult(
                success=False,
                errors=[
                    ParseError(
                        message=str(e),
                        line_number=None,
                        column=None,
                        error_type=type(e).__name__,
                        severity="error",
                    )
                ],
                theorems=[],
                metadata=None,
                parse_time_ms=0.0,
            )
        except Exception as e:
            # Handle unexpected exceptions
            self.logger.error(
                f"Unexpected error during LSP parsing: {e}", exc_info=True
            )
            return ParseResult(
                success=False,
                errors=[
                    ParseError(
                        message=f"Unexpected error during LSP parsing: {e!s}",
                        line_number=None,
                        column=None,
                        error_type="unexpected_error",
                        severity="error",
                    )
                ],
                theorems=[],
                metadata=None,
                parse_time_ms=0.0,
            )
        finally:
            await self._stop_lsp_server()

    async def _start_lsp_server(self) -> None:
        """Start the Lean 4 LSP server process."""
        try:
            # Start Lean LSP server with security measures
            # Use shlex.quote to prevent shell injection
            command = [self.lean_executable, "--server"]

            # Additional security: no shell execution
            self._process = subprocess.Popen(
                command,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=0,
                shell=False,  # Explicitly disable shell execution
                env=os.environ.copy(),  # Use a copy of environment
            )

            # Initialize LSP with standard initialize request
            await self._send_lsp_request(
                "initialize",
                {
                    "processId": None,
                    "clientInfo": {"name": "proof-sketcher", "version": "0.1.0"},
                    "capabilities": {
                        "textDocument": {
                            "hover": {"contentFormat": ["markdown", "plaintext"]},
                            "definition": {"linkSupport": True},
                            "documentSymbol": {
                                "hierarchicalDocumentSymbolSupport": True
                            },
                        }
                    },
                    "workspaceFolders": None,
                },
            )

            # Send initialized notification
            await self._send_lsp_notification("initialized", {})

            self.logger.debug("LSP server started successfully")

        except subprocess.SubprocessError as e:
            self.logger.error(f"Failed to start LSP server process: {e}")
            raise LSPConnectionError(f"Failed to start LSP server: {e}")
        except Exception as e:
            self.logger.error(
                f"Unexpected error starting LSP server: {e}", exc_info=True
            )
            raise LSPConnectionError(f"Failed to start LSP server: {e}")

    async def _stop_lsp_server(self) -> None:
        """Stop the LSP server process."""
        if self._process:
            try:
                # Send shutdown request
                await self._send_lsp_request("shutdown", {})
                await self._send_lsp_notification("exit", {})

                # Terminate process
                self._process.terminate()
                self._process.wait(timeout=5)

            except Exception as e:
                self.logger.warning(f"Error stopping LSP server: {e}")
                if self._process:
                    self._process.kill()
            finally:
                self._process = None

    async def _send_lsp_request(
        self, method: str, params: dict[str, Any]
    ) -> dict[str, Any]:
        """Send an LSP request and wait for response."""
        if not self._process or not self._process.stdin:
            raise RuntimeError("LSP server not running")

        self._request_id += 1
        request = {
            "jsonrpc": "2.0",
            "id": self._request_id,
            "method": method,
            "params": params,
        }

        # Send request
        request_str = json.dumps(request)
        content_length = len(request_str.encode("utf-8"))
        message = f"Content-Length: {content_length}\r\n\r\n{request_str}"

        self._process.stdin.write(message)
        self._process.stdin.flush()

        # Read response
        response = await self._read_lsp_response()

        if "error" in response:
            raise RuntimeError(f"LSP error: {response['error']}")

        return response.get("result", {})

    async def _send_lsp_notification(self, method: str, params: dict[str, Any]) -> None:
        """Send an LSP notification (no response expected)."""
        if not self._process or not self._process.stdin:
            raise RuntimeError("LSP server not running")

        notification = {"jsonrpc": "2.0", "method": method, "params": params}

        notification_str = json.dumps(notification)
        content_length = len(notification_str.encode("utf-8"))
        message = f"Content-Length: {content_length}\r\n\r\n{notification_str}"

        self._process.stdin.write(message)
        self._process.stdin.flush()

    async def _read_lsp_response(self) -> dict[str, Any]:
        """Read an LSP response from the server."""
        if not self._process or not self._process.stdout:
            raise RuntimeError("LSP server not running")

        # Read headers
        headers = {}
        while True:
            line = self._process.stdout.readline().strip()
            if not line:
                break
            if ": " in line:
                key, value = line.split(": ", 1)
                headers[key] = value

        # Read content
        content_length = int(headers.get("Content-Length", 0))
        content = self._process.stdout.read(content_length)

        return json.loads(content)

    async def _initialize_file(self, file_path: Path) -> None:
        """Initialize a file with the LSP server."""
        content = file_path.read_text(encoding="utf-8")

        await self._send_lsp_notification(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": file_path.as_uri(),
                    "languageId": "lean4",
                    "version": 1,
                    "text": content,
                }
            },
        )

        # Wait a bit for the server to process the file
        await asyncio.sleep(1)

    async def _extract_theorems_semantic(
        self, file_path: Path
    ) -> list[SemanticTheoremInfo]:
        """Extract theorems with semantic analysis using LSP."""
        theorems = []

        try:
            # Get document symbols (theorems, lemmas, etc.)
            symbols = await self._send_lsp_request(
                "textDocument/documentSymbol",
                {"textDocument": {"uri": file_path.as_uri()}},
            )

            # Process each symbol
            for symbol in symbols:
                if symbol.get("kind") in [
                    8,
                    12,
                ]:  # Function or Constant (theorems/lemmas)
                    theorem = await self._analyze_theorem_symbol(file_path, symbol)
                    if theorem:
                        theorems.append(theorem)

        except Exception as e:
            self.logger.warning(f"Failed to extract theorems semantically: {e}")
            # Fall back to simple parsing if LSP fails
            return await self._fallback_to_simple_parsing(file_path)

        return theorems

    async def _analyze_theorem_symbol(
        self, file_path: Path, symbol: dict[str, Any]
    ) -> SemanticTheoremInfo | None:
        """Analyze a single theorem symbol using LSP."""
        try:
            name = symbol.get("name", "unknown")
            range_info = symbol.get("range", {})

            # Get definition location
            start_line = range_info.get("start", {}).get("line", 0)
            start_char = range_info.get("start", {}).get("character", 0)

            # Get hover information for the theorem
            hover_info = await self._get_hover_info(file_path, start_line, start_char)

            # Get definition information
            definition_info = await self._get_definition_info(
                file_path, start_line, start_char
            )

            # Extract semantic information from hover and definition
            statement = self._extract_statement_from_hover(hover_info)
            proof_info = self._extract_proof_info(file_path, range_info)

            # Analyze proof structure if available
            proof_states, tactic_sequence = await self._analyze_proof_structure(
                file_path, range_info, proof_info
            )

            # Calculate complexity and identify mathematical areas
            complexity_score = self._calculate_complexity(tactic_sequence, proof_states)
            math_entities = self._extract_mathematical_entities(statement, hover_info)

            return SemanticTheoremInfo(
                name=name,
                statement=statement,
                proof=proof_info.get("text", ""),
                dependencies=proof_info.get("dependencies", []),
                line_number=start_line + 1,  # Convert to 1-based
                docstring=hover_info.get("documentation"),
                namespace=definition_info.get("namespace"),
                visibility="public",
                tactics=tactic_sequence,
                is_axiom=self._is_axiom(hover_info),
                file_path=str(file_path),
                start_line=start_line + 1,
                end_line=range_info.get("end", {}).get("line", start_line) + 1,
                # Semantic analysis fields
                proof_states=proof_states,
                tactic_sequence=tactic_sequence,
                semantic_dependencies=proof_info.get("semantic_deps", []),
                mathematical_entities=math_entities,
                complexity_score=complexity_score,
                proof_method=self._identify_proof_method(tactic_sequence),
                # LSP metadata
                definition_location=(start_line, start_char),
                type_signature=hover_info.get("type"),
                hover_info=hover_info.get("contents"),
            )

        except Exception as e:
            self.logger.warning(
                f"Failed to analyze theorem {symbol.get('name', 'unknown')}: {e}"
            )
            return None

    async def _get_hover_info(
        self, file_path: Path, line: int, character: int
    ) -> dict[str, Any]:
        """Get hover information for a position."""
        try:
            result = await self._send_lsp_request(
                "textDocument/hover",
                {
                    "textDocument": {"uri": file_path.as_uri()},
                    "position": {"line": line, "character": character},
                },
            )
            return result or {}
        except Exception:
            return {}

    async def _get_definition_info(
        self, file_path: Path, line: int, character: int
    ) -> dict[str, Any]:
        """Get definition information for a position."""
        try:
            result = await self._send_lsp_request(
                "textDocument/definition",
                {
                    "textDocument": {"uri": file_path.as_uri()},
                    "position": {"line": line, "character": character},
                },
            )
            return result[0] if result else {}
        except Exception:
            return {}

    def _extract_statement_from_hover(self, hover_info: dict[str, Any]) -> str:
        """Extract theorem statement from hover information."""
        contents = hover_info.get("contents", {})
        if isinstance(contents, dict):
            return contents.get("value", "")
        elif isinstance(contents, list) and contents:
            return (
                contents[0].get("value", "")
                if isinstance(contents[0], dict)
                else str(contents[0])
            )
        return str(contents) if contents else ""

    def _extract_proof_info(
        self, file_path: Path, range_info: dict[str, Any]
    ) -> dict[str, Any]:
        """Extract proof information from file content."""
        try:
            content = file_path.read_text(encoding="utf-8")
            lines = content.split("\n")

            start_line = range_info.get("start", {}).get("line", 0)
            end_line = range_info.get("end", {}).get("line", start_line)

            proof_lines = lines[start_line : end_line + 1]
            proof_text = "\n".join(proof_lines)

            return {
                "text": proof_text,
                "dependencies": self._extract_dependencies(proof_text),
                "semantic_deps": self._extract_semantic_dependencies(proof_text),
            }
        except Exception:
            return {"text": "", "dependencies": [], "semantic_deps": []}

    async def _analyze_proof_structure(
        self, file_path: Path, range_info: dict[str, Any], proof_info: dict[str, Any]
    ) -> tuple[list[ProofState], list[TacticInfo]]:
        """Analyze the structure of a proof to extract states and tactics."""
        # This is a simplified version - full implementation would use LSP's
        # goal state information and tactic analysis
        proof_states = []
        tactic_sequence = []

        proof_text = proof_info.get("text", "")

        # Extract tactics from proof text (basic implementation)
        import re

        tactic_patterns = [r"by\s+(\w+)", r"(\w+)\s*\(", r"(\w+)\s*$"]

        lines = proof_text.split("\n")
        for i, line in enumerate(lines):
            for pattern in tactic_patterns:
                matches = re.findall(pattern, line.strip())
                for match in matches:
                    if match in [
                        "simp",
                        "rw",
                        "exact",
                        "apply",
                        "intro",
                        "cases",
                        "induction",
                    ]:
                        tactic_info = TacticInfo(
                            name=match,
                            arguments=[],
                            line_number=range_info.get("start", {}).get("line", 0) + i,
                            column=0,
                        )
                        tactic_sequence.append(tactic_info)

        return proof_states, tactic_sequence

    def _calculate_complexity(
        self, tactics: list[TacticInfo], states: list[ProofState]
    ) -> float:
        """Calculate proof complexity score."""
        if not tactics:
            return 0.0

        # Simple complexity scoring
        complexity_weights = {
            "simp": 1.0,
            "rw": 1.5,
            "exact": 2.0,
            "apply": 2.5,
            "intro": 1.0,
            "cases": 3.0,
            "induction": 4.0,
            "conv": 5.0,
            "calc": 4.0,
        }

        total_score = sum(
            complexity_weights.get(tactic.name, 2.0) for tactic in tactics
        )
        return total_score / len(tactics) if tactics else 0.0

    def _extract_mathematical_entities(
        self, statement: str, hover_info: dict[str, Any]
    ) -> list[str]:
        """Extract mathematical entities from statement and hover information."""
        entities = set()

        # Extract from statement
        import re

        entity_patterns = [
            r"\b(Nat|Int|Real|Complex|Set|List|Vector|Matrix)\b",
            r"\b[A-Z][a-zA-Z]*\b",  # Type names
        ]

        for pattern in entity_patterns:
            entities.update(re.findall(pattern, statement))

        return list(entities)

    def _identify_proof_method(self, tactics: list[TacticInfo]) -> str:
        """Identify the primary proof method used."""
        if not tactics:
            return "unknown"

        tactic_counts = {}
        for tactic in tactics:
            tactic_counts[tactic.name] = tactic_counts.get(tactic.name, 0) + 1

        # Identify method based on dominant tactics
        if "induction" in tactic_counts:
            return "induction"
        elif "simp" in tactic_counts and tactic_counts["simp"] > len(tactics) / 2:
            return "simplification"
        elif "rw" in tactic_counts:
            return "rewriting"
        elif "cases" in tactic_counts:
            return "case_analysis"
        elif "apply" in tactic_counts:
            return "application"
        else:
            return "direct"

    def _extract_dependencies(self, proof_text: str) -> list[str]:
        """Extract theorem dependencies from proof text."""
        import re

        # Look for explicit theorem applications
        dep_patterns = [
            r"apply\s+([a-zA-Z_][a-zA-Z0-9_]*)",
            r"exact\s+([a-zA-Z_][a-zA-Z0-9_]*)",
            r"rw\s*\[([^\]]+)\]",
        ]

        dependencies = set()
        for pattern in dep_patterns:
            matches = re.findall(pattern, proof_text)
            dependencies.update(matches)

        return list(dependencies)

    def _extract_semantic_dependencies(self, proof_text: str) -> list[str]:
        """Extract semantic dependencies (imports, namespaces, etc.)."""
        # This would analyze semantic relationships - simplified for now
        return []

    def _is_axiom(self, hover_info: dict[str, Any]) -> bool:
        """Determine if this is an axiom."""
        contents = str(hover_info.get("contents", "")).lower()
        return "axiom" in contents or "sorry" in contents

    async def _get_lean_version(self) -> str:
        """Get the Lean version."""
        try:
            result = subprocess.run(
                [self.lean_executable, "--version"],
                capture_output=True,
                text=True,
                timeout=5,
            )
            return result.stdout.strip()
        except Exception:
            return "unknown"

    async def _fallback_to_simple_parsing(
        self, file_path: Path
    ) -> list[SemanticTheoremInfo]:
        """Fallback to simple regex parsing if LSP fails."""
        from .simple_parser import SimpleLeanParser

        simple_parser = SimpleLeanParser()
        result = simple_parser.parse_file(file_path)

        # Convert TheoremInfo to SemanticTheoremInfo
        semantic_theorems = []
        for theorem in result.theorems:
            semantic_theorem = SemanticTheoremInfo(
                name=theorem.name,
                statement=theorem.statement,
                proof=theorem.proof,
                dependencies=theorem.dependencies,
                line_number=theorem.line_number,
                docstring=theorem.docstring,
                namespace=theorem.namespace,
                visibility=theorem.visibility,
                tactics=theorem.tactics,
                is_axiom=theorem.is_axiom,
                file_path=theorem.file_path,
                start_line=theorem.start_line,
                end_line=theorem.end_line,
                # Default semantic values
                proof_states=[],
                tactic_sequence=[],
                semantic_dependencies=[],
                mathematical_entities=[],
                complexity_score=0.0,
                proof_method="unknown",
            )
            semantic_theorems.append(semantic_theorem)

        return semantic_theorems


# Convenience function for backward compatibility
async def parse_file_with_lsp(file_path: Path | str) -> ParseResult:
    """Parse a Lean file using LSP client.

    Args:
        file_path: Path to the Lean file

    Returns:
        ParseResult with semantic analysis
    """
    client = LeanLSPClient()
    return await client.parse_file(file_path)
