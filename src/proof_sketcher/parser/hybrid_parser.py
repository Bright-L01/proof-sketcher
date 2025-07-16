"""Hybrid parser that combines LSP semantic analysis with simple fallback.

This parser provides the best of both worlds:
- Advanced semantic analysis via Lean 4 LSP when available
- Reliable fallback to regex-based parsing when LSP is unavailable
- Seamless interface that abstracts the complexity

The hybrid approach ensures that Proof Sketcher works in all environments:
- Full-featured semantic analysis in Lean 4 environments
- Basic functionality in environments without Lean 4 installation
- Graceful degradation when LSP server has issues

Key Features:
- Automatic LSP availability detection
- Transparent fallback mechanism
- Consistent interface regardless of backend
- Performance optimization (LSP caching, simple parser speed)
- Educational content enhancement for both modes
"""

import asyncio
import logging
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Optional, Union

from .lsp_client import LeanLSPClient, SemanticTheoremInfo
from .models import ParseResult, TheoremInfo, FileMetadata, ParseError
from .simple_parser import SimpleLeanParser


class HybridLeanParser:
    """Hybrid parser combining LSP semantic analysis with simple fallback."""
    
    def __init__(
        self, 
        lean_executable: str = "lean",
        prefer_lsp: bool = True,
        lsp_timeout: float = 30.0,
        enable_fallback: bool = True
    ):
        """Initialize the hybrid parser.
        
        Args:
            lean_executable: Path to Lean 4 executable
            prefer_lsp: Whether to prefer LSP over simple parsing
            lsp_timeout: Timeout for LSP operations
            enable_fallback: Whether to fall back to simple parsing on LSP failure
        """
        self.lean_executable = lean_executable
        self.prefer_lsp = prefer_lsp
        self.lsp_timeout = lsp_timeout
        self.enable_fallback = enable_fallback
        self.logger = logging.getLogger(__name__)
        
        # Initialize parsers
        self.lsp_client = LeanLSPClient(lean_executable, lsp_timeout)
        self.simple_parser = SimpleLeanParser()
        
        # Runtime state
        self._lsp_available: Optional[bool] = None
        self._lsp_checked = False
        
    async def parse_file(self, file_path: Union[Path, str]) -> ParseResult:
        """Parse a Lean file using the best available method.
        
        Args:
            file_path: Path to the Lean file
            
        Returns:
            ParseResult with the richest available analysis
        """
        if isinstance(file_path, str):
            file_path = Path(file_path)
            
        # Validate file exists
        if not file_path.exists():
            return self._create_error_result(f"File not found: {file_path}", "file_not_found")
            
        if file_path.suffix != ".lean":
            return self._create_error_result(f"Not a Lean file: {file_path}", "invalid_file_type")
            
        # Determine which parser to use
        use_lsp = await self._should_use_lsp()
        
        if use_lsp and self.prefer_lsp:
            self.logger.info(f"Parsing {file_path} with LSP semantic analysis")
            try:
                result = await self.lsp_client.parse_file(file_path)
                
                # LSP result already has proper FileMetadata, just return it
                
                return result
                
            except Exception as e:
                self.logger.warning(f"LSP parsing failed: {e}")
                
                # Fall back to simple parsing if enabled
                if self.enable_fallback:
                    self.logger.info("Falling back to simple parsing")
                    return await self._parse_with_simple_fallback(file_path, lsp_error=str(e))
                else:
                    return self._create_error_result(f"LSP parsing failed: {e}", "lsp_error")
        else:
            # Use simple parser
            self.logger.info(f"Parsing {file_path} with simple regex parser")
            return await self._parse_with_simple_fallback(file_path)
            
    def parse_file_sync(self, file_path: Union[Path, str]) -> ParseResult:
        """Synchronous wrapper for parse_file.
        
        Args:
            file_path: Path to the Lean file
            
        Returns:
            ParseResult
        """
        try:
            # Try to get existing event loop
            loop = asyncio.get_event_loop()
            if loop.is_running():
                # If we're in an async context, we can't use run()
                # Fall back to simple parsing
                self.logger.info("Already in async context, using simple parser")
                return self._parse_with_simple_sync(file_path)
            else:
                # Run in the existing event loop
                return loop.run_until_complete(self.parse_file(file_path))
        except RuntimeError:
            # No event loop, create one
            return asyncio.run(self.parse_file(file_path))
            
    async def _should_use_lsp(self) -> bool:
        """Determine if LSP should be used based on availability."""
        if not self.prefer_lsp:
            return False
            
        # Check cache
        if self._lsp_checked and self._lsp_available is not None:
            return self._lsp_available
            
        # Check if Lean 4 is available
        try:
            result = subprocess.run(
                [self.lean_executable, "--version"],
                capture_output=True,
                text=True,
                timeout=5
            )
            
            if result.returncode == 0:
                version_output = result.stdout.lower()
                
                # Check for Lean 4 (LSP support)
                if "lean 4" in version_output or "lean version 4" in version_output:
                    self._lsp_available = True
                    self.logger.debug(f"Lean 4 detected: {result.stdout.strip()}")
                else:
                    self._lsp_available = False
                    self.logger.info(f"Non-Lean 4 version detected: {result.stdout.strip()}")
            else:
                self._lsp_available = False
                self.logger.warning(f"Lean executable check failed: {result.stderr}")
                
        except (subprocess.TimeoutExpired, FileNotFoundError, Exception) as e:
            self._lsp_available = False
            self.logger.info(f"Lean not available: {e}")
            
        self._lsp_checked = True
        return self._lsp_available or False
        
    async def _parse_with_simple_fallback(
        self, file_path: Path, lsp_error: Optional[str] = None
    ) -> ParseResult:
        """Parse using simple parser with enhanced metadata."""
        result = self.simple_parser.parse_file(file_path)
        
        # Simple parser already creates proper FileMetadata, just use it as-is
            
        # Convert TheoremInfo to SemanticTheoremInfo for consistency
        if result.success and result.theorems:
            enhanced_theorems = []
            for theorem in result.theorems:
                if not isinstance(theorem, SemanticTheoremInfo):
                    enhanced_theorem = SemanticTheoremInfo(
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
                        
                        # Add basic semantic analysis from simple parser
                        proof_states=[],
                        tactic_sequence=[],
                        semantic_dependencies=[],
                        mathematical_entities=self._extract_entities_simple(theorem.statement),
                        complexity_score=self._estimate_complexity_simple(theorem.proof),
                        proof_method=self._guess_proof_method_simple(theorem.proof),
                    )
                    enhanced_theorems.append(enhanced_theorem)
                else:
                    enhanced_theorems.append(theorem)
            result.theorems = enhanced_theorems
            
        return result
        
    def _parse_with_simple_sync(self, file_path: Union[Path, str]) -> ParseResult:
        """Synchronous simple parsing with basic enhancement."""
        if isinstance(file_path, str):
            file_path = Path(file_path)
            
        result = self.simple_parser.parse_file(file_path)
        
        # Simple parser already creates proper FileMetadata, just return it
        return result
        
    def _extract_entities_simple(self, statement: str) -> list[str]:
        """Extract mathematical entities from statement (simple version)."""
        if not statement:
            return []
            
        import re
        entities = set()
        
        # Extract type names and mathematical constructs
        patterns = [
            r'\b(Nat|Int|Real|Complex|Set|List|Vector|Matrix|Group|Ring|Field)\b',
            r'\b[A-Z][a-zA-Z]*\b',  # Capitalized words (likely types)
        ]
        
        for pattern in patterns:
            entities.update(re.findall(pattern, statement))
            
        return list(entities)
        
    def _estimate_complexity_simple(self, proof: str) -> float:
        """Estimate proof complexity (simple heuristic)."""
        if not proof:
            return 0.0
            
        # Simple scoring based on proof length and keywords
        length_score = min(len(proof) / 100, 5.0)  # Max 5 points for length
        
        complexity_keywords = {
            'induction': 4.0,
            'cases': 3.0,
            'conv': 5.0,
            'calc': 4.0,
            'have': 2.0,
            'let': 2.0,
            'simp': 1.0,
            'rw': 1.5,
            'exact': 2.0,
            'apply': 2.5,
        }
        
        keyword_score = 0.0
        for keyword, score in complexity_keywords.items():
            if keyword in proof.lower():
                keyword_score += score
                
        return min(length_score + keyword_score, 10.0)  # Max complexity of 10
        
    def _guess_proof_method_simple(self, proof: str) -> str:
        """Guess the primary proof method (simple heuristic)."""
        if not proof:
            return "unknown"
            
        proof_lower = proof.lower()
        
        if 'induction' in proof_lower:
            return "induction"
        elif 'cases' in proof_lower:
            return "case_analysis"
        elif 'simp' in proof_lower and len(proof) < 50:
            return "simplification"
        elif 'rw' in proof_lower:
            return "rewriting"
        elif 'calc' in proof_lower:
            return "calculation"
        elif 'apply' in proof_lower:
            return "application"
        elif 'exact' in proof_lower:
            return "direct"
        else:
            return "mixed"
            
    def _create_error_result(self, message: str, error_type: str) -> ParseResult:
        """Create a ParseResult for errors."""
        return ParseResult(
            success=False,
            errors=[ParseError(
                message=message,
                line_number=None,
                column=None,
                error_type=error_type,
                severity="error"
            )],
            theorems=[],
            metadata=None,  # No metadata available on error
            parse_time_ms=0.0,
        )
        
    async def get_parser_status(self) -> dict[str, any]:
        """Get status information about available parsers."""
        lsp_available = await self._should_use_lsp()
        
        status = {
            "lsp_available": lsp_available,
            "lsp_preferred": self.prefer_lsp,
            "fallback_enabled": self.enable_fallback,
            "lean_executable": self.lean_executable,
        }
        
        if lsp_available:
            try:
                version = await self.lsp_client._get_lean_version()
                status["lean_version"] = version
            except Exception:
                status["lean_version"] = "unknown"
        else:
            status["lean_version"] = "not_available"
            
        return status
        
    def get_parser_status_sync(self) -> dict[str, any]:
        """Synchronous version of get_parser_status."""
        try:
            return asyncio.run(self.get_parser_status())
        except Exception:
            return {
                "lsp_available": False,
                "lsp_preferred": self.prefer_lsp,
                "fallback_enabled": self.enable_fallback,
                "lean_executable": self.lean_executable,
                "lean_version": "error",
            }