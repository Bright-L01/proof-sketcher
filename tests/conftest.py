"""Test configuration and shared fixtures for proof-sketcher."""

from __future__ import annotations

import shutil
import tempfile
from pathlib import Path
from typing import Iterator
from unittest.mock import MagicMock, Mock

import pytest
from click.testing import CliRunner

from proof_sketcher.cli.main import cli
from proof_sketcher.generator.models import ProofSketch, ProofStep
from proof_sketcher.parser.models import TheoremInfo


@pytest.fixture
def cli_runner() -> CliRunner:
    """Provide a Click CLI test runner."""
    return CliRunner()


@pytest.fixture
def temp_dir() -> Iterator[Path]:
    """Provide temporary directory that cleans up after test."""
    with tempfile.TemporaryDirectory() as tmpdir:
        yield Path(tmpdir)


@pytest.fixture
def sample_lean_file(temp_dir: Path) -> Path:
    """Create a sample Lean file for testing."""
    lean_file = temp_dir / "sample.lean"
    lean_file.write_text(
        """
/-- Addition is commutative for natural numbers -/
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih => simp [succ_add, ih]
"""
    )
    return lean_file


@pytest.fixture
def complex_lean_file(temp_dir: Path) -> Path:
    """Create a complex Lean file with multiple theorems."""
    lean_file = temp_dir / "complex.lean"
    lean_file.write_text(
        """
import Mathlib.Data.Nat.Basic

/-- Zero is the additive identity -/
theorem zero_add (n : Nat) : 0 + n = n := by simp

/-- Multiplication distributes over addition -/
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => simp
  | succ a ih => simp [succ_mul, ih, add_assoc]

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => simp
  | succ a ih => simp [succ_add, ih]
"""
    )
    return lean_file


@pytest.fixture
def malformed_lean_file(temp_dir: Path) -> Path:
    """Create a malformed Lean file for error testing."""
    lean_file = temp_dir / "malformed.lean"
    lean_file.write_text(
        """
theorem broken_theorem  -- Missing everything
theorem incomplete : -- Missing proof
def not_a_theorem := 42
this is not valid lean code
"""
    )
    return lean_file


@pytest.fixture
def empty_lean_file(temp_dir: Path) -> Path:
    """Create an empty Lean file."""
    lean_file = temp_dir / "empty.lean"
    lean_file.write_text("")
    return lean_file


@pytest.fixture
def sample_theorem() -> TheoremInfo:
    """Create a sample TheoremInfo for testing."""
    return TheoremInfo(
        name="add_comm",
        statement="∀ (a b : Nat), a + b = b + a",
        type_signature="(a b : Nat) : a + b = b + a",
        docstring="Addition is commutative for natural numbers",
        line_number=3,
        file_path="sample.lean",
        dependencies=["Mathlib.Data.Nat.Basic"],
        tactics=["induction", "simp"],
        namespace="",
        is_theorem=True,
        is_lemma=False,
        is_definition=False,
        complexity_score=2,
        proof_text="by induction a with | zero => simp | succ a ih => simp [succ_add, ih]",
    )


@pytest.fixture
def sample_proof_sketch() -> ProofSketch:
    """Create a sample ProofSketch for testing."""
    return ProofSketch(
        theorem_name="add_comm",
        theorem_statement="∀ (a b : Nat), a + b = b + a",
        explanation="This theorem establishes that addition is commutative for natural numbers.",
        steps=[
            ProofStep(
                step_number=1,
                description="Base case: prove 0 + b = b + 0",
                tactic="simp",
                mathematical_content="0 + b = b",
                complexity=1,
            ),
            ProofStep(
                step_number=2,
                description="Inductive step: assume (a + b = b + a) and prove (succ a + b = b + succ a)",
                tactic="simp [succ_add, ih]",
                mathematical_content="succ a + b = succ (a + b) = succ (b + a) = b + succ a",
                complexity=2,
            ),
        ],
        difficulty_level="intermediate",
        prerequisites=["natural numbers", "mathematical induction"],
        applications=["algebra", "number_theory"],
        proof_strategy="mathematical induction",
        key_insights=[
            "Use induction on the first argument",
            "Apply properties of successor",
        ],
        estimated_time=15,
        source_file="sample.lean",
        generation_metadata={
            "generator": "offline",
            "timestamp": "2025-01-01T00:00:00Z",
            "version": "0.1.0",
        },
    )


@pytest.fixture
def output_dir(temp_dir: Path) -> Path:
    """Create an output directory for testing exporters."""
    output_dir = temp_dir / "output"
    output_dir.mkdir(exist_ok=True)
    return output_dir


@pytest.fixture
def sample_files(temp_dir: Path) -> list[Path]:
    """Create multiple sample files for batch testing."""
    files = []

    # Simple theorem
    simple_file = temp_dir / "simple.lean"
    simple_file.write_text("theorem simple (n : Nat) : n + 0 = n := by simp")
    files.append(simple_file)

    # Theorem with proof
    proof_file = temp_dir / "with_proof.lean"
    proof_file.write_text(
        """
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]
"""
    )
    files.append(proof_file)

    # Theorem with docstring
    doc_file = temp_dir / "with_doc.lean"
    doc_file.write_text(
        """
/-- This theorem shows reflexivity -/
theorem refl_test (n : Nat) : n = n := by rfl
"""
    )
    files.append(doc_file)

    return files


@pytest.fixture(autouse=True)
def clean_environment(monkeypatch):
    """Clean environment variables that might affect tests."""
    # Remove API keys to ensure tests use offline mode
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)

    # Remove other environment variables that might interfere
    env_vars_to_remove = [
        "PROOF_SKETCHER_CONFIG",
        "PROOF_SKETCHER_CACHE_DIR",
        "PROOF_SKETCHER_LOG_LEVEL",
    ]

    for var in env_vars_to_remove:
        monkeypatch.delenv(var, raising=False)

    # Set test-friendly environment
    monkeypatch.setenv("PROOF_SKETCHER_TEST_MODE", "true")


@pytest.fixture
def captured_logs(caplog):
    """Capture logs for testing."""
    return caplog


# Test data factory for generating various test scenarios
class TestDataFactory:
    """Factory for generating test data."""

    @staticmethod
    def create_theorem_info(
        name: str = "test_theorem", statement: str = "True", **kwargs
    ) -> TheoremInfo:
        """Create a TheoremInfo with default values."""
        defaults = {
            "type_signature": f"{name} : {statement}",
            "docstring": f"Test theorem {name}",
            "line_number": 1,
            "file_path": "test.lean",
            "dependencies": [],
            "tactics": [],
            "namespace": "",
            "is_theorem": True,
            "is_lemma": False,
            "is_definition": False,
            "complexity_score": 1,
            "proof_text": "sorry",
        }
        defaults.update(kwargs)

        return TheoremInfo(name=name, statement=statement, **defaults)

    @staticmethod
    def create_lean_file_content(theorems: list[tuple[str, str]] | None = None) -> str:
        """Create Lean file content with specified theorems."""
        if theorems is None:
            theorems = [("test", "True")]

        content = []
        for name, statement in theorems:
            content.append(f"theorem {name} : {statement} := sorry")

        return "\n".join(content)


@pytest.fixture
def test_data_factory() -> TestDataFactory:
    """Provide the test data factory."""
    return TestDataFactory


# Performance testing utility
@pytest.fixture
def performance_timer():
    """Provide a simple performance timer for tests."""
    import time

    class Timer:
        def __init__(self):
            self.start_time = None
            self.end_time = None

        def start(self):
            self.start_time = time.perf_counter()

        def stop(self):
            self.end_time = time.perf_counter()

        @property
        def elapsed(self) -> float:
            if self.start_time is None or self.end_time is None:
                raise ValueError("Timer not properly started/stopped")
            return self.end_time - self.start_time

    return Timer()


# Custom pytest configuration
def pytest_configure(config):
    """Configure custom pytest markers."""
    markers = [
        "slow: marks tests as slow (deselect with '-m \"not slow\"')",
        "integration: marks tests as integration tests",
        "unit: marks tests as unit tests",
        "e2e: marks tests as end-to-end tests",
        "parser: marks tests related to parsing",
        "generator: marks tests related to generation",
        "exporter: marks tests related to export",
        "cli: marks tests related to CLI",
    ]

    for marker in markers:
        config.addinivalue_line("markers", marker)


# Async test support
@pytest.fixture
def event_loop():
    """Create an instance of the default event loop for the test session."""
    import asyncio

    loop = asyncio.get_event_loop_policy().new_event_loop()
    yield loop
    loop.close()
