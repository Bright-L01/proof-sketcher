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
from proof_sketcher.generator.models import ProofSketch, ProofStep, ProofStrategy
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
        intuitive_overview="This theorem shows that the order of addition doesn't matter for natural numbers.",
        conceptual_overview="We use mathematical induction on the first argument to prove commutativity.",
        bridging_overview="The proof connects our intuitive understanding of addition with formal induction.",
        formal_overview="This is proven using Lean's induction tactic on natural numbers.",
        key_steps=[
            ProofStep(
                step_number=1,
                intuitive_explanation="First, we check that 0 + b equals b + 0",
                conceptual_explanation="Base case: prove commutativity when a = 0",
                bridging_explanation="We use the definition of addition for zero",
                formal_explanation="By definition, 0 + b = b and b + 0 = b",
                tactics=["simp"],
                mathematical_content="0 + b = b = b + 0",
                lean_code="simp",
            ),
            ProofStep(
                step_number=2,
                intuitive_explanation="If a + b = b + a, then (a+1) + b = b + (a+1)",
                conceptual_explanation="Inductive step: extend from a to successor of a",
                bridging_explanation="Use the inductive hypothesis and successor properties",
                formal_explanation="succ a + b = succ (a + b) = succ (b + a) = b + succ a",
                tactics=["simp", "rw"],
                mathematical_content="succ a + b = b + succ a",
                lean_code="simp [succ_add, ih]",
            ),
        ],
        intuitive_conclusion="Therefore, addition is commutative for all natural numbers.",
        conceptual_conclusion="Induction proves the property holds for all naturals.",
        bridging_conclusion="We've shown our intuition about addition is formally correct.",
        formal_conclusion="By induction, ∀ a b : Nat, a + b = b + a.",
        proof_strategy=ProofStrategy.INDUCTION,
        discrete_math_topic="arithmetic",
        difficulty_level="intermediate",
        mathematical_areas=["arithmetic", "number_theory"],
        prerequisites=["natural_numbers", "induction"],
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

    @staticmethod
    def create_proof_sketch(**overrides) -> ProofSketch:
        """Create a valid ProofSketch with sensible defaults.

        All required fields are provided with test-appropriate defaults.
        Use overrides to customize specific fields.
        """
        defaults = {
            "theorem_name": "test_theorem",
            "theorem_statement": "∀ n : ℕ, n + 0 = n",
            "intuitive_overview": "This theorem shows that adding zero to any natural number leaves it unchanged.",
            "conceptual_overview": "We use the definition of natural number addition to prove this identity property.",
            "bridging_overview": "The proof connects our intuitive understanding of zero as the additive identity with the formal definition in Lean.",
            "formal_overview": "This theorem is proven using Lean's inductive definition of natural number addition.",
            "key_steps": [TestDataFactory.create_proof_step()],
            "intuitive_conclusion": "Therefore, zero is the right identity for addition.",
            "conceptual_conclusion": "This completes our proof of the right identity property.",
            "bridging_conclusion": "We've shown the formal definition matches our intuition.",
            "formal_conclusion": "The theorem is proven by definitional equality.",
            "proof_strategy": ProofStrategy.DIRECT,
            "discrete_math_topic": "arithmetic",
            "difficulty_level": "beginner",
            "mathematical_areas": ["arithmetic", "number_theory"],
            "prerequisites": ["natural_numbers", "addition"],
        }

        defaults.update(overrides)
        return ProofSketch(**defaults)

    @staticmethod
    def create_proof_step(**overrides) -> ProofStep:
        """Create a valid ProofStep with sensible defaults."""
        defaults = {
            "step_number": 1,
            "intuitive_explanation": "Test intuitive explanation",
            "conceptual_explanation": "Test conceptual explanation",
            "bridging_explanation": "Test bridging explanation",
            "formal_explanation": "Test formal explanation",
            "tactics": ["simp"],
            "mathematical_content": "test content",
            "lean_code": "by simp",
        }

        defaults.update(overrides)
        return ProofStep(**defaults)

    @staticmethod
    def create_minimal_proof_sketch(theorem_name: str = "test_theorem") -> ProofSketch:
        """Create a minimal valid ProofSketch for simple tests."""
        return TestDataFactory.create_proof_sketch(
            theorem_name=theorem_name,
            theorem_statement=f"theorem {theorem_name}",
            key_steps=[],
        )


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
