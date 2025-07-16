"""Test configuration and shared fixtures."""

import shutil
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, Mock

import pytest

# AI client imports removed - not implemented in alpha version
from src.proof_sketcher.generator.models import ProofSketch, ProofStep
from src.proof_sketcher.parser.models import TheoremInfo


@pytest.fixture
def temp_dir():
    """Provide temporary directory that cleans up after test."""
    with tempfile.TemporaryDirectory() as tmpdir:
        yield Path(tmpdir)


@pytest.fixture
def sample_lean_file(temp_dir):
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
def complex_lean_file(temp_dir):
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
def malformed_lean_file(temp_dir):
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
def empty_lean_file(temp_dir):
    """Create an empty Lean file."""
    lean_file = temp_dir / "empty.lean"
    lean_file.write_text("")
    return lean_file


@pytest.fixture
def sample_theorem():
    """Create a sample TheoremInfo for testing."""
    return TheoremInfo(
        name="add_comm",
        statement="∀ (a b : Nat), a + b = b + a",
        proof="by induction a with | zero => simp | succ a ih => simp [succ_add, ih]",
        dependencies=["Mathlib.Data.Nat.Basic"],
        docstring="Addition is commutative for natural numbers",
        line_number=3,
        visibility="public",
    )


@pytest.fixture
def sample_proof_sketch():
    """Create a sample ProofSketch for testing."""
    return ProofSketch(
        theorem_name="add_comm",
        theorem_statement="∀ (a b : Nat), a + b = b + a",
        introduction="This theorem establishes that addition is commutative for natural numbers.",
        key_steps=[
            ProofStep(
                step_number=1,
                description="Base case: prove 0 + b = b + 0",
                mathematical_content="0 + b = b",
                tactics=["simp"],
                intuition="Zero is the additive identity",
            ),
            ProofStep(
                step_number=2,
                description="Inductive step: assume (a + b = b + a) and prove (succ a + b = b + succ a)",
                mathematical_content="succ a + b = succ (a + b) = succ (b + a) = b + succ a",
                tactics=["simp", "succ_add"],
                intuition="Use the induction hypothesis and properties of successor",
            ),
        ],
        conclusion="By mathematical induction, addition is commutative for all natural numbers.",
        difficulty_level="intermediate",
        mathematical_areas=["algebra", "number_theory"],
        prerequisites=["natural numbers", "mathematical induction"],
    )


# AI client fixtures removed - not implemented in alpha version


@pytest.fixture
def output_dir(temp_dir):
    """Create an output directory for testing exporters."""
    output_dir = temp_dir / "output"
    output_dir.mkdir(exist_ok=True)
    return output_dir


@pytest.fixture
def sample_files(temp_dir):
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

    # Set test-friendly environment
    monkeypatch.setenv("PROOF_SKETCHER_TEST_MODE", "true")


@pytest.fixture
def captured_logs(caplog):
    """Capture logs for testing."""
    return caplog


# Test markers
pytest.mark.slow = pytest.mark.mark(
    "slow", reason="Slow test - may take several seconds"
)

pytest.mark.integration = pytest.mark.mark(
    "integration", reason="Integration test - tests multiple components"
)

pytest.mark.unit = pytest.mark.mark("unit", reason="Unit test - tests single component")

pytest.mark.parser = pytest.mark.mark("parser", reason="Parser-related test")

pytest.mark.generator = pytest.mark.mark("generator", reason="Generator-related test")

pytest.mark.exporter = pytest.mark.mark("exporter", reason="Exporter-related test")
