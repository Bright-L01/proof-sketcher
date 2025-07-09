#!/usr/bin/env python3
"""Tests for the enhanced Lean 4 parser."""

import tempfile
from pathlib import Path

import pytest

from src.proof_sketcher.parser.enhanced_parser import LeanConstruct
from src.proof_sketcher.parser.lean_parser import LeanParser


class TestEnhancedParser:
    """Test enhanced Lean 4 parser capabilities."""

    def setup_method(self):
        """Set up test environment."""
        self.parser = LeanParser()

    def test_theorem_parsing(self):
        """Test basic theorem parsing still works."""
        content = """
-- Basic theorem test
theorem test_theorem (n : ℕ) : n + 0 = n := by simp

lemma test_lemma (a b : ℕ) : a + b = b + a := by
  exact Nat.add_comm a b
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            f.flush()
            temp_path = Path(f.name)

        try:
            # Test basic parsing
            result = self.parser.parse_file(temp_path)
            assert result.success
            assert len(result.theorems) >= 2

            # Test enhanced parsing
            declarations = self.parser.parse_file_enhanced(temp_path)
            assert "theorem" in declarations
            assert "lemma" in declarations
            assert len(declarations["theorem"]) >= 1
            assert len(declarations["lemma"]) >= 1

        finally:
            temp_path.unlink()

    def test_inductive_parsing(self):
        """Test inductive type parsing."""
        content = """
-- Inductive type test
inductive Color : Type where
  | red : Color
  | green : Color
  | blue : Color
  deriving Repr, DecidableEq

inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            f.flush()
            temp_path = Path(f.name)

        try:
            declarations = self.parser.parse_file_enhanced(temp_path)
            assert "inductive" in declarations
            assert len(declarations["inductive"]) >= 2

            # Check that constructors are parsed
            color_inductive = None
            for inductive in declarations["inductive"]:
                if inductive.name == "Color":
                    color_inductive = inductive
                    break

            assert color_inductive is not None
            assert len(color_inductive.constructors) == 3
            assert any(c["name"] == "red" for c in color_inductive.constructors)

        finally:
            temp_path.unlink()

    def test_structure_parsing(self):
        """Test structure parsing."""
        content = """
-- Structure test
structure Point where
  x : ℝ
  y : ℝ
  deriving Repr

structure Rectangle extends Point where
  width : ℝ
  height : ℝ
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            f.flush()
            temp_path = Path(f.name)

        try:
            declarations = self.parser.parse_file_enhanced(temp_path)
            assert "structure" in declarations
            assert len(declarations["structure"]) >= 2

            # Check structure fields
            point_structure = None
            for structure in declarations["structure"]:
                if structure.name == "Point":
                    point_structure = structure
                    break

            assert point_structure is not None
            assert len(point_structure.fields) >= 2
            assert any(f["name"] == "x" for f in point_structure.fields)
            assert any(f["name"] == "y" for f in point_structure.fields)

        finally:
            temp_path.unlink()

    def test_class_and_instance_parsing(self):
        """Test class and instance parsing."""
        content = """
-- Class and instance test
class Additive (α : Type) where
  add : α → α → α
  zero : α

instance : Additive ℕ where
  add := Nat.add
  zero := 0
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            f.flush()
            temp_path = Path(f.name)

        try:
            declarations = self.parser.parse_file_enhanced(temp_path)
            assert "class" in declarations
            assert "instance" in declarations
            assert len(declarations["class"]) >= 1
            assert len(declarations["instance"]) >= 1

            # Check class fields
            additive_class = declarations["class"][0]
            assert additive_class.name == "Additive"
            assert len(additive_class.fields) >= 2

        finally:
            temp_path.unlink()

    def test_definition_parsing(self):
        """Test definition parsing."""
        content = """
-- Definition test
def double (n : ℕ) : ℕ := n + n

noncomputable def sqrt (x : ℝ) : ℝ := Real.sqrt x

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            f.flush()
            temp_path = Path(f.name)

        try:
            declarations = self.parser.parse_file_enhanced(temp_path)
            assert "def" in declarations
            assert len(declarations["def"]) >= 3

            # Check noncomputable detection
            sqrt_def = None
            for definition in declarations["def"]:
                if definition.name == "sqrt":
                    sqrt_def = definition
                    break

            assert sqrt_def is not None
            assert sqrt_def.is_noncomputable

        finally:
            temp_path.unlink()

    def test_namespace_parsing(self):
        """Test namespace parsing."""
        content = """
-- Namespace test
namespace MyMath

def add (a b : ℕ) : ℕ := a + b

theorem add_comm (a b : ℕ) : add a b = add b a := by
  simp [add, Nat.add_comm]

end MyMath
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            f.flush()
            temp_path = Path(f.name)

        try:
            declarations = self.parser.parse_file_enhanced(temp_path)
            assert "namespace" in declarations
            assert len(declarations["namespace"]) >= 1

            # The theorems should now be parsed with namespace context
            namespace_decl = declarations["namespace"][0]
            assert namespace_decl.name == "MyMath"

        finally:
            temp_path.unlink()

    def test_complex_file_parsing(self):
        """Test parsing a complex file with multiple constructs."""
        content = """
-- Complex file test
import Mathlib.Data.Nat.Basic

namespace TestProject

/-- A simple color type -/
inductive Color : Type where
  | red : Color
  | green : Color
  | blue : Color
  deriving Repr

/-- Point structure with coordinates -/
structure Point where
  x : ℝ
  y : ℝ

class Drawable (α : Type) where
  draw : α → String

instance : Drawable Color where
  draw
    | Color.red => "Red"
    | Color.green => "Green"
    | Color.blue => "Blue"

@[simp]
def distance (p1 p2 : Point) : ℝ :=
  Real.sqrt ((p1.x - p2.x)^2 + (p1.y - p2.y)^2)

theorem distance_self (p : Point) : distance p p = 0 := by
  simp [distance]

axiom classical_logic : ∀ P : Prop, P ∨ ¬P

end TestProject
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            f.flush()
            temp_path = Path(f.name)

        try:
            # Test parsing statistics
            stats = self.parser.get_parsing_statistics(temp_path)
            assert stats["total_constructs"] > 5
            assert stats["construct_counts"]["inductive"] >= 1
            assert stats["construct_counts"]["structure"] >= 1
            assert stats["construct_counts"]["class"] >= 1
            assert stats["construct_counts"]["instance"] >= 1
            assert stats["construct_counts"]["def"] >= 1
            assert stats["construct_counts"]["theorem"] >= 1
            assert stats["construct_counts"]["axiom"] >= 1
            assert stats["construct_counts"]["namespace"] >= 1

            # Test enhanced vs basic comparison
            assert stats["theorem_count_enhanced"] >= stats["theorem_count_basic"]

        finally:
            temp_path.unlink()

    def test_supported_constructs(self):
        """Test getting supported constructs."""
        constructs = self.parser.get_supported_constructs()

        expected_constructs = [
            "theorem",
            "lemma",
            "def",
            "inductive",
            "structure",
            "class",
            "instance",
            "axiom",
            "namespace",
        ]

        for construct in expected_constructs:
            assert construct in constructs

    def test_docstring_and_attributes(self):
        """Test parsing of docstrings and attributes."""
        content = """
/-- This is a documented theorem -/
@[simp]
theorem documented_theorem (n : ℕ) : n + 0 = n := by simp

@[instance]
def my_instance : DecidableEq ℕ := Nat.decEq
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            f.flush()
            temp_path = Path(f.name)

        try:
            declarations = self.parser.parse_file_enhanced(temp_path)

            # Check theorem with docstring and attributes
            theorem = declarations["theorem"][0]
            assert theorem.docstring is not None
            assert "documented" in theorem.docstring
            assert len(theorem.attributes) >= 1

        finally:
            temp_path.unlink()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
