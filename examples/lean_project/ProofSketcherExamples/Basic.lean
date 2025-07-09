/-!
# Basic Theorems for Proof Sketcher Examples

This file contains basic theorems to test Proof Sketcher's functionality.
-/

namespace ProofSketcherExamples

/-- Two plus two equals four -/
theorem two_plus_two : 2 + 2 = 4 := by rfl

/-- Logical AND is commutative -/
theorem and_comm (p q : Prop) : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

/-- Modus ponens: from P and P → Q, we can derive Q -/
theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  exact hpq hp

end ProofSketcherExamples
