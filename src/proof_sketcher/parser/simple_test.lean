/-
Simple test file without Mathlib dependencies for testing ExtractTheorem.lean
-/

/-- Addition of zero is the identity -/
theorem simple_add_zero (n : Nat) : n + 0 = n := by
  rfl

/-- Equality is reflexive -/
theorem simple_refl (x : Nat) : x = x := by
  rfl

/-- Identity function theorem -/
theorem simple_id (α : Type) (x : α) : id x = x := by
  rfl

/-- Simple implication -/
theorem simple_impl (P Q : Prop) (h1 : P) (h2 : P → Q) : Q := by
  exact h2 h1

/-- Constructor example -/
theorem simple_and (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq