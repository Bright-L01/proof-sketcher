/-
Test file with sample theorems for Proof Sketcher.
Contains various theorem types to test the extractor.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic

/-- Addition of zero is the identity function on natural numbers. -/
theorem add_zero_theorem (n : Nat) : n + 0 = n := by
  rw [Nat.add_zero]

/-- Commutativity of addition for natural numbers. -/
theorem add_comm_theorem (n m : Nat) : n + m = m + n := by
  rw [Nat.add_comm]

/-- Identity function is indeed the identity. -/
lemma id_lemma (α : Type) (x : α) : id x = x := by
  rfl

/-- Modus ponens in propositional logic. -/
theorem modus_ponens (P Q : Prop) (h1 : P) (h2 : P → Q) : Q := by
  exact h2 h1

/-- Double negation elimination for classical logic. -/
theorem double_neg_elim (P : Prop) : ¬¬P → P := by
  intro h
  by_contra h_not_p
  exact h h_not_p

/-- Conjunction is commutative. -/
theorem and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.right
  · exact h.left

/-- De Morgan's law for conjunction. -/
theorem de_morgan_and (P Q : Prop) : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  constructor
  · intro h
    by_contra h_not
    push_neg at h_not
    apply h
    constructor
    · exact h_not.left
    · exact h_not.right
  · intro h h_and
    cases h with
    | inl h_not_p => exact h_not_p h_and.left
    | inr h_not_q => exact h_not_q h_and.right

/-- Simple arithmetic theorem with multiple dependencies. -/
theorem add_assoc_example (a b c : Nat) : (a + b) + c = a + (b + c) := by
  rw [Nat.add_assoc]

/-- A theorem about list length. -/
theorem list_length_cons {α : Type} (x : α) (xs : List α) :
  List.length (x :: xs) = List.length xs + 1 := by
  simp [List.length_cons]

/-- Simple equivalence theorem. -/
theorem iff_refl (P : Prop) : P ↔ P := by
  constructor
  · intro h; exact h
  · intro h; exact h

-- Example with multiple hypotheses
theorem complex_example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  have q : Q := h1 h3
  exact h2 q

-- Theorem with existential quantifier
theorem exists_example : ∃ n : Nat, n + 1 = 2 := by
  use 1
  norm_num

-- Theorem about functions
theorem function_comp_example {α β γ : Type} (f : α → β) (g : β → γ) (x : α) :
  (g ∘ f) x = g (f x) := by
  rfl
