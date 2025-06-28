/-
Copyright (c) 2024 Proof Sketcher Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Proof Sketcher Contributors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Example theorems from mathlib style

This file demonstrates Proof Sketcher with mathlib-style theorems.
-/

namespace ProofSketcherExamples

section NatTheorems

/-- The sum of two even numbers is even. -/
theorem even_add_even {m n : ℕ} (hm : Even m) (hn : Even n) : Even (m + n) := by
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨l, rfl⟩ := hn
  use k + l
  ring

/-- The product of any number with an even number is even. -/
theorem mul_even {m n : ℕ} (hn : Even n) : Even (m * n) := by
  obtain ⟨k, rfl⟩ := hn
  use m * k
  ring

/-- Fibonacci sequence is defined recursively. -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- The Fibonacci sequence satisfies a specific recurrence relation. -/
theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by
  rfl

end NatTheorems

section ListTheorems

open List

variable {α : Type*}

/-- Appending a list to itself doubles its length. -/
theorem length_append_self (l : List α) : length (l ++ l) = 2 * length l := by
  simp [two_mul]

/-- Reversing a concatenation distributes over the lists. -/
theorem reverse_append (l₁ l₂ : List α) : reverse (l₁ ++ l₂) = reverse l₂ ++ reverse l₁ := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The head of a non-empty list remains the same after appending to its tail. -/
theorem head_cons_append (x : α) (xs ys : List α) : 
    head? (x :: xs ++ ys) = some x := by
  rfl

end ListTheorems

section LogicTheorems

variable (p q r : Prop)

/-- Modus tollens: from ¬q and p → q, we can derive ¬p. -/
theorem modus_tollens : ¬q → (p → q) → ¬p := by
  intros hnq hpq hp
  exact hnq (hpq hp)

/-- De Morgan's law for conjunction. -/
theorem not_and_de_morgan : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  · intro h
    by_cases hp : p
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp
  · intro h ⟨hp, hq⟩
    cases h with
    | inl hnp => exact hnp hp
    | inr hnq => exact hnq hq

/-- The contrapositive is logically equivalent to the original implication. -/
theorem contrapositive : (p → q) ↔ (¬q → ¬p) := by
  constructor
  · intros hpq hnq hp
    exact hnq (hpq hp)
  · intros hcp hp
    by_contra hnq
    exact hcp hnq hp

end LogicTheorems

end ProofSketcherExamples