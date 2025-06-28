/-!
# Natural Number Theorems

This file contains theorems about natural numbers for testing Proof Sketcher.
-/

namespace ProofSketcherExamples

open Nat

/-- Addition is commutative for natural numbers -/
theorem nat_add_comm (m n : Nat) : m + n = n + m := by
  induction m with
  | zero => simp
  | succ m ih => simp [add_succ, ih]

/-- Zero is a left identity for addition -/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add_succ, ih]

/-- Addition is associative -/
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => rfl
  | succ a ih => simp [add_succ, ih]

/-- Multiplication distributes over addition -/
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => simp
  | succ a ih => simp [succ_mul, add_assoc, ih]

end ProofSketcherExamples