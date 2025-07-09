import Mathlib.Data.Nat.Basic

-- Simple theorem for testing
theorem add_zero (n : ℕ) : n + 0 = n := by
  rfl

-- Theorem with tactics
theorem add_comm_simple (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]

-- Theorem with induction
theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

-- Theorem with dependencies
theorem add_assoc_example (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c
