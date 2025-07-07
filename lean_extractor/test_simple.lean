-- Simple test file without Mathlib dependencies

theorem test_simple : 1 + 1 = 2 := rfl

theorem nat_add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem example_proof (a b : Nat) : a = b → b = a := by
  intro h
  rw [h]