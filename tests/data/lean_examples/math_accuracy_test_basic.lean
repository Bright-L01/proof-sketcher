-- Basic Arithmetic Tests for Mathematical Accuracy Evaluation
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

-- Test 1: Fundamental arithmetic properties
theorem test_add_zero (n : ℕ) : n + 0 = n := by
  rfl

theorem test_zero_add (n : ℕ) : 0 + n = n := by
  simp

theorem test_add_comm (m n : ℕ) : m + n = n + m := by
  exact Nat.add_comm m n

theorem test_mul_one (n : ℕ) : n * 1 = n := by
  simp

theorem test_one_mul (n : ℕ) : 1 * n = n := by
  simp

-- Test 2: Associativity laws
theorem test_add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c

theorem test_mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  exact Nat.mul_assoc a b c

-- Test 3: Distributivity
theorem test_left_distrib (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  exact Nat.left_distrib a b c

theorem test_right_distrib (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  exact Nat.right_distrib a b c

-- Test 4: Real number arithmetic (for comparison)
theorem test_real_add_zero (x : ℝ) : x + 0 = x := by
  ring

theorem test_real_mul_one (x : ℝ) : x * 1 = x := by
  ring