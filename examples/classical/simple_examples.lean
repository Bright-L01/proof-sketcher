-- Simple Classical Examples for Testing
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

-- Example 1: Simple arithmetic
theorem add_zero (n : ℕ) : n + 0 = n := by
  simp

-- Example 2: Commutativity of natural numbers
theorem nat_add_comm (n m : ℕ) : n + m = m + n := by
  exact Nat.add_comm n m

-- Example 3: Associativity
theorem nat_add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c

-- Example 4: Simple real number fact
theorem real_add_zero (x : ℝ) : x + 0 = x := by
  simp

-- Example 5: Multiplication by one
theorem real_mul_one (x : ℝ) : x * 1 = x := by
  simp