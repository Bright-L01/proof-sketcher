-- Induction Tests for Mathematical Accuracy Evaluation
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic

-- Test 1: Sum of first n natural numbers
def sum_first_n : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sum_first_n n

theorem test_sum_formula (n : ℕ) : 2 * sum_first_n n = n * (n + 1) := by
  induction n with
  | zero =>
    simp [sum_first_n]
  | succ n ih =>
    calc 2 * sum_first_n (n + 1)
      = 2 * ((n + 1) + sum_first_n n) := by rfl
      _ = 2 * (n + 1) + 2 * sum_first_n n := by ring
      _ = 2 * (n + 1) + n * (n + 1) := by rw [ih]
      _ = (n + 1) * (2 + n) := by ring
      _ = (n + 1) * (n + 2) := by ring

-- Test 2: Powers of 2
theorem test_power_2_positive (n : ℕ) : 0 < 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc 0 < 2^n := ih
         _ < 2 * 2^n := by linarith
         _ = 2^(n + 1) := by rw [pow_succ]

-- Test 3: Factorial definition and basic property
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem test_factorial_positive (n : ℕ) : 0 < factorial n := by
  induction n with
  | zero =>
    simp [factorial]
  | succ n ih =>
    simp [factorial]
    exact Nat.mul_pos (Nat.succ_pos n) ih

-- Test 4: Geometric series sum
theorem test_geometric_sum (n : ℕ) : (Finset.range (n + 1)).sum (fun i => 2^i) = 2^(n + 1) - 1 := by
  induction n with
  | zero =>
    simp [Finset.sum_range_one]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    ring

-- Test 5: Inequality by induction
theorem test_inequality_induction (n : ℕ) (h : n ≥ 1) : n < 2^n := by
  induction n, h using Nat.le_induction with
  | base =>
    norm_num
  | succ n hn ih =>
    calc n + 1 < 2^n + 1 := by linarith [ih]
               _ ≤ 2^n + 2^n := by simp [pow_succ]; linarith [Nat.one_le_pow _ _ (by norm_num : 1 ≤ 2)]
               _ = 2^(n + 1) := by rw [← two_mul, ← pow_succ]
