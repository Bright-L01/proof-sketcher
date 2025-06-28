-- Mathematical induction examples

/-- Sum of first n natural numbers -/
def sum_to_n : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sum_to_n n

/-- Formula for sum of first n natural numbers -/
theorem sum_formula (n : Nat) : 2 * sum_to_n n = n * (n + 1) := by
  induction n with
  | zero => 
    -- Base case: 2 * sum_to_n 0 = 0 * (0 + 1)
    simp [sum_to_n]
  | succ n ih =>
    -- Inductive step: assume true for n, prove for n + 1
    calc 2 * sum_to_n (n + 1) 
      = 2 * ((n + 1) + sum_to_n n) := by rfl
      _ = 2 * (n + 1) + 2 * sum_to_n n := by ring
      _ = 2 * (n + 1) + n * (n + 1) := by rw [ih]
      _ = (n + 1) * (2 + n) := by ring
      _ = (n + 1) * (n + 2) := by ring
      _ = (n + 1) * ((n + 1) + 1) := by ring

/-- Power of 2 is always positive -/
theorem pow_two_pos (n : Nat) : 0 < 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih => 
    calc 0 < 2^n := ih
         _ < 2 * 2^n := by linarith
         _ = 2^(n + 1) := by rw [pow_succ]

/-- Factorial grows faster than powers of 2 -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_ge_2_pow (n : Nat) (h : n ≥ 4) : factorial n ≥ 2^n := by
  induction n, h using Nat.le_induction with
  | base =>
    -- Base case: n = 4
    norm_num [factorial, pow_succ]
  | succ n hn ih =>
    -- Inductive step
    calc factorial (n + 1)
      = (n + 1) * factorial n := by rfl
      _ ≥ (n + 1) * 2^n := by exact Nat.mul_le_mul_left (n + 1) ih
      _ ≥ 2 * 2^n := by {
        apply Nat.mul_le_mul_right
        calc n + 1 ≥ 4 + 1 := by linarith
                  _ = 5 := by norm_num
                  _ ≥ 2 := by norm_num
      }
      _ = 2^(n + 1) := by rw [pow_succ]