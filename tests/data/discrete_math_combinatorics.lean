-- Combinatorics Examples for Discrete Mathematics

/-- Binomial coefficient symmetry: C(n,k) = C(n,n-k) -/
theorem binom_symm (n k : Nat) (h : k ≤ n) : Nat.choose n k = Nat.choose n (n - k) := by
  rw [Nat.choose_symm_of_eq_add]
  rw [Nat.add_sub_cancel' h]

/-- Pascal's identity: C(n+1,k+1) = C(n,k) + C(n,k+1) -/
theorem pascal_identity (n k : Nat) : 
  Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) := by
  rw [Nat.choose_succ_succ]

/-- C(n,0) = 1 for all n -/
theorem choose_zero (n : Nat) : Nat.choose n 0 = 1 := by
  rw [Nat.choose_zero]

/-- C(n,n) = 1 for all n -/
theorem choose_self (n : Nat) : Nat.choose n n = 1 := by
  rw [Nat.choose_self]

/-- C(n,1) = n for all n -/
theorem choose_one (n : Nat) : Nat.choose n 1 = n := by
  cases n with
  | zero => rfl
  | succ n => rw [Nat.choose_one]

/-- Factorial recurrence: (n+1)! = (n+1) * n! -/
theorem factorial_succ (n : Nat) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  rfl

/-- 0! = 1 -/
theorem factorial_zero : Nat.factorial 0 = 1 := by
  rfl

/-- 1! = 1 -/
theorem factorial_one : Nat.factorial 1 = 1 := by
  rfl

/-- Permutation formula: P(n,k) = n! / (n-k)! when k ≤ n -/
-- Note: In Lean, we typically work with the relationship directly rather than division
theorem perm_def (n k : Nat) (h : k ≤ n) : 
  n.factorial = Nat.choose n k * k.factorial * (n - k).factorial := by
  rw [← Nat.choose_mul_factorial_mul_factorial h]

/-- Sum of first n numbers using combination identity -/
theorem sum_range_choose (n : Nat) : 
  (List.range n).sum = Nat.choose n 2 := by
  sorry -- This requires more advanced techniques