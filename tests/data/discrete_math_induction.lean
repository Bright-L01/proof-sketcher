-- Mathematical Induction Examples for Discrete Mathematics

/-- Sum of first n natural numbers equals n(n+1)/2 -/
theorem sum_first_n_naturals (n : Nat) :
  (List.range (n + 1)).sum = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp [List.range_succ]
    rw [ih]
    ring

/-- 2^n ≥ n + 1 for all natural numbers n -/
theorem two_pow_ge_succ (n : Nat) : 2^n ≥ n + 1 := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    calc 2 * 2^k
      ≥ 2 * (k + 1) := by apply Nat.mul_le_mul_left; exact ih
      _ = 2 * k + 2 := by ring
      _ ≥ k + 1 + 1 := by simp; apply Nat.add_le_add_right; simp
      _ = k + 2 := by ring
      _ = (k + 1) + 1 := by ring

/-- Every integer n ≥ 8 can be expressed as 3a + 5b for non-negative integers a, b -/
theorem coin_problem (n : Nat) (h : n ≥ 8) :
  ∃ a b : Nat, n = 3 * a + 5 * b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases' n with n
    · -- n = 0, contradicts h
      simp at h
    cases' n with n
    · -- n = 1, contradicts h
      simp at h
    cases' n with n
    · -- n = 2, contradicts h
      simp at h
    cases' n with n
    · -- n = 3, contradicts h
      simp at h
    cases' n with n
    · -- n = 4, contradicts h
      simp at h
    cases' n with n
    · -- n = 5, contradicts h
      simp at h
    cases' n with n
    · -- n = 6, contradicts h
      simp at h
    cases' n with n
    · -- n = 7, contradicts h
      simp at h
    cases' n with n
    · -- n = 8 = 3*1 + 5*1
      use 1, 1
      norm_num
    cases' n with n
    · -- n = 9 = 3*3 + 5*0
      use 3, 0
      norm_num
    cases' n with n
    · -- n = 10 = 3*0 + 5*2
      use 0, 2
      norm_num
    · -- n ≥ 11, use induction hypothesis on n-3
      have h_ge : n + 11 ≥ 8 := by simp; linarith
      have h_minus : n + 8 ≥ 8 := by simp; linarith
      obtain ⟨a, b, hab⟩ := ih (n + 8) (by simp) h_minus
      use a + 1, b
      rw [← hab]
      ring
