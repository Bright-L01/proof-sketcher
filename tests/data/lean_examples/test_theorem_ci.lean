theorem add_zero (n : Nat) : n + 0 = n := by
  induction n
  · rfl
  · simp
