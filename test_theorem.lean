
-- Simple theorem about natural numbers
theorem add_zero (n : Nat) : n + 0 = n := by
  simp

-- Commutativity of addition
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp [Nat.zero_add]
  | succ a ih => rw [Nat.succ_add, ih, Nat.add_succ]

-- A simple lemma
lemma mul_one (n : Nat) : n * 1 = n := by
  simp
