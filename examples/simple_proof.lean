-- Simple equality proof example

/-- Basic reflexivity example -/
theorem eq_refl_example (a : Nat) : a = a := by
  rfl

/-- Symmetry of equality -/
theorem eq_symm_example (a b : Nat) (h : a = b) : b = a := by
  exact h.symm

/-- Transitivity of equality -/
theorem eq_trans_example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  exact h1.trans h2

/-- Simple arithmetic: zero is neutral for addition -/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [Nat.add_succ]
    rw [ih]

/-- Commutativity of addition (simplified) -/
theorem add_comm_simple (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]