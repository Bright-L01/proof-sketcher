
-- Foundation: Basic arithmetic properties

/-- Zero is the additive identity on the right -/
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ, ih]

/-- Zero is the additive identity on the left -/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.succ_eq_add_one, ← ih]
    rfl

/-- One plus a number equals its successor -/
lemma add_one (n : Nat) : n + 1 = n.succ := by
  rfl

/-- Successor distributes over addition -/
theorem succ_add (n m : Nat) : n.succ + m = (n + m).succ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.add_succ, ih, Nat.add_succ]
