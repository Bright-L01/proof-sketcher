-- Arithmetic and Number Theory Examples for Discrete Mathematics

/-- Addition is commutative: n + m = m + n -/
theorem add_comm (n m : Nat) : n + m = m + n := by
  rw [Nat.add_comm]

/-- Addition is associative: (n + m) + k = n + (m + k) -/
theorem add_assoc (n m k : Nat) : (n + m) + k = n + (m + k) := by
  rw [Nat.add_assoc]

/-- Zero is the additive identity: n + 0 = n -/
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

/-- Zero is the left additive identity: 0 + n = n -/
theorem zero_add (n : Nat) : 0 + n = n := by
  rw [Nat.zero_add]

/-- Multiplication distributes over addition: n * (m + k) = n * m + n * k -/
theorem mul_add (n m k : Nat) : n * (m + k) = n * m + n * k := by
  rw [Nat.mul_add]

/-- Multiplication is commutative: n * m = m * n -/
theorem mul_comm (n m : Nat) : n * m = m * n := by
  rw [Nat.mul_comm]

/-- One is the multiplicative identity: n * 1 = n -/
theorem mul_one (n : Nat) : n * 1 = n := by
  rw [Nat.mul_one]

/-- Zero multiplication: n * 0 = 0 -/
theorem mul_zero (n : Nat) : n * 0 = 0 := by
  rw [Nat.mul_zero]

/-- Successor function: n + 1 = succ n -/
theorem add_one_eq_succ (n : Nat) : n + 1 = Nat.succ n := by
  rfl

/-- Cancellation law for addition: if n + k = m + k then n = m -/
theorem add_right_cancel (n m k : Nat) : n + k = m + k → n = m := by
  intro h
  exact Nat.add_right_cancel h