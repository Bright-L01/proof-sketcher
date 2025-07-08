
import Foundation
import Advanced.Arithmetic

-- Applied theorems using previous results

/-- Double of a number equals adding it to itself -/
theorem double_eq_add_self (n : Nat) : 2 * n = n + n := by
  simp [Nat.succ_mul, Nat.one_mul, add_comm]

/-- Square of sum formula -/
theorem square_sum (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  rw [mul_add, mul_add, mul_add]
  simp [mul_comm b a, double_eq_add_self]
  rw [← add_assoc, ← add_assoc]
  rw [add_assoc (a * a), add_comm (a * b), ← add_assoc]

/-- Sum of first n natural numbers -/
theorem sum_first_n (n : Nat) : 2 * (List.range n.succ).sum = n * n.succ := by
  sorry  -- Complex proof omitted for demo
