
import Foundation
import Data.ListOps

-- Advanced arithmetic properties

/-- Addition is commutative -/
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp [zero_add, add_zero]
  | succ a ih =>
    rw [succ_add, ih, ← add_succ, add_one]

/-- Addition is associative -/
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => simp [zero_add]
  | succ a ih =>
    simp [succ_add, ih]

/-- Multiplication distributes over addition -/
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero => simp
  | succ a ih =>
    simp [Nat.succ_mul, ih, add_assoc]
    rw [add_comm (a * b), add_assoc, add_comm c, ← add_assoc]
