-- Test theorem for LSP integration testing
-- This file contains theorems of varying complexity

-- Simple theorem using simp
theorem add_zero (n : Nat) : n + 0 = n := by simp

-- Theorem with induction
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_succ, ih, Nat.succ_add]

-- More complex theorem with multiple tactics
theorem dvd_antisymm {a b : Nat} (h1 : a ∣ b) (h2 : b ∣ a) (ha : 0 < a) : a = b := by
  cases' h1 with k hk
  cases' h2 with l hl
  rw [hk] at hl
  rw [← mul_assoc] at hl
  have : k * l = 1 := by
    sorry -- simplified for testing
  exact hk.symm

-- Simple lemma
lemma zero_add (n : Nat) : 0 + n = n := by
  simp [Nat.zero_add]