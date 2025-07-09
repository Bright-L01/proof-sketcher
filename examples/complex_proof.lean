-- Complex multi-step proof with various tactics

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime

/-- Helper: list reversal is involutive -/
theorem reverse_reverse {α : Type} (l : List α) : l.reverse.reverse = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [List.reverse_cons]
    rw [ih]

/-- Pigeonhole principle for lists -/
theorem pigeonhole_list (l : List Nat) (h : l.length > l.toFinset.card * 2) :
    ∃ x, (l.filter (· = x)).length > 2 := by
  -- Proof by contradiction
  by_contra h_not
  push_neg at h_not

  -- Count occurrences of each element
  have count_bound : ∀ x ∈ l.toFinset, (l.filter (· = x)).length ≤ 2 := by
    intro x hx
    exact h_not x

  -- Sum of all counts equals list length
  have sum_eq : l.length = (l.toFinset.sum fun x => (l.filter (· = x)).length) := by
    sorry -- Complex counting argument

  -- But sum is bounded by card * 2
  have sum_le : (l.toFinset.sum fun x => (l.filter (· = x)).length) ≤ l.toFinset.card * 2 := by
    sorry -- Finite sum argument

  -- Contradiction
  linarith

/-- Example with case analysis -/
theorem min_cases (a b : Nat) : min a b = a ∨ min a b = b := by
  unfold min
  split_ifs with h
  · left
    rfl
  · right
    rfl

/-- Example with exists and forall -/
theorem exists_prime_gt (n : Nat) : ∃ p, Nat.Prime p ∧ p > n := by
  -- Use the fact that there are infinitely many primes
  cases' Nat.exists_infinite_primes (n + 1) with p hp
  use p
  constructor
  · exact hp.1
  · exact hp.2

/-- Complex equality chain -/
theorem complex_calc (a b c d : Nat) (h1 : a = b + 1) (h2 : b = c + 1) (h3 : c = d + 1) :
    a = d + 3 := by
  calc a = b + 1 := h1
       _ = (c + 1) + 1 := by rw [h2]
       _ = c + 2 := by ring
       _ = (d + 1) + 2 := by rw [h3]
       _ = d + 3 := by ring

/-- Using classical logic -/
theorem not_not_intro (p : Prop) (hp : p) : ¬¬p := by
  intro h_not_p
  exact h_not_p hp

/-- De Morgan's law with tactics -/
theorem demorgan_and (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  · -- Forward direction
    intro h
    by_cases hp : p
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp
  · -- Backward direction
    intro h ⟨hp, hq⟩
    cases h with
    | inl h_not_p => exact h_not_p hp
    | inr h_not_q => exact h_not_q hq

/-- Function composition example -/
theorem comp_example {α β γ : Type} (f : α → β) (g : β → γ) (h : γ → α) :
    ∀ x, (h ∘ g ∘ f) x = h (g (f x)) := by
  intro x
  rfl
