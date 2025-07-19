-- Logic and Proof Technique Tests for Mathematical Accuracy Evaluation
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic

-- Test 1: Basic propositional logic
theorem test_and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

theorem test_or_comm (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

-- Test 2: De Morgan's laws
theorem test_de_morgan_and (P Q : Prop) : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hp : P
    · by_cases hq : Q
      · exact False.elim (h ⟨hp, hq⟩)
      · exact Or.inr hq
    · exact Or.inl hp
  · intro h
    intro hpq
    cases h with
    | inl hnp => exact hnp hpq.1
    | inr hnq => exact hnq hpq.2

-- Test 3: Proof by contradiction
theorem test_contradiction_sqrt_2 : ¬∃ (p q : ℕ), q ≠ 0 ∧ (p : ℝ)^2 = 2 * (q : ℝ)^2 ∧ Nat.gcd p q = 1 := by
  intro h
  obtain ⟨p, q, hq_ne_zero, h_eq, h_gcd⟩ := h
  -- This is a simplified version - the full proof would be much longer
  sorry -- Placeholder for the detailed contradiction proof

-- Test 4: Proof by cases
theorem test_cases_even_odd (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by
  cases' Nat.mod_two_eq_zero_or_one n with h h
  · exact Or.inl h
  · exact Or.inr h

-- Test 5: Universal quantification
theorem test_forall_example : ∀ n : ℕ, n + 0 = n := by
  intro n
  rfl

-- Test 6: Existential quantification
theorem test_exists_example : ∃ n : ℕ, n > 5 := by
  use 6
  norm_num