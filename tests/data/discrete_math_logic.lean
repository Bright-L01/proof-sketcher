-- Logic and Set Theory Examples for Discrete Mathematics

/-- De Morgan's law: ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) -/
theorem de_morgan_and (P Q : Prop) : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  constructor
  · intro h
    by_cases hp : P
    · by_cases hq : Q
      · have : P ∧ Q := ⟨hp, hq⟩
        contradiction
      · right; exact hq
    · left; exact hp
  · intro h
    intro hpq
    cases h with
    | inl hnp => exact hnp hpq.1
    | inr hnq => exact hnq hpq.2

/-- Proof by contradiction: If ¬¬P then P (in classical logic) -/
theorem double_negation_elim (P : Prop) : ¬¬P → P := by
  intro h
  by_contra hp
  exact h hp

/-- Contrapositive: (P → Q) ↔ (¬Q → ¬P) -/
theorem contrapositive (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  · intro h hnq hp
    exact hnq (h hp)
  · intro h hp
    by_contra hnq
    exact h hnq hp

/-- Distributivity: P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) -/
theorem and_or_distrib (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h
    cases h.2 with
    | inl hq => left; exact ⟨h.1, hq⟩
    | inr hr => right; exact ⟨h.1, hr⟩
  · intro h
    cases h with
    | inl hpq => exact ⟨hpq.1, Or.inl hpq.2⟩
    | inr hpr => exact ⟨hpr.1, Or.inr hpr.2⟩

/-- Set inclusion transitivity: A ⊆ B ∧ B ⊆ C → A ⊆ C -/
theorem subset_trans {α : Type*} (A B C : Set α) : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hab hbc x hxa
  exact hbc (hab hxa)

/-- Set intersection is commutative: A ∩ B = B ∩ A -/
theorem inter_comm {α : Type*} (A B : Set α) : A ∩ B = B ∩ A := by
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨h.2, h.1⟩
  · intro h; exact ⟨h.2, h.1⟩