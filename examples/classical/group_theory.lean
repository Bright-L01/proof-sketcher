-- Group Theory Examples for Proof Sketcher

-- Example 1: Identity element is unique
theorem unique_identity (G : Type*) [Group G] :
  ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a := by
  use 1
  constructor
  · intro a
    simp [one_mul, mul_one]
  · intro e' he'
    have h1 : e' = e' * 1 := by rw [mul_one]
    have h2 : e' * 1 = 1 := by
      have := he' 1
      rw [←this.1, one_mul]
    rw [h1, h2]

-- Example 2: Inverse is unique
theorem unique_inverse (G : Type*) [Group G] (a : G) :
  ∃! b : G, a * b = 1 ∧ b * a = 1 := by
  use a⁻¹
  constructor
  · simp [mul_inv_self, inv_mul_self]
  · intro b hb
    have h1 : b = 1 * b := by rw [one_mul]
    have h2 : 1 * b = (a⁻¹ * a) * b := by rw [inv_mul_self]
    have h3 : (a⁻¹ * a) * b = a⁻¹ * (a * b) := by rw [mul_assoc]
    have h4 : a⁻¹ * (a * b) = a⁻¹ * 1 := by rw [hb.1]
    have h5 : a⁻¹ * 1 = a⁻¹ := by rw [mul_one]
    rw [h1, h2, h3, h4, h5]

-- Example 3: Cancellation law
theorem left_cancellation (G : Type*) [Group G] (a b c : G) :
  a * b = a * c → b = c := by
  intro h
  have : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by rw [h]
  rw [←mul_assoc, ←mul_assoc, inv_mul_self, one_mul, one_mul] at this
  exact this

-- Example 4: Order of identity is 1
theorem order_of_identity (G : Type*) [Group G] :
  orderOf (1 : G) = 1 := by
  rw [orderOf_eq_one_iff]

-- Example 5: Subgroup criterion (Lagrange's theorem component)
theorem subgroup_criterion {G : Type*} [Group G] (H : Set G) :
  (1 ∈ H ∧ (∀ a b, a ∈ H → b ∈ H → a * b ∈ H) ∧ (∀ a, a ∈ H → a⁻¹ ∈ H)) ↔
  Subgroup.carrier (⟨H, sorry⟩ : Subgroup G) = H := by
  sorry -- This requires more setup
