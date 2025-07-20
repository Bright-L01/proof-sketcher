-- University Scale Test File: Intermediate Level
-- Simulates advanced undergraduate course in real analysis or abstract algebra
-- Contains 20-25 more complex theorems with longer proofs

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Basic
import Mathlib.Algebra.Group.Basic

-- Real analysis theorems
theorem intermediate_value_simplified (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
  (hfa : f a < 0) (hfb : 0 < f b) (hcont : ContinuousOn f (Set.Icc a b)) :
  ∃ c ∈ Set.Icc a b, f c = 0 := by
  -- This would normally require the intermediate value theorem from Mathlib
  sorry

theorem monotone_function_image (f : ℝ → ℝ) (hf : Monotone f) (s : Set ℝ) :
  f '' s = {y | ∃ x ∈ s, f x = y} := by
  rfl

theorem continuous_image_compact (f : ℝ → ℝ) (K : Set ℝ)
  (hK : IsCompact K) (hf : ContinuousOn f K) :
  IsCompact (f '' K) := by
  exact IsCompact.image hK hf

-- Sequence convergence
theorem convergent_sequence_bounded (a : ℕ → ℝ) (L : ℝ)
  (ha : Filter.Tendsto a Filter.atTop (𝓝 L)) :
  ∃ M : ℝ, ∀ n : ℕ, |a n| ≤ M := by
  -- Convergent sequences are bounded
  sorry

theorem squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ)
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
  (ha : Filter.Tendsto a Filter.atTop (𝓝 L))
  (hc : Filter.Tendsto c Filter.atTop (𝓝 L)) :
  Filter.Tendsto b Filter.atTop (𝓝 L) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le ha hc hab hbc

-- Series convergence
theorem geometric_series_convergence (r : ℝ) (hr : |r| < 1) :
  ∃ S : ℝ, Filter.Tendsto (fun n ↦ ∑ k in Finset.range n, r^k) Filter.atTop (𝓝 S) := by
  use 1 / (1 - r)
  -- Would require geometric series formula
  sorry

-- Group theory basics
variable {G : Type*} [Group G]

theorem group_left_cancel (a b c : G) : a * b = a * c → b = c := by
  exact Group.mul_left_cancel

theorem group_inv_unique (a b : G) (h : a * b = 1) : b = a⁻¹ := by
  have : b = 1 * b := by simp
  rw [← Group.mul_left_inv a] at this
  rw [← Group.mul_assoc] at this
  rw [h] at this
  rw [Group.one_mul] at this
  exact this.symm

theorem subgroup_contains_inverse {H : Subgroup G} (h : G) (hh : h ∈ H) : h⁻¹ ∈ H := by
  exact Subgroup.inv_mem H hh

-- Ring theory
variable {R : Type*} [Ring R]

theorem ring_mul_neg_one (a : R) : a * (-1) = -a := by
  exact mul_neg_one a

theorem ring_distributive_left (a b c : R) : a * (b + c) = a * b + a * c := by
  exact mul_add a b c

theorem ring_distributive_right (a b c : R) : (a + b) * c = a * c + b * c := by
  exact add_mul a b c

-- Field properties
variable {F : Type*} [Field F]

theorem field_inv_mul (a : F) (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  exact Field.inv_mul_cancel ha

theorem field_div_self (a : F) (ha : a ≠ 0) : a / a = 1 := by
  exact div_self ha

-- Linear algebra basics
theorem vector_add_comm {V : Type*} [AddCommGroup V] (u v : V) : u + v = v + u := by
  exact add_comm u v

theorem scalar_distributive {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (a : F) (u v : V) : a • (u + v) = a • u + a • v := by
  exact smul_add a u v

-- Topology basics
theorem open_sets_union {X : Type*} [TopologicalSpace X]
  (𝒰 : Set (Set X)) (h : ∀ U ∈ 𝒰, IsOpen U) :
  IsOpen (⋃₀ 𝒰) := by
  exact isOpen_sSup h

theorem closed_sets_intersection {X : Type*} [TopologicalSpace X]
  (𝒞 : Set (Set X)) (h : ∀ C ∈ 𝒞, IsClosed C) :
  IsClosed (⋂₀ 𝒞) := by
  exact isClosed_sSup h

-- Metric space properties
variable {X : Type*} [MetricSpace X]

theorem metric_triangle (x y z : X) : dist x z ≤ dist x y + dist y z := by
  exact dist_triangle x y z

theorem metric_nonneg (x y : X) : 0 ≤ dist x y := by
  exact dist_nonneg

theorem metric_self (x : X) : dist x x = 0 := by
  exact dist_self x

-- Calculus basics
theorem derivative_sum (f g : ℝ → ℝ) (x : ℝ)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  deriv (fun t ↦ f t + g t) x = deriv f x + deriv g x := by
  exact deriv_add hf hg

theorem derivative_constant (c : ℝ) (x : ℝ) :
  deriv (fun _ : ℝ ↦ c) x = 0 := by
  exact deriv_const _ _

theorem derivative_identity (x : ℝ) :
  deriv (fun t : ℝ ↦ t) x = 1 := by
  exact deriv_id'' x

-- Integration basics
theorem integral_linearity (f g : ℝ → ℝ) (a b c d : ℝ) :
  ∫ x in a..b, (c • f x + d • g x) = c • ∫ x in a..b, f x + d • ∫ x in a..b, g x := by
  simp [integral_smul, integral_add]

-- Complex analysis preview
theorem complex_conjugate_mul (z w : ℂ) : (z * w)† = z† * w† := by
  exact Complex.conj_mul z w

theorem complex_modulus_mul (z w : ℂ) : |z * w| = |z| * |w| := by
  exact Complex.abs_mul z w

-- Advanced number theory
theorem euclid_gcd_lemma (a b : ℕ) : Nat.gcd a b = Nat.gcd b (a % b) := by
  exact Nat.gcd_rec a b

theorem bezout_identity (a b : ℕ) (ha : a > 0) (hb : b > 0) :
  ∃ x y : ℤ, (x : ℤ) * a + (y : ℤ) * b = Nat.gcd a b := by
  exact Nat.gcd_eq_gcd_ab a b

-- Probability theory basics
theorem probability_complement {Ω : Type*} (P : Set Ω → ℝ) (A : Set Ω)
  (h_prob : P A + P Aᶜ = 1) : P Aᶜ = 1 - P A := by
  linarith

-- Graph theory
structure SimpleGraph (V : Type*) where
  adj : V → V → Prop
  symm : ∀ a b, adj a b → adj b a
  irrefl : ∀ a, ¬adj a a

theorem graph_degree_sum {V : Type*} [Fintype V] (G : SimpleGraph V) :
  ∑ v : V, (Finset.filter (G.adj v) (Finset.univ : Finset V)).card % 2 = 0 := by
  -- Handshaking lemma - sum of degrees is even
  sorry
