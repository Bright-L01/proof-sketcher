-- University Scale Test File: Basic Course Level
-- Simulates a typical undergraduate discrete mathematics or introduction to proofs course
-- Contains 25-30 theorems of varying complexity that a student might encounter

-- Basic arithmetic and equality proofs
theorem add_zero (n : ℕ) : n + 0 = n := by
  rfl

theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.add_succ, ih]

theorem add_comm (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero => simp [add_zero, zero_add]
  | succ n ih => simp [Nat.succ_add, Nat.add_succ, ih]

theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => simp [zero_add]
  | succ a ih => simp [Nat.succ_add, ih]

-- Multiplication properties
theorem mul_zero (n : ℕ) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.succ_mul, ih]

theorem zero_mul (n : ℕ) : 0 * n = 0 := by
  rfl

theorem mul_one (n : ℕ) : n * 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.succ_mul, ih]

theorem one_mul (n : ℕ) : 1 * n = n := by
  simp [Nat.one_mul]

theorem mul_comm (n m : ℕ) : n * m = m * n := by
  induction n with
  | zero => simp [zero_mul, mul_zero]
  | succ n ih => simp [Nat.succ_mul, Nat.mul_succ, ih, add_comm]

-- Basic logic and set theory
theorem and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h
    exact ⟨h.right, h.left⟩
  · intro h
    exact ⟨h.right, h.left⟩

theorem or_comm (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

theorem not_not (P : Prop) [DecidableProp P] : ¬¬P ↔ P := by
  constructor
  · intro h
    by_contra hnp
    exact h hnp
  · intro hp hnp
    exact hnp hp

-- Function properties
theorem function_comp_assoc {α β γ δ : Type*} (f : α → β) (g : β → γ) (h : γ → δ) :
  (h ∘ g) ∘ f = h ∘ (g ∘ f) := by
  rfl

theorem id_left_comp {α β : Type*} (f : α → β) : id ∘ f = f := by
  rfl

theorem id_right_comp {α β : Type*} (f : α → β) : f ∘ id = f := by
  rfl

-- Induction examples
theorem sum_first_n (n : ℕ) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => simp [List.range, List.sum]
  | succ n ih =>
    have h1 : List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by
      simp [List.range_succ]
    rw [h1, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    simp [mul_add, add_mul, ih]
    ring

theorem pow_add (a : ℕ) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp [add_zero, pow_zero, mul_one]
  | succ n ih => simp [add_succ, pow_succ, ih, mul_assoc]

-- Divisibility theorems
theorem dvd_refl (n : ℕ) : n ∣ n := by
  use 1
  simp

theorem dvd_trans {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  use k * l
  rw [← hl, ← hk, mul_assoc]

theorem dvd_add {a b c : ℕ} (hab : a ∣ b) (hac : a ∣ c) : a ∣ (b + c) := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hac
  use k + l
  rw [← hk, ← hl, mul_add]

-- Modular arithmetic basics
theorem mod_self (n : ℕ) (hn : n > 0) : n % n = 0 := by
  simp [Nat.mod_self]

theorem mod_lt (a n : ℕ) (hn : n > 0) : a % n < n := by
  exact Nat.mod_lt a hn

-- List properties
theorem list_length_append {α : Type*} (l1 l2 : List α) :
  (l1 ++ l2).length = l1.length + l2.length := by
  induction l1 with
  | nil => simp
  | cons h t ih => simp [List.length_cons, ih, Nat.succ_add]

theorem list_reverse_length {α : Type*} (l : List α) :
  l.reverse.length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.reverse_cons, list_length_append, ih]

-- Inequality proofs
theorem succ_pos (n : ℕ) : 0 < n + 1 := by
  simp [Nat.succ_pos]

theorem lt_succ_self (n : ℕ) : n < n + 1 := by
  simp [Nat.lt_succ_self]

-- Basic real number properties (if available)
variable {x y z : ℝ}

theorem real_add_comm : x + y = y + x := by
  exact add_comm x y

theorem real_mul_comm : x * y = y * x := by
  exact mul_comm x y

theorem real_add_assoc : (x + y) + z = x + (y + z) := by
  exact add_assoc x y z

-- Absolute value properties
theorem abs_nonneg (x : ℝ) : 0 ≤ |x| := by
  exact abs_nonneg x

theorem abs_zero : |0 : ℝ| = 0 := by
  exact abs_zero

-- Basic set theory
variable {α : Type*} {s t : Set α}

theorem set_union_comm : s ∪ t = t ∪ s := by
  exact Set.union_comm s t

theorem set_inter_comm : s ∩ t = t ∩ s := by
  exact Set.inter_comm s t

theorem subset_refl : s ⊆ s := by
  exact Set.subset_refl s

-- Function injectivity and surjectivity basics
theorem injective_comp {α β γ : Type*} {f : α → β} {g : β → γ}
  (hf : Function.Injective f) (hg : Function.Injective g) :
  Function.Injective (g ∘ f) := by
  exact Function.Injective.comp hg hf

theorem surjective_comp {α β γ : Type*} {f : α → β} {g : β → γ}
  (hf : Function.Surjective f) (hg : Function.Surjective g) :
  Function.Surjective (g ∘ f) := by
  exact Function.Surjective.comp hg hf
