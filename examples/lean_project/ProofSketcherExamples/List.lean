/-!
# List Theorems

This file contains theorems about lists for testing Proof Sketcher.
-/

namespace ProofSketcherExamples

open List

/-- Reversing a list twice gives the original list -/
theorem reverse_reverse (l : List α) : reverse (reverse l) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [reverse_cons, ih]

/-- Length of concatenation is sum of lengths -/
theorem length_append (l₁ l₂ : List α) : length (l₁ ++ l₂) = length l₁ + length l₂ := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_succ]

/-- Map fusion: mapping f then g is the same as mapping their composition -/
theorem map_map (f : α → β) (g : β → γ) (l : List α) : 
    map g (map f l) = map (g ∘ f) l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Appending to an empty list -/
theorem append_nil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

end ProofSketcherExamples