-- Tutorial: Your First Proof with Proof Sketcher
-- This file demonstrates basic theorem proving and explanation generation

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

-- 🎯 TUTORIAL OBJECTIVE
-- Learn how to write simple Lean 4 theorems and generate explanations

namespace Tutorial

-- Example 1: Basic Natural Number Arithmetic
theorem add_zero (n : ℕ) : n + 0 = n := by
  -- This follows directly from the definition of addition
  rfl

-- Example 2: Simple Commutativity
theorem nat_add_comm (n m : ℕ) : n + m = m + n := by
  -- We use the built-in commutativity
  exact Nat.add_comm n m

-- Example 3: Associativity with Step-by-Step Proof
theorem nat_add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  -- Step 1: Use the associativity property
  rw [Nat.add_assoc]

-- Example 4: Simple Identity Property
theorem zero_add (n : ℕ) : 0 + n = n := by
  -- By definition of natural number addition
  simp

-- Example 5: More Complex Example - Cancellation
theorem add_left_cancel (a b c : ℕ) (h : a + b = a + c) : b = c := by
  -- Cancel 'a' from both sides
  exact Nat.add_left_cancel h

-- Example 6: Introduction to Groups (Preview)
variable (G : Type*) [Group G]

-- This theorem shows unique identity in groups
theorem group_identity_unique : ∃! e : G, ∀ a : G, e * a = a ∧ a * e = a := by
  -- The identity element 1 satisfies this property
  use 1
  constructor
  · intro a
    simp [one_mul, mul_one]
  · intro e' he'
    -- Any other identity must equal 1
    have h1 : e' = e' * 1 := by rw [mul_one]
    have h2 : e' * 1 = 1 := by
      have := he' 1
      rw [←this.1, one_mul]
    rw [h1, h2]

end Tutorial

-- 🚀 HOW TO USE THIS FILE
/-
1. List all theorems:
   python -m proof_sketcher list-theorems examples/tutorial/first_proof.lean

2. Generate explanation for a simple theorem:
   python -m proof_sketcher prove examples/tutorial/first_proof.lean \
     --theorem add_zero \
     --format markdown

3. Generate explanations for all theorems:
   python -m proof_sketcher prove examples/tutorial/first_proof.lean \
     --format html \
     --output tutorial_output/

4. Try offline mode (no AI required):
   python -m proof_sketcher prove examples/tutorial/first_proof.lean \
     --offline \
     --format markdown

5. Generate with animations:
   python -m proof_sketcher prove examples/tutorial/first_proof.lean \
     --animate \
     --format html

📚 LEARNING OBJECTIVES:
• Understand basic Lean 4 syntax
• Learn how theorem statements work
• See different proof techniques (rfl, exact, rw, simp)
• Experience the power of automated explanation generation
• Explore both simple and complex mathematical concepts

💡 NEXT STEPS:
• Try modifying the theorems
• Add your own simple theorems
• Explore the showcase examples in showcase/algebra_proofs.lean
• Read the generated explanations to understand the mathematics
-/
