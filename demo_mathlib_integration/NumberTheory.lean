
-- Number Theory: Prime numbers and divisibility
import Mathlib.Data.Nat.Prime

namespace Nat

/-- Euclid's theorem: There are infinitely many primes -/
theorem infinite_primes : ∀ n : ℕ, ∃ p : ℕ, n < p ∧ Prime p := by
  intro n
  -- Consider the number N = n! + 1
  let N := n.factorial + 1
  -- Let p be the smallest prime factor of N
  obtain ⟨p, hp_prime, hp_dvd⟩ := exists_prime_near N
  use p
  constructor
  · -- Show n < p
    by_contra h
    have h_le : p ≤ n := Nat.le_of_not_gt h
    -- p divides n! since p ≤ n
    have hp_dvd_fact : p ∣ n.factorial := dvd_factorial hp_prime.pos h_le
    -- But p also divides N = n! + 1
    have hp_dvd_one : p ∣ 1 := by
      rw [← Nat.add_sub_cancel n.factorial 1]
      exact dvd_sub' hp_dvd hp_dvd_fact
    -- This contradicts p being prime
    exact Prime.not_dvd_one hp_prime hp_dvd_one
  · exact hp_prime

/-- Fundamental theorem of arithmetic (existence) -/
theorem prime_factorization_exists (n : ℕ) (hn : 1 < n) :
    ∃ l : List ℕ, l.all Prime ∧ l.prod = n := by
  sorry -- Proof omitted for demo

/-- Wilson's theorem: (p-1)! ≡ -1 (mod p) for prime p -/
theorem wilson_theorem (p : ℕ) (hp : Prime p) : (p - 1).factorial ≡ -1 [MOD p] := by
  sorry -- Proof omitted for demo

end Nat
