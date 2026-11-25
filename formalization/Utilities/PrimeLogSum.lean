module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

open scoped BigOperators

namespace Utilities

/-- A partial sum of prime multiplicities weighted by logarithms is
bounded by the logarithm of the integer. -/
theorem sum_log_mul_factorization_le (n : ℕ) (primes : Finset ℕ) :
    ∑ ℓ ∈ primes, Real.log ℓ * (n.factorization ℓ : ℝ) ≤ Real.log n := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc
    _ = ∑ ℓ ∈ primes ∩ n.factorization.support, Real.log ℓ * (n.factorization ℓ : ℝ) := by
      symm
      refine Finset.sum_subset Finset.inter_subset_left ?_
      intro ℓ hℓ hnot
      have hzero : n.factorization ℓ = 0 := Finsupp.notMem_support_iff.mp
        (fun h => hnot (Finset.mem_inter.mpr ⟨hℓ, h⟩))
      simp [hzero]
    _ ≤ ∑ ℓ ∈ n.factorization.support, Real.log ℓ * (n.factorization ℓ : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun ℓ _ _ =>
        mul_nonneg (Real.log_natCast_nonneg ℓ) (Nat.cast_nonneg _)
    _ = _ := Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Two certificates with different exceptional primes give a simultaneous
weighted bound over every finite set of primes. -/
theorem sum_log_mul_le_of_two_certificates
    {primes : Finset ℕ} {p q n₁ n₂ : ℕ} {w : ℕ → ℝ} (hpq : p ≠ q)
    (h₁ : ∀ ℓ ∈ primes, ℓ ≠ p → w ℓ ≤ 2 * n₁.factorization ℓ)
    (h₂ : ∀ ℓ ∈ primes, ℓ ≠ q → w ℓ ≤ 2 * n₂.factorization ℓ) :
    ∑ ℓ ∈ primes, Real.log ℓ * w ℓ ≤ 2 * (Real.log n₁ + Real.log n₂) := by
  calc
    _ ≤ ∑ ℓ ∈ primes, Real.log ℓ *
        (2 * (n₁.factorization ℓ : ℝ) + 2 * (n₂.factorization ℓ : ℝ)) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg ℓ)
      by_cases h : ℓ = p
      · exact (h₂ ℓ hℓ (h ▸ hpq)).trans (le_add_of_nonneg_left (by positivity))
      · exact (h₁ ℓ hℓ h).trans (le_add_of_nonneg_right (by positivity))
    _ = 2 * ((∑ ℓ ∈ primes, Real.log ℓ * (n₁.factorization ℓ : ℝ)) +
        ∑ ℓ ∈ primes, Real.log ℓ * (n₂.factorization ℓ : ℝ)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (sum_log_mul_factorization_le n₁ primes) (sum_log_mul_factorization_le n₂ primes))
      (by norm_num)

end Utilities
