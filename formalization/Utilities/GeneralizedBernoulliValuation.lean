module

public import Utilities.GeneralizedBernoulliProducts
public import Utilities.PadicProductBound
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Utilities.PrimeLogSum

@[expose] public section

open scoped BigOperators

namespace Utilities

/-- The weighted prime valuations of an integer are bounded on every finite set
of primes by the logarithm of its absolute value. -/
theorem sum_padicValInt_mul_log_le_log_abs (m : ℤ) (S : Finset ℕ)
    (hS : ∀ ℓ ∈ S, ℓ.Prime) :
    (∑ ℓ ∈ S, (padicValInt ℓ m : ℝ) * Real.log ℓ) ≤ Real.log |(m : ℝ)| := by
  have hlog : Real.log |(m : ℝ)| = Real.log (m.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hlog]
  calc
    _ = ∑ ℓ ∈ S, Real.log ℓ * (m.natAbs.factorization ℓ : ℝ) := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      rw [Nat.factorization_def _ (hS ℓ hℓ)]
      change (padicValInt ℓ m : ℝ) * Real.log ℓ = Real.log ℓ * (padicValInt ℓ m : ℝ)
      exact mul_comm _ _
    _ ≤ _ := sum_log_mul_factorization_le m.natAbs S

/-- The one integer product controls the normalized Bernoulli valuation sums
at every prime simultaneously. -/
theorem exists_weighted_padic_bernoulli_bounds {N k : ℕ} [NeZero N] (hk : 2 ≤ k)
    (P : Set (Subgroup (ZMod N)ˣ))
    (hP : ∀ H ∈ P, ((-1 : (ZMod N)ˣ) ∈ H ↔ Even k)) :
    ∃ w : ℕ → ℕ,
      (∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) →
        (∑ ℓ ∈ S, (w ℓ : ℝ) * Real.log ℓ) ≤
          (dirichletCharactersWithKernelIn ℂ P).ncard *
            Real.log (generalizedBernoulliHeightBound N k)) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (T : Finset (DirichletCharacter (PadicAlgCl ℓ) N)),
        (∀ χ ∈ T, χ ∈ dirichletCharactersWithKernelIn (PadicAlgCl ℓ) P) →
        (∑ χ ∈ T, -Real.log ‖(generalizedBernoulliDenominator N k : PadicAlgCl ℓ) *
          primitiveBernoulliValue k χ‖) ≤ (w ℓ : ℝ) * Real.log ℓ := by
  obtain ⟨m, hm, hlog, hprod⟩ := exists_int_normalized_primitiveBernoulliProduct hk P hP
  refine ⟨fun ℓ => padicValInt ℓ m, fun S hS => (sum_padicValInt_mul_log_le_log_abs m S hS).trans hlog,
    fun ℓ _ T hT => ?_⟩
  let : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  let Ω := PadicAlgCl ℓ
  let S := dirichletCharactersWithKernelIn Ω P
  let B (χ : DirichletCharacter Ω N) : Ω :=
    (generalizedBernoulliDenominator N k : Ω) * primitiveBernoulliValue k χ
  have hS : S.Finite := Set.toFinite _
  have hprod' : (∏ χ ∈ hS.toFinset, B χ) = (m : Ω) := by
    have h := hprod Ω
    rw [finprod_mem_eq_finite_toFinset_prod _ hS] at h
    exact h
  have hne : ∀ χ ∈ hS.toFinset, B χ ≠ 0 := by
    rw [← Finset.prod_ne_zero_iff, hprod']
    exact Int.cast_ne_zero.mpr hm
  have hsubset : T ⊆ hS.toFinset := fun χ hχ => hS.mem_toFinset.mpr (hT χ hχ)
  calc
    _ ≤ ∑ χ ∈ hS.toFinset, -Real.log ‖B χ‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro χ _ _
      exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (norm_le_one_of_isIntegral_int
        (isIntegral_normalized_primitiveBernoulliValue χ)))
    _ = -Real.log ‖(m : Ω)‖ := by
      rw [← hprod', norm_prod, Real.log_prod (fun χ hχ => norm_ne_zero_iff.mpr (hne χ hχ)),
        Finset.sum_neg_distrib]
    _ = _ := neg_log_norm_intCast_padicAlgCl ℓ m hm

end Utilities
