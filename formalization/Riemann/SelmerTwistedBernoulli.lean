module

public import Riemann.SelmerSharedClosure
import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

open Utilities

namespace Riemann

/-- The remaining Bernoulli input at primes prime to the host degree. The
length is that of the inverse host character Tate twist over the rational
base on the common closure. -/
def HasSelmerSharedTwistBernoulliComparison : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i ≥ 1,
      let F := selmerHostField target e q d
      letI : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
      let f := selmerHostConductor target e q d
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ¬ ℓ ∣ Module.finrank ℚ F →
        ∀ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))
          [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O]
          [HasEnoughRootsOfUnity O (Monoid.exponent (F ≃ₐ[ℚ] F))],
          ∀ ψ : (F ≃ₐ[ℚ] F) →* Oˣ,
            (ψ (selmerHostConductorGalMap target e q d (-1)) : O) = (-1 : O) ^ (i + 1) →
            let T := numberFieldSelmerSharedInverseTwist F ℓ i O ψ
            let n := Module.length O (T.selmerKernel
              (numberFieldSelmerRestrictionsIn ℚ (AlgebraicClosure F) ℓ))
            let r := Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O))
            n ≠ ⊤ ∧ (ENat.toNat n : ℝ) * Real.log ℓ ≤ (ENat.toNat r : ℝ) *
              (-Real.log ‖(generalizedBernoulliDenominator f (i + 1) : PadicAlgCl ℓ) *
                primitiveBernoulliValue (i + 1)
                  (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ)‖)

/-- The inverse twist bound implies the comparison for each scalar-extended
minus eigenspace. -/
theorem selmerBernoulliCharacterLengthComparison_of_sharedTwist
    (h : HasSelmerSharedTwistBernoulliComparison) : HasSelmerBernoulliCharacterLengthComparison := by
  intro target ht e q d he hp i hi
  dsimp only
  intro ℓ _ hodd hdegree O _ _ _ ψ hψ
  let F := selmerHostField target e q d
  let _ : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  let _ : FaithfulSMul ℤ_[ℓ] O :=
    (faithfulSMul_iff_algebraMap_injective ℤ_[ℓ] O).mpr (padicSubalgebra_algebraMap_injective ℓ O)
  let _ : Module.Free ℤ_[ℓ] O := inferInstance
  have hlen := numberFieldSelmerMinusCharacterLength_le_sharedTwist F ℓ i O hdegree ψ
  have htw := h target ht e q d he hp i hi ℓ hodd hdegree O ψ hψ
  dsimp only at htw ⊢
  refine ⟨ne_top_of_le_ne_top htw.1 hlen, ?_⟩
  have hc := ENat.toNat_le_toNat hlen htw.1
  have hl : 0 ≤ Real.log (ℓ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le)
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hl).trans htw.2

/-- The shared-closure twist bound gives the Bernoulli valuation comparison
used by the prime-to-degree part of the minus estimate. -/
theorem selmerBernoulliValuationComparison_of_sharedTwist
    (h : HasSelmerSharedTwistBernoulliComparison) : HasSelmerBernoulliValuationComparison :=
  selmerBernoulliValuationComparison_of_characterLengths
    (selmerBernoulliCharacterLengthComparison_of_sharedTwist h)

end Riemann
