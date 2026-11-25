module

public import Riemann.SelmerTwistFrobeniusLength
public import Riemann.SelmerTwistResidual
import Utilities.PadicDVRValuation
import Utilities.GeneralizedBernoulliProducts
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

open Utilities IsDiscreteValuationRing

namespace Riemann

private theorem ofUnitHom_ringHomComp {R A K : Type*} [CommMonoidWithZero R]
    [CommRing A] [CommRing K] (j : A →+* K) (u : Rˣ →* Aˣ) :
    (MulChar.ofUnitHom u).ringHomComp j = MulChar.ofUnitHom ((Units.map j.toMonoidHom).comp u) := by
  apply MulChar.ext
  intro a
  rw [MulChar.ringHomComp_apply, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
  rfl

variable (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))

local notation "F" => selmerHostField target e q d
local notation "f" => selmerHostConductor target e q d
local instance : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d

variable (ψ : Gal((selmerHostField target e q d)/ℚ) →* Oˣ)

local notation "χ" => selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ

private theorem selmerDirichletOfCharacter_on_unit (u : (ZMod (selmerHostConductor target e q d))ˣ) :
    χ (u : ZMod f) = O.val (ψ (selmerHostConductorGalMap target e q d u) : O) :=
  MulChar.ofUnitHom_coe
    ((Units.map O.val.toRingHom.toMonoidHom).comp (ψ.comp (selmerHostConductorGalMap target e q d))) u

/-- The normalized primitive Bernoulli value, as an element of the coefficient
ring in which the Frobenius evaluations and their annihilators are defined. -/
noncomputable def selmerNormalizedPrimitiveBernoulli (k : ℕ) : O :=
  ⟨(generalizedBernoulliDenominator f k : PadicAlgCl ℓ) * primitiveBernoulliValue k χ, by
    let : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
    let θ : DirichletCharacter O f :=
      MulChar.ofUnitHom (ψ.comp (selmerHostConductorGalMap target e q d))
    have hθ : θ.ringHomComp O.toSubring.subtype = χ :=
      ofUnitHom_ringHomComp O.toSubring.subtype (ψ.comp (selmerHostConductorGalMap target e q d))
    have hm := normalized_primitiveBernoulliValue_ringHomComp_mem_subring O.toSubring k θ
    rw [hθ] at hm
    exact hm⟩

theorem selmerNormalizedPrimitiveBernoulli_ne_zero (hi : 1 ≤ i)
    (hψ : (ψ (selmerHostConductorGalMap target e q d (-1)) : O) = (-1 : O) ^ (i + 1)) :
    selmerNormalizedPrimitiveBernoulli target e q d ℓ O ψ (i + 1) ≠ 0 := by
  let : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let : NeZero (Monoid.exponent (ZMod f)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hpar : χ (-1) = (-1) ^ (i + 1) := by
    change χ ((-1 : (ZMod f)ˣ) : ZMod f) = _
    rw [selmerDirichletOfCharacter_on_unit, hψ, map_pow, map_neg, map_one]
  have hn := normalized_primitiveBernoulliValue_ne_zero (K := PadicAlgCl ℓ) (by omega) χ hpar
  exact fun h => hn (by simpa [selmerNormalizedPrimitiveBernoulli] using congrArg O.val h)

/-- A Frobenius budget dividing the coefficient-valued Bernoulli value gives
the normalized real length inequality used in the host comparison. -/
theorem selmerSharedTwistArithmeticBernoulliBound_of_frobeniusBudget
    [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O] (m : ℕ) (hi : 1 ≤ i)
    (hψ : (ψ (selmerHostConductorGalMap target e q d (-1)) : O) = (-1 : O) ^ (i + 1))
    (h : HasSharedTwistFrobeniusBudget target e q d ℓ i m O ψ
      (selmerNormalizedPrimitiveBernoulli target e q d ℓ O ψ (i + 1))) :
    SelmerSharedTwistArithmeticBernoulliBound target e q d ℓ i O ψ m := by
  let B := selmerNormalizedPrimitiveBernoulli target e q d ℓ O ψ (i + 1)
  have hB := selmerNormalizedPrimitiveBernoulli_ne_zero target e q d ℓ i O ψ hi hψ
  let : FaithfulSMul ℤ_[ℓ] O := (faithfulSMul_iff_algebraMap_injective ℤ_[ℓ] O).mpr
    (padicSubalgebra_algebraMap_injective ℓ O)
  have hlen := sharedTwist_arithmeticLayer_length_le_of_frobeniusBudget target e q d ℓ i m O ψ B hB h
  have hfinite : addVal O B ≠ ⊤ := addVal_eq_top_iff.not.mpr hB
  have hlog : 0 ≤ Real.log (ℓ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le)
  unfold SelmerSharedTwistArithmeticBernoulliBound
  refine ⟨ne_top_of_le_ne_top hfinite hlen, ?_⟩
  calc
    _ ≤ ((addVal O B).toNat : ℝ) * Real.log ℓ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast ENat.toNat_le_toNat hlen hfinite) hlog
    _ = _ := padicDVR_addVal_mul_log_eq ℓ O B hB

/-- The remaining arithmetic input for the noncyclotomic comparison.
At every nonzero reachable layer the next auxiliary prime supplies an
evaluation annihilator. The accumulated coefficient divides the normalized
Bernoulli value. -/
theorem selmer_noncyclotomic_frobeniusBudgets :
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i ≥ 1,
      let E := selmerHostField target e q d
      letI : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ¬ ℓ ∣ Module.finrank ℚ E →
        ∀ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))
          [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O]
          [HasEnoughRootsOfUnity O (Monoid.exponent (E ≃ₐ[ℚ] E))],
          ∀ ψ : (E ≃ₐ[ℚ] E) →* Oˣ,
            (ψ (selmerHostConductorGalMap target e q d (-1)) : O) = (-1 : O) ^ (i + 1) →
            (∃ g, IsUnit (sharedTwistCyclotomicDifference E ℓ i O ψ g)) →
            ∀ m : ℕ, HasSharedTwistFrobeniusBudget target e q d ℓ i m O ψ
              (selmerNormalizedPrimitiveBernoulli target e q d ℓ O ψ (i + 1)) := by
  sorry

end Riemann
