module

public import Riemann.SelmerTwistedBernoulli
public import Utilities.SelmerNormalizedLayers
public import Utilities.PadicTateConjugation

@[expose] public section

open Utilities DiscreteGaloisModule
open scoped TensorProduct

namespace Riemann

section SharedTwist

variable (F : Type) [Field F] [NumberField F] [IsAbelianGalois ℚ F]
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S]
  (ψ : Gal(F/ℚ) →* Sˣ)

local notation "Ω" => AlgebraicClosure F
local notation "T" => numberFieldSelmerSharedInverseTwist F ℓ i S ψ
local notation "D" => numberFieldSelmerRestrictionsIn ℚ Ω ℓ
local instance : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω

/-- Complex conjugation on the shared closure is the normalization element. -/
noncomputable def numberFieldTwistNormalizationElement : Gal(Ω/ℚ) :=
  algEquiv_complexConjugation Ω IsAlgClosed.lift

local notation "δ" => numberFieldTwistNormalizationElement F

/-- For the parity of the minus estimate, complex conjugation acts as
minus one on the inverse-character Tate coefficient module. -/
theorem numberFieldSelmerSharedInverseTwist_complexConjugation (hodd : ℓ ≠ 2)
    (hψ : (ψ ((δ).restrictNormal F) : S) = (-1 : S) ^ (i + 1)) :
    (T).rep.ρ δ = (-1 : S) • (1 : Module.End S (T).rep) := by
  have hψu : ψ ((δ).restrictNormal F) = (-1 : Sˣ) ^ (i + 1) := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using hψ
  have hψinv : (((ψ ((δ).restrictNormal F))⁻¹ : Sˣ) : S) = (-1 : S) ^ (i + 1) := by
    rw [hψu, ← inv_pow, inv_neg, inv_one, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have ht : padicTateScalarIn ℚ Ω ℓ i δ = (-1 : ℤ_[ℓ]) ^ i :=
    padicTateScalarOnAut_complexConjugation Ω IsAlgClosed.lift ℓ hodd i
  have hsign : (-1 : S) ^ (i + 1) * (-1 : S) ^ i = -1 := by
    rw [pow_succ, mul_right_comm ((-1 : S) ^ i) (-1) ((-1 : S) ^ i), ← mul_pow]
    simp
  rw [numberFieldSelmerSharedInverseTwist_ρ F ℓ i S ψ δ, hψinv, ht, map_pow, map_neg, map_one, hsign]

/-- The normalized bounded-exponent layer of the inverse twist on the common closure. -/
noncomputable def numberFieldSelmerSharedTwistLayer (r : ℕ) :
    Submodule S (normalizedSelmerCocycles T D δ) :=
  Submodule.torsionBy S (normalizedSelmerCocycles T D δ) ((ℓ : S) ^ r)

/-- The value of a global coboundary at the normalizing element determines
its coefficient witness. -/
theorem numberFieldSelmerSharedTwist_normalization_bijective (hodd : ℓ ≠ 2)
    (hψ : (ψ ((δ).restrictNormal F) : S) = (-1 : S) ^ (i + 1)) :
    Function.Bijective ((T).rep.ρ δ - 1 : Module.End S (T).rep) := by
  have htwo : IsUnit (2 : S) := by
    have hp : IsUnit (2 : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr
      ((PadicInt.norm_natCast_eq_one_iff (n := 2)).mpr
        ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hodd))
    simpa only [map_ofNat] using hp.map (algebraMap ℤ_[ℓ] S)
  have hu : IsUnit ((-1 : S) - 1) := by
    rw [show (-1 : S) - 1 = -2 by ring]
    exact htwo.neg
  exact subOne_bijective_of_scalar T δ (-1)
    (numberFieldSelmerSharedInverseTwist_complexConjugation F ℓ i S ψ hodd hψ) hu

/-- A uniform valuation bound for the normalized layers bounds the full
shared-closure twist length. -/
theorem numberFieldSelmerSharedTwist_log_bound_of_layers (hodd : ℓ ≠ 2)
    (hψ : (ψ ((δ).restrictNormal F) : S) = (-1 : S) ^ (i + 1))
    (K : ℝ)
    (h : ∀ r : ℕ,
      let n := Module.length S (numberFieldSelmerSharedTwistLayer F ℓ i S ψ r)
      n ≠ ⊤ ∧ (ENat.toNat n : ℝ) * Real.log ℓ ≤ K) :
    Module.length S ((T).selmerKernel D) ≠ ⊤ ∧
      ((Module.length S ((T).selmerKernel D)).toNat : ℝ) * Real.log ℓ ≤ K := by
  have hδ := numberFieldSelmerSharedTwist_normalization_bijective F ℓ i S ψ hodd hψ
  have hlog : 0 < Real.log (ℓ : ℝ) :=
    Real.log_pos (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt)
  exact selmerKernel_log_bound_of_normalized_torsionLayers T D δ hδ (ℓ : S)
    (exists_pow_smul_eq_zero_extendedPadicTate ℓ S) hlog K h

end SharedTwist

theorem numberFieldTwistNormalizationElement_restrictNormal_host
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+) :
    let F := selmerHostField target e q d
    letI : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
    (numberFieldTwistNormalizationElement F).restrictNormal F =
      selmerHostConductorGalMap target e q d (-1) := by
  dsimp only
  let F := selmerHostField target e q d
  let Ω := AlgebraicClosure F
  let _ : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  let _ : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω
  let ι : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  exact (algEquiv_complexConjugation_restrictNormal F Ω ι).trans
    (selmerHostConductorGalMap_neg_one_eq_conjugation target e q d (ι.domRestrict F)).symm

/-- The remaining uniform arithmetic inequality on normalized inverse-twist
cocycles killed by a power of the rational prime. -/
def HasSelmerSharedTwistLayerBernoulliComparison : Prop :=
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
            ∀ m : ℕ,
              let n := Module.length O (numberFieldSelmerSharedTwistLayer F ℓ i O ψ m)
              let r := Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O))
              n ≠ ⊤ ∧ (ENat.toNat n : ℝ) * Real.log ℓ ≤ (ENat.toNat r : ℝ) *
                (-Real.log ‖(generalizedBernoulliDenominator f (i + 1) : PadicAlgCl ℓ) *
                  primitiveBernoulliValue (i + 1)
                    (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ)‖)

/-- It suffices to prove the Bernoulli bound uniformly on the normalized
torsion layers of the shared-closure twists. -/
theorem selmerSharedTwistBernoulliComparison_of_normalizedLayers
    (h : HasSelmerSharedTwistLayerBernoulliComparison) : HasSelmerSharedTwistBernoulliComparison := by
  intro target ht e q d he hp i hi
  dsimp only
  intro ℓ _ hodd hdegree O _ _ _ ψ hψ
  let F := selmerHostField target e q d
  let _ : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  have hδ := numberFieldTwistNormalizationElement_restrictNormal_host target e q d
  apply numberFieldSelmerSharedTwist_log_bound_of_layers F ℓ i O ψ hodd
  · rw [hδ]
    exact hψ
  · exact h target ht e q d he hp i hi ℓ hodd hdegree O ψ hψ

end Riemann
