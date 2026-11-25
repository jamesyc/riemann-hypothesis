module

public import Riemann.SelmerBernoulliCharacters
public import Utilities.SelmerBaseChange
import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open Utilities
open scoped IsMulCommutative TensorProduct

namespace Riemann

variable (F : Type) [Field F] [NumberField F] [IsAbelianGalois ℚ F]
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S]

local notation "Ω" => AlgebraicClosure F
local notation "A" => padicTateTwist F ℓ i
local notation "D" => numberFieldSelmerRestrictions F ℓ

/-- The lifted host action on Selmer classes with scalar-extended Tate
coefficients. -/
noncomputable def numberFieldSelmerScalarExtendedAmbientPullback (τ : Gal(Ω/ℚ)) :
    Module.End S (((A).baseChange S).selmerKernel D) :=
  (A).baseChangeSelmerPullback S D
    (relativeGaloisConj ℚ F Ω τ.symm) (relativeGaloisConj_continuous ℚ F Ω τ.symm)
    (padicTateScalarOnAut Ω ℓ i τ.toRingEquiv • LinearMap.id)
    (numberFieldSelmerAmbientCoefficient_intertwines F ℓ i τ)
    (numberFieldSelmerRestrictions_map_conj F ℓ τ.symm)

variable [Module.Free ℤ_[ℓ] S] [Module.Finite ℤ_[ℓ] S]

/-- Scalar extension of the actual host action agrees with conjugation
on cocycles with the scalar-extended Tate coefficients. -/
theorem numberFieldSelmerBaseChangeEquiv_restrictNormal (τ : Gal(Ω/ℚ))
    (x : S ⊗[ℤ_[ℓ]] (A).selmerKernel D) :
    (A).selmerBaseChangeEquiv S D
      ((numberFieldSelmerGaloisAction F ℓ i (τ.restrictNormal F)).baseChange S x) =
      numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ ((A).selmerBaseChangeEquiv S D x) := by
  rw [numberFieldSelmerGaloisAction_restrictNormal]
  exact (A).selmerBaseChangeEquiv_pullback S D
    (relativeGaloisConj ℚ F Ω τ.symm) (relativeGaloisConj_continuous ℚ F Ω τ.symm)
    (padicTateScalarOnAut Ω ℓ i τ.toRingEquiv • LinearMap.id)
    (numberFieldSelmerAmbientCoefficient_intertwines F ℓ i τ)
    (numberFieldSelmerRestrictions_map_conj F ℓ τ.symm) x

section SignEmbedding

variable (positive : Bool)

local notation "Mσ" => numberFieldSelmerSignPart positive F ℓ i

/-- Include the scalar extension of the sign submodule in the Selmer
kernel with scalar-extended coefficients. -/
noncomputable def numberFieldSelmerSignScalarEmbedding :
    S ⊗[ℤ_[ℓ]] (↥Mσ) →ₗ[S] ((A).baseChange S).selmerKernel D :=
  ((A).selmerBaseChangeEquiv S D).toLinearMap.comp ((Mσ).subtype.baseChange S)

theorem numberFieldSelmerSignScalarEmbedding_injective :
    Function.Injective (numberFieldSelmerSignScalarEmbedding F ℓ i S positive) :=
  ((A).selmerBaseChangeEquiv S D).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := S) (Mσ).subtype (Submodule.subtype_injective Mσ))

theorem numberFieldSelmerSignScalarEmbedding_restrictNormal (τ : Gal(Ω/ℚ))
    (x : S ⊗[ℤ_[ℓ]] (↥Mσ)) :
    numberFieldSelmerSignScalarEmbedding F ℓ i S positive
      (numberFieldSelmerSignBaseChangeAction F ℓ i S positive (τ.restrictNormal F) x) =
      numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ
        (numberFieldSelmerSignScalarEmbedding F ℓ i S positive x) := by
  let γ := τ.restrictNormal F
  let ρ := numberFieldSelmerGaloisAction F ℓ i γ
  let ρsign := numberFieldSelmerSignGaloisAction F ℓ i positive γ
  have hcomp : (Mσ).subtype.comp ρsign = ρ.comp (Mσ).subtype := rfl
  have hS := congrArg (fun f : (↥Mσ) →ₗ[ℤ_[ℓ]] (A).selmerKernel D => f.baseChange S) hcomp
  simp only [LinearMap.baseChange_comp] at hS
  change (A).selmerBaseChangeEquiv S D (((Mσ).subtype.baseChange S) ((ρsign.baseChange S) x)) =
    numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ
      ((A).selmerBaseChangeEquiv S D (((Mσ).subtype.baseChange S) x))
  have hx : ((Mσ).subtype.baseChange S) ((ρsign.baseChange S) x) =
      ρ.baseChange S (((Mσ).subtype.baseChange S) x) := DFunLike.congr_fun hS x
  rw [hx]
  exact numberFieldSelmerBaseChangeEquiv_restrictNormal F ℓ i S τ (((Mσ).subtype.baseChange S) x)

/-- A character eigenspace of the scalar-extended sign part embeds in the
same eigenspace of the action on the scalar-extended Tate coefficients. -/
theorem numberFieldSelmerSignScalarEmbedding_of_character
    (ψ : Gal(F/ℚ) →* Sˣ) (x : characterEigenspace
      (numberFieldSelmerSignBaseChangeAction F ℓ i S positive) ψ) (τ : Gal(Ω/ℚ)) :
    numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ
        (numberFieldSelmerSignScalarEmbedding F ℓ i S positive x.val) =
      (ψ (τ.restrictNormal F) : S) • numberFieldSelmerSignScalarEmbedding F ℓ i S positive x.val := by
  rw [← numberFieldSelmerSignScalarEmbedding_restrictNormal,
    mem_characterEigenspace.mp x.property _, map_smul]

end SignEmbedding

noncomputable abbrev numberFieldSelmerMinusScalarEmbedding :=
  numberFieldSelmerSignScalarEmbedding F ℓ i S false

theorem numberFieldSelmerMinusScalarEmbedding_injective :
    Function.Injective (numberFieldSelmerMinusScalarEmbedding F ℓ i S) :=
  numberFieldSelmerSignScalarEmbedding_injective F ℓ i S false

theorem numberFieldSelmerMinusScalarEmbedding_restrictNormal (τ : Gal(Ω/ℚ))
    (x : S ⊗[ℤ_[ℓ]] (↥(numberFieldSelmerMinusPart F ℓ i))) :
    numberFieldSelmerMinusScalarEmbedding F ℓ i S
      (numberFieldSelmerMinusBaseChangeAction F ℓ i S (τ.restrictNormal F) x) =
      numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ
        (numberFieldSelmerMinusScalarEmbedding F ℓ i S x) :=
  numberFieldSelmerSignScalarEmbedding_restrictNormal F ℓ i S false τ x

theorem numberFieldSelmerMinusScalarEmbedding_of_character
    (ψ : Gal(F/ℚ) →* Sˣ) (x : characterEigenspace
      (numberFieldSelmerMinusBaseChangeAction F ℓ i S) ψ) (τ : Gal(Ω/ℚ)) :
    numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ
        (numberFieldSelmerMinusScalarEmbedding F ℓ i S x.val) =
      (ψ (τ.restrictNormal F) : S) • numberFieldSelmerMinusScalarEmbedding F ℓ i S x.val :=
  numberFieldSelmerSignScalarEmbedding_of_character F ℓ i S false ψ x τ

/-- The ambient-lift character conditions on the Selmer kernel with
scalar-extended coefficients. -/
noncomputable def numberFieldSelmerScalarExtendedCharacterEigenspace (ψ : Gal(F/ℚ) →* Sˣ) :
    Submodule S (((A).baseChange S).selmerKernel D) :=
  ⨅ τ : Gal(Ω/ℚ), LinearMap.ker (numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ -
    (ψ (τ.restrictNormal F) : S) • LinearMap.id)

/-- The character lengths on either sign part are bounded by
the corresponding lengths for the Selmer kernel with extended coefficients. -/
theorem numberFieldSelmerSignCharacterLength_le (positive : Bool) (ψ : Gal(F/ℚ) →* Sˣ) :
    Module.length S (characterEigenspace (numberFieldSelmerSignBaseChangeAction F ℓ i S positive) ψ) ≤
      Module.length S (numberFieldSelmerScalarExtendedCharacterEigenspace F ℓ i S ψ) := by
  let C := characterEigenspace (numberFieldSelmerSignBaseChangeAction F ℓ i S positive) ψ
  let V := numberFieldSelmerScalarExtendedCharacterEigenspace F ℓ i S ψ
  let j := (numberFieldSelmerSignScalarEmbedding F ℓ i S positive).comp C.subtype
  have hj (x : C) : j x ∈ V := by
    change j x ∈ ⨅ τ : Gal(Ω/ℚ), LinearMap.ker
      (numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ -
        (ψ (τ.restrictNormal F) : S) • LinearMap.id)
    rw [Submodule.mem_iInf]
    intro τ
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    exact numberFieldSelmerSignScalarEmbedding_of_character F ℓ i S positive ψ x τ
  apply Module.length_le_of_injective (j.codRestrict V hj)
  intro x y h
  have hval : j x = j y := congrArg (fun v : V => v.val) h
  exact Subtype.ext (numberFieldSelmerSignScalarEmbedding_injective F ℓ i S positive hval)

theorem numberFieldSelmerMinusCharacterLength_le (ψ : Gal(F/ℚ) →* Sˣ) :
    Module.length S (characterEigenspace (numberFieldSelmerMinusBaseChangeAction F ℓ i S) ψ) ≤
      Module.length S (numberFieldSelmerScalarExtendedCharacterEigenspace F ℓ i S ψ) :=
  numberFieldSelmerSignCharacterLength_le F ℓ i S false ψ

end Riemann
