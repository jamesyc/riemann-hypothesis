module

public import Utilities.ArtinConjugation
import Utilities.ArtinSurjectivity
public import Utilities.CyclotomicPrimeSieve
public import Utilities.KrullConjugation

@[expose] public section

open NumberField
open scoped NumberField

namespace Utilities

variable (N : ℕ) [NeZero N] (E L : Type*) [Field E] [Field L] [NumberField E] [NumberField L]
  [IsCyclotomicExtension {N} ℚ E] [Algebra E L] [IsScalarTower ℚ E L]
  [Normal ℚ E] [FiniteDimensional E L] [IsAbelianGalois E L]

local notation "χ" => MulEquiv.symm (IsCyclotomicExtension.Rat.galEquivZMod N E)

/-- Principal-ideal reciprocity transfers weight-one annihilation
to the conjugates of an element of the unramified Galois group. -/
theorem cyclotomic_sum_smoothing_smul_artin_conjugates_eq_zero
    (hprincipal : ∀ x : Eˣ, numberFieldIdealArtin E L (toPrincipalIdeal (𝓞 E) E x) = 1)
    (hI : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ → ∀ σ ∈ P.inertia Gal(L/E), σ = 1)
    (lift : (ZMod N)ˣ → Gal(L/ℚ)) (hlift : ∀ b, (lift b).restrictNormal E = χ b)
    {X : Type*} [AddCommGroup X] (φ : Additive Gal(L/E) →+ X)
    (a : ℕ) (ha : a.Coprime N) (τ : Gal(L/E)) :
    ∑ b : (ZMod N)ˣ, smoothedWeightOneCoefficient a ha b •
      φ (Additive.ofMul (relativeGaloisConj ℚ E L (lift b).symm τ)) = 0 := by
  let Art := numberFieldClassGroupArtinOfPrincipal E L hprincipal
  obtain ⟨c, hc⟩ := numberFieldClassGroupArtinOfPrincipal_surjective E L hprincipal hI τ
  let R := numberFieldClassGroupGaloisAction ℚ E
  let ψ : Additive (ClassGroup (𝓞 E)) →+ X := φ.comp Art.toAdditive
  have hterm (b : (ZMod N)ˣ) :
      ψ (R (χ b)⁻¹ (Additive.ofMul c)) =
        φ (Additive.ofMul (relativeGaloisConj ℚ E L (lift b).symm τ)) := by
    let s := (lift b).symm
    have hs : s.restrictNormal E = (χ b)⁻¹ :=
      (map_inv (AlgEquiv.restrictNormalHom E) (lift b)).trans (congrArg Inv.inv (hlift b))
    let aE := (s.restrictNormal E).toRingEquiv
    let bL := s.toRingEquiv
    have hab (x : E) : bL (algebraMap E L x) = algebraMap E L (aE x) :=
      (s.restrictNormal_commutes E x).symm
    let γ := galoisMulEquivOfTowerRingEquiv aE bL hab
    have hArt : γ (Art c) = Art (classGroupMulEquivOfRingEquiv E E (RingOfIntegers.mapRingEquiv aE) c) :=
      DFunLike.congr_fun (numberFieldClassGroupArtinOfPrincipal_equivariant aE bL hab hprincipal hprincipal hI) c
    have hγ : γ τ = relativeGaloisConj ℚ E L s τ := by
      ext x
      rw [galoisMulEquivOfTowerRingEquiv_apply, relativeGaloisConj_apply]
      rfl
    have hconj := hArt.symm.trans ((congrArg γ hc).trans hγ)
    change Art (classGroupMulEquivOfRingEquiv E E
      (RingOfIntegers.mapRingEquiv (s.restrictNormal E).toRingEquiv) c) = _ at hconj
    rw [hs] at hconj
    exact congrArg (fun x => φ (Additive.ofMul x)) hconj
  have hzero := cyclotomicWeightOneClassAction_eq_zero E N a ha (Additive.ofMul c)
  change R.asAlgebraHom (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha) (Additive.ofMul c) = 0 at hzero
  rw [twistedWeightOneStickelberger, map_sum, LinearMap.sum_apply] at hzero
  simp only [pow_zero, mul_one, Representation.asAlgebraHom_single, LinearMap.smul_apply,
    MulEquiv.coe_toMonoidHom] at hzero
  have h := congrArg ψ hzero
  simpa only [map_sum, map_zsmul, hterm, map_zero] using h

end Utilities
