module

public import Riemann.SelmerGaloisAction
public import Utilities.CyclotomicArtinAnnihilation
public import Utilities.PadicCyclotomicRestriction
import Utilities.CyclotomicLayer
import Utilities.PadicTateFiniteRestriction

@[expose] public section

open Utilities NumberField

namespace Riemann

variable (F : Type) [Field F] [NumberField F] [Normal ℚ F]
variable (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)

local notation "Ω" => AlgebraicClosure F
local notation "A" => padicTateTwist F ℓ i
local notation "D" => numberFieldSelmerRestrictions F ℓ
local notation "ρ" => numberFieldSelmerGaloisAction F ℓ i

/-- Evaluate the host action on the cyclotomic kernel using a cocycle representative. -/
theorem padicTateSelmerRestriction_galoisAction_mk (s : Gal(Ω/ℚ))
    (c : (A).locallyTrivialCocycles₁ D) (σ : padicCyclotomicKernel F ℓ) :
    padicTateSelmerRestriction F ℓ i D (ρ (s.restrictNormal F) (Submodule.Quotient.mk c)) σ =
      padicTateScalarOnAut Ω ℓ i s.toRingEquiv •
        c.val (relativeGaloisConj ℚ F Ω s.symm σ.val) := by
  rw [numberFieldSelmerGaloisAction_restrictNormal]
  rfl

/-- Finite-level Artin reciprocity and weight-one annihilation kill the
restriction of the twisted Selmer action. The residue powers cancel the
Tate scalar on the bounded representative. -/
theorem padicTateSelmerRestriction_twistedWeightOne_eq_zero_of_artin
    (N : ℕ) [NeZero N] (E : IntermediateField F Ω) [NumberField E] [Normal ℚ E]
    [IsCyclotomicExtension {N} ℚ E] (T : FiniteGaloisIntermediateField E Ω)
    [NumberField T] [Normal ℚ T] [IsAbelianGalois E T]
    (r : ℕ) (hr : ℓ ^ r ∣ N) (c : (A).locallyTrivialCocycles₁ D) (hc : (ℓ : ℤ_[ℓ]) ^ r • c = 0)
    (φ : Additive Gal(T/E) →+ (A).rep)
    (hφ : ∀ g : Gal(Ω/E), φ (Additive.ofMul (g.restrictNormal T)) = c.val (g.restrictScalars F))
    (π : (ZMod N)ˣ →* Gal(F/ℚ)) (lift : (ZMod N)ˣ → Gal(Ω/ℚ))
    (hlift : ∀ b, (lift b).restrictNormal E = (IsCyclotomicExtension.Rat.galEquivZMod N E).symm b)
    (hπ : ∀ b, (π b)⁻¹ = (lift b).restrictNormal F)
    (a : ℕ) (ha : a.Coprime N)
    (σ : padicCyclotomicKernel F ℓ) (g : Gal(Ω/E)) (hg : g.restrictScalars F = σ.val)
    (hprincipal : ∀ x : Eˣ, numberFieldIdealArtin E T (toPrincipalIdeal (𝓞 E) E x) = 1)
    (hI : ∀ (P : Ideal (𝓞 T)) [P.IsPrime], P ≠ ⊥ → ∀ t ∈ P.inertia Gal(T/E), t = 1) :
    padicTateSelmerRestriction F ℓ i D
      (Representation.asAlgebraHom ρ (MonoidAlgebra.mapRingHom Gal(F/ℚ) (Int.castRingHom ℤ_[ℓ])
        (twistedWeightOneStickelberger π i a ha)) (Submodule.Quotient.mk c)) σ = 0 := by
  have hcval (τ : Field.absoluteGaloisGroup F) : (ℓ : ℤ_[ℓ]) ^ r • c.val τ = 0 :=
    congrFun (congrArg Subtype.val hc) τ
  let liftT (b : (ZMod N)ˣ) : Gal(T/ℚ) := (lift b).restrictNormal T
  have hliftT (b : (ZMod N)ˣ) :
      (liftT b).restrictNormal E = (IsCyclotomicExtension.Rat.galEquivZMod N E).symm b :=
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E T (lift b)).symm.trans (hlift b)
  have hroot (b : (ZMod N)ˣ) (ζ : Ω) (hζ : ζ ^ N = 1) :
      lift b ζ = ζ ^ b.val.val := by
    let z : E := ⟨ζ, mem_cyclotomicLayer_of_pow_eq_one N E hζ⟩
    have hz : z ^ N = 1 := (algebraMap E Ω).injective (by rw [map_pow, map_one]; exact hζ)
    change lift b (algebraMap E Ω z) = (algebraMap E Ω z) ^ b.val.val
    rw [← (lift b).restrictNormal_commutes E, hlift,
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq _ _ _ hz,
      MulEquiv.apply_symm_apply, map_pow]
  have hterm (b : (ZMod N)ˣ) :
      (b.val.val : ℤ_[ℓ]) ^ i •
        padicTateSelmerRestriction F ℓ i D (ρ (π b)⁻¹ (Submodule.Quotient.mk c)) σ =
      φ (Additive.ofMul (relativeGaloisConj ℚ E T (liftT b).symm (g.restrictNormal T))) := by
    rw [hπ, padicTateSelmerRestriction_galoisAction_mk]
    let τ : Field.absoluteGaloisGroup F := relativeGaloisConj ℚ F Ω (lift b).symm σ.val
    have hcancel : (b.val.val : ℤ_[ℓ]) ^ i • (padicTateScalarOnAut Ω ℓ i (lift b).toRingEquiv •
        c.val τ) = c.val τ :=
      natCast_pow_smul_padicTateScalarOnAut_eq_self_of_acts_on_roots ℓ Ω i r hr
        (lift b).toRingEquiv b.val.val (hroot b) (hcval τ)
    change (b.val.val : ℤ_[ℓ]) ^ i • (padicTateScalarOnAut Ω ℓ i (lift b).toRingEquiv •
      c.val τ) = _
    rw [hcancel]
    have hconj := relativeGaloisConj_restrictNormal ℚ E Ω (E := T) (lift b).symm g
    have hinv : (lift b).symm.restrictNormal T = (liftT b).symm :=
      map_inv (AlgEquiv.restrictNormalHom T) (lift b)
    rw [hinv] at hconj
    rw [← hconj, hφ, relativeGaloisConj_restrictScalars_of_tower, hg]
  have hzero := cyclotomic_sum_smoothing_smul_artin_conjugates_eq_zero N E T hprincipal hI
    liftT hliftT φ a ha (g.restrictNormal T)
  rw [twistedWeightOneStickelberger]
  simp only [map_sum, MonoidAlgebra.mapRingHom_single, Representation.asAlgebraHom_single,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, LinearMap.map_smul, Pi.smul_apply]
  refine Eq.trans (Finset.sum_congr rfl fun b _ => ?_) hzero
  change ((smoothedWeightOneCoefficient a ha b * (b.val.val : ℤ) ^ i : ℤ) : ℤ_[ℓ]) •
      padicTateSelmerRestriction F ℓ i D (ρ (π b)⁻¹ (Submodule.Quotient.mk c)) σ = _
  rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, mul_smul, hterm, Int.cast_smul_eq_zsmul]

end Riemann
