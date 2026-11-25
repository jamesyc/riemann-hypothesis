module

public import Utilities.CyclotomicSignedFloor
public import Utilities.WeightOneStickelbergerClassGroup

@[expose] public section

open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace Utilities

/-- The fractional ideal with the Jacobi signed floor exponents, indexed by
inverse conjugates of a nonzero ideal. -/
noncomputable def cyclotomicJacobiIdeal (N : ℕ) [NeZero N] (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {N} ℚ K] (b : ℕ) (I : (Ideal (𝓞 K))⁰) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  ∏ t : (ZMod N)ˣ, (FractionalIdeal.mk0 K (cyclotomicInverseConjugateIdeal N K t I)) ^
    cyclotomicSignedFloor N b t.val

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {N} ℚ K]

local notation "τ" => MulEquiv.symm (Rat.galEquivZMod N K)

/-- Transport a nonzero fractional ideal by the inverse of a cyclotomic automorphism. -/
noncomputable def cyclotomicInverseConjugateFractionalIdeal (u : (ZMod N)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ ≃* (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K
    (RingOfIntegers.mapRingEquiv ((τ u)⁻¹ : Gal(K/ℚ)).toRingEquiv))

/-- Conjugating an inverse conjugate shifts the product index. -/
theorem cyclotomicInverseConjugateFractionalIdeal_mk0 (u t : (ZMod N)ˣ) (I : (Ideal (𝓞 K))⁰) :
    cyclotomicInverseConjugateFractionalIdeal N K u
      (FractionalIdeal.mk0 K (cyclotomicInverseConjugateIdeal N K t I)) =
    FractionalIdeal.mk0 K (cyclotomicInverseConjugateIdeal N K (u * t) I) := by
  let e (s : (ZMod N)ˣ) := RingOfIntegers.mapRingEquiv ((τ s)⁻¹ : Gal(K/ℚ)).toRingEquiv
  have he : (e u).toRingHom.comp (e t).toRingHom = (e (u * t)).toRingHom := by
    refine RingHom.ext fun x => RingOfIntegers.ext ?_
    change (τ u)⁻¹ ((τ t)⁻¹ (x : K)) = (τ (u * t))⁻¹ (x : K)
    rw [← AlgEquiv.mul_apply, mul_comm u t, map_mul, mul_inv_rev]
  have hI := (cyclotomicInverseConjugateIdeal N K u (cyclotomicInverseConjugateIdeal N K t I)).property
  rw [cyclotomicInverseConjugateFractionalIdeal, fractionalIdealUnits_mapEquiv_mk0 K K (e u) _ hI]
  apply congrArg (FractionalIdeal.mk0 K)
  apply Subtype.ext
  change (I.val.map (e t).toRingHom).map (e u).toRingHom = I.val.map (e (u * t)).toRingHom
  rw [Ideal.map_map, he]

theorem cyclotomicInverseConjugateJacobiIdeal (b : ℕ) (u : (ZMod N)ˣ) (I : (Ideal (𝓞 K))⁰) :
    cyclotomicInverseConjugateFractionalIdeal N K u (cyclotomicJacobiIdeal N K b I) =
      ∏ t : (ZMod N)ˣ, (FractionalIdeal.mk0 K (cyclotomicInverseConjugateIdeal N K (u * t) I)) ^
        cyclotomicSignedFloor N b t.val := by
  simp only [cyclotomicJacobiIdeal, map_prod, map_zpow, cyclotomicInverseConjugateFractionalIdeal_mk0]

theorem cyclotomicInverseConjugatePrincipalIdeal (u : (ZMod N)ˣ) (x : Kˣ) :
    cyclotomicInverseConjugateFractionalIdeal N K u (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 K) K (Units.map ((τ u)⁻¹ : Gal(K/ℚ)).toRingEquiv.toMonoidHom x) := by
  let g := ((τ u)⁻¹ : Gal(K/ℚ)).toRingEquiv
  let e := RingOfIntegers.mapRingEquiv g
  have he : (IsFractionRing.ringEquivOfRingEquiv e : K ≃+* K).toRingHom = g.toRingHom := by
    apply IsLocalization.ringHom_ext (𝓞 K)⁰
    ext y
    change IsFractionRing.ringEquivOfRingEquiv e (algebraMap (𝓞 K) K y) =
      g (algebraMap (𝓞 K) K y)
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    rfl
  apply Units.ext
  change FractionalIdeal.ringEquivOfRingEquiv K K e ((toPrincipalIdeal (𝓞 K) K x).val) =
    (toPrincipalIdeal (𝓞 K) K (Units.map g.toMonoidHom x)).val
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton]
  exact congrArg (fun f : K →+* K => FractionalIdeal.spanSingleton (𝓞 K)⁰ (f (x : K))) he

end Utilities
