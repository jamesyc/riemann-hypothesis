module

public import Utilities.CyclotomicJacobiIdeal
public import Utilities.RelativeFractionalIdealNorm
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Utilities.KummerClassGroup

@[expose] public section

open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace Utilities

variable {N q : ℕ} [NeZero N] [NeZero (q * N)]
  (K E : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]
  [Field E] [NumberField E] [IsCyclotomicExtension {q * N} ℚ E] [Algebra K E]

local notation "ρ" => ZMod.unitsMap (dvd_mul_left N q)
local notation "σ" => MulEquiv.symm (Rat.galEquivZMod (q * N) E)
local notation "τ" => MulEquiv.symm (Rat.galEquivZMod N K)

private theorem norm_cyclotomicConjugate (t : (ZMod (q * N))ˣ) (x : E) :
    Algebra.norm K (σ t x) = τ (ρ t) (Algebra.norm K x) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have : IsGalois ℚ E := IsCyclotomicExtension.isGalois {q * N} ℚ E
  have : IsGalois K E := IsGalois.tower_top_of_isGalois ℚ K E
  have hrestrict : (σ t).restrictNormal K = τ (ρ t) := by
    apply (Rat.galEquivZMod N K).injective
    rw [Rat.galEquivZMod_restrictNormal_apply (q * N) E K (dvd_mul_left N q),
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  apply (algebraMap K E).injective
  rw [← hrestrict, AlgEquiv.restrictNormal_commutes, Algebra.norm_eq_prod_automorphisms,
    Algebra.norm_eq_prod_automorphisms, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hcomm : g.restrictScalars ℚ * σ t = σ t * g.restrictScalars ℚ := by
    apply (Rat.galEquivZMod (q * N) E).injective
    simp only [map_mul]
    exact mul_comm _ _
  exact congrArg (fun f : Gal(E/ℚ) => f x) hcomm

private theorem nonzeroIdealNorm_cyclotomicInverseConjugate
    (t : (ZMod (q * N))ˣ) (I : (Ideal (𝓞 E))⁰) :
    numberFieldNonzeroIdealNorm K E (cyclotomicInverseConjugateIdeal (q * N) E t I) =
      cyclotomicInverseConjugateIdeal N K (ρ t) (numberFieldNonzeroIdealNorm K E I) := by
  let e := RingOfIntegers.mapRingEquiv ((σ t)⁻¹ : Gal(E/ℚ)).toRingEquiv
  let k := RingOfIntegers.mapRingEquiv ((τ (ρ t))⁻¹ : Gal(K/ℚ)).toRingEquiv
  have hnorm (x : 𝓞 E) :
      Algebra.intNorm (𝓞 K) (𝓞 E) (e x) = k (Algebra.intNorm (𝓞 K) (𝓞 E) x) := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [Algebra.algebraMap_intNorm (L := E)]
    change Algebra.norm K ((σ t)⁻¹ (x : E)) =
      (τ (ρ t))⁻¹ (algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 E) x))
    rw [Algebra.algebraMap_intNorm (L := E)]
    simpa only [map_inv] using norm_cyclotomicConjugate (N := N) (q := q) K E t⁻¹ (x : E)
  apply Subtype.ext
  change Ideal.relNorm (𝓞 K) (I.val.map e.toRingHom) =
    (Ideal.relNorm (𝓞 K) I.val).map k.toRingHom
  rw [Ideal.relNorm_apply, Ideal.map_relNorm (𝓞 K) I.val k.toRingHom]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv e z).mp hz
    exact ⟨x, hx, (hnorm x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, Ideal.mem_map_of_mem e hx, hnorm x⟩

/-- Norm of the signed Jacobi ideal at one auxiliary prime level, expressed as
a product at the lower level. The starting ideal need only be nonzero. -/
theorem numberFieldFractionalIdealNorm_cyclotomicJacobiIdeal
    (hq : q.Prime) {b : ℕ} (hb : b < q) (u : (ZMod N)ˣ) (hu : (u : ZMod N) = q)
    (I : (Ideal (𝓞 E))⁰) :
    numberFieldFractionalIdealNorm K E (cyclotomicJacobiIdeal (q * N) E b I) =
      ∏ t : (ZMod N)ˣ,
        (FractionalIdeal.mk0 K (cyclotomicInverseConjugateIdeal N K t
          (numberFieldNonzeroIdealNorm K E I))) ^
          (cyclotomicSignedFloor N b t.val - cyclotomicSignedFloor N b (u⁻¹ * t).val) := by
  classical
  let J (t : (ZMod N)ˣ) := FractionalIdeal.mk0 K
    (cyclotomicInverseConjugateIdeal N K t (numberFieldNonzeroIdealNorm K E I))
  simp only [cyclotomicJacobiIdeal, map_prod, map_zpow, numberFieldFractionalIdealNorm_mk0,
    nonzeroIdealNorm_cyclotomicInverseConjugate]
  change (∏ t : (ZMod (q * N))ˣ, J (ρ t) ^ cyclotomicSignedFloor (q * N) b t.val) =
    ∏ t : (ZMod N)ˣ, J t ^ (cyclotomicSignedFloor N b t.val -
      cyclotomicSignedFloor N b (u⁻¹ * t).val)
  have hpow (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (S : Finset (ZMod (q * N))ˣ) :
      (∏ x ∈ S, a ^ cyclotomicSignedFloor (q * N) b x.val) =
        a ^ (∑ x ∈ S, cyclotomicSignedFloor (q * N) b x.val) := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert x S hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, zpow_add, ih]
  rw [← Finset.prod_fiberwise Finset.univ ρ]
  refine Finset.prod_congr rfl fun t _ => ?_
  calc
    _ = ∏ x ∈ Finset.univ.filter (fun x => ρ x = t),
        J t ^ cyclotomicSignedFloor (q * N) b x.val := by
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by
      rw [hpow, cyclotomicSignedFloor_sum_fiber hq hb u t hu]

/-- The norm of an upper Jacobi generator and the lower generator divided by
its inverse Frobenius conjugate generate the same fractional ideal. -/
theorem cyclotomicJacobi_principalIdeal_norm_eq
    (hq : q.Prime) {b : ℕ} (hb : b < q) (u : (ZMod N)ˣ) (hu : (u : ZMod N) = q)
    (I : (Ideal (𝓞 E))⁰) (X' : Eˣ) (X : Kˣ)
    (hX' : toPrincipalIdeal (𝓞 E) E X' = cyclotomicJacobiIdeal (q * N) E b I)
    (hX : toPrincipalIdeal (𝓞 K) K X =
      cyclotomicJacobiIdeal N K b (numberFieldNonzeroIdealNorm K E I)) :
    toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K : E →* K) X') =
      toPrincipalIdeal (𝓞 K) K (X / Units.map ((τ u)⁻¹ : Gal(K/ℚ)).toRingEquiv.toMonoidHom X) := by
  rw [← numberFieldFractionalIdealNorm_principal, hX',
    numberFieldFractionalIdealNorm_cyclotomicJacobiIdeal K E hq hb u hu, map_div,
    ← cyclotomicInverseConjugatePrincipalIdeal, hX, cyclotomicInverseConjugateJacobiIdeal]
  let J (t : (ZMod N)ˣ) := FractionalIdeal.mk0 K
    (cyclotomicInverseConjugateIdeal N K t (numberFieldNonzeroIdealNorm K E I))
  have htranslate :
      (∏ t : (ZMod N)ˣ, J t ^ cyclotomicSignedFloor N b (u⁻¹ * t).val) =
        ∏ t : (ZMod N)ˣ, J (u * t) ^ cyclotomicSignedFloor N b t.val := by
    symm
    refine Fintype.prod_equiv (Equiv.mulLeft u) _ _ fun t => ?_
    simp
  change (∏ t : (ZMod N)ˣ, J t ^ (cyclotomicSignedFloor N b t.val -
      cyclotomicSignedFloor N b (u⁻¹ * t).val)) =
    (∏ t : (ZMod N)ˣ, J t ^ cyclotomicSignedFloor N b t.val) /
      ∏ t : (ZMod N)ˣ, J (u * t) ^ cyclotomicSignedFloor N b t.val
  simp only [zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib, div_eq_mul_inv, htranslate]

private theorem embedding_cyclotomic_negOne (φ : K →+* ℂ) (x : K) :
    φ (τ (-1) x) = starRingEnd ℂ (φ x) := by
  let ζ := zeta N ℚ K
  have hζ : IsPrimitiveRoot ζ N := zeta_spec N ℚ K
  have hroot : (φ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hnorm : ‖φ ζ‖ = 1 := by
    have h := congrArg norm hroot
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne N)).mp h
  have hinv : starRingEnd ℂ (φ ζ) = (φ ζ)⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
    simp
  have hgen : φ (τ (-1) ζ) = starRingEnd ℂ (φ ζ) := by
    rw [Rat.galEquivZMod_apply_of_pow_eq N K _ hζ.pow_eq_one,
      MulEquiv.apply_symm_apply, map_pow, hinv]
    have hdvd : N ∣ ((-1 : (ZMod N)ˣ) : ZMod N).val + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simp
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, hroot, one_pow]
  have hext := AlgHom.ext_of_adjoin_eq_top (R := ℚ) (adjoin_primitive_root_eq_top hζ)
    (φ₁ := (φ.comp (τ (-1)).toAlgHom.toRingHom).toRatAlgHom)
    (φ₂ := ((starRingEnd ℂ).comp φ).toRatAlgHom)
    (by rintro y hy; rw [Set.mem_singleton_iff] at hy; exact hy.symm ▸ hgen)
  exact DFunLike.congr_fun hext x

private theorem pow_eq_one_of_principalIdeal_eq_one
    (x : Kˣ) (hI : toPrincipalIdeal (𝓞 K) K x = 1)
    (hx : x * Units.map (τ (-1)).toRingEquiv.toMonoidHom x = 1) :
    x ^ (2 * N) = 1 := by
  obtain ⟨z, hz⟩ := exists_unit_of_principal_eq_one K x hI
  have hzval : ((z : 𝓞 K) : K) = (x : K) := congrArg (fun y : Kˣ => (y : K)) hz
  have htor : z ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.mem_torsion, InfinitePlace.eq_iff_eq]
    intro φ
    change ‖φ ((z : 𝓞 K) : K)‖ = 1
    rw [hzval]
    have h : φ (x : K) * starRingEnd ℂ (φ (x : K)) = 1 := by
      rw [← embedding_cyclotomic_negOne (N := N) K φ, ← map_mul]
      change φ ((x * Units.map (τ (-1)).toRingEquiv.toMonoidHom x : Kˣ) : K) = 1
      rw [hx, Units.val_one, map_one]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by exact_mod_cast h)
  have hpow : x ^ NumberField.Units.torsionOrder K = 1 := by
    rw [← hz, ← map_pow, NumberField.Units.pow_torsionOrder_eq_one K htor, map_one]
  have hdvd : NumberField.Units.torsionOrder K ∣ 2 * N := by
    rw [Rat.torsionOrder_eq (n := N)]
    split_ifs
    · exact dvd_mul_left N 2
    · exact dvd_rfl
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul, hpow, one_pow]

/-- The adjacent-level norm relation for Jacobi generators. The correction
is a root of unity of order dividing twice the lower conductor. -/
theorem cyclotomicJacobi_norm_eq_rootOfUnity_mul
    (hq : q.Prime) {b : ℕ} (hb : b < q) (u : (ZMod N)ˣ) (hu : (u : ZMod N) = q)
    (I : (Ideal (𝓞 E))⁰) (X' : Eˣ) (X : Kˣ)
    (hX' : toPrincipalIdeal (𝓞 E) E X' = cyclotomicJacobiIdeal (q * N) E b I)
    (hX : toPrincipalIdeal (𝓞 K) K X =
      cyclotomicJacobiIdeal N K b (numberFieldNonzeroIdealNorm K E I))
    (hX'bar : X' * Units.map (σ (-1)).toRingEquiv.toMonoidHom X' = 1)
    (hXbar : X * Units.map (τ (-1)).toRingEquiv.toMonoidHom X = 1) :
    ∃ ζ : Kˣ, ζ ^ (2 * N) = 1 ∧
      Units.map (Algebra.norm K : E →* K) X' =
        ζ * (X / Units.map ((τ u)⁻¹ : Gal(K/ℚ)).toRingEquiv.toMonoidHom X) := by
  let c := Units.map (τ (-1)).toRingEquiv.toMonoidHom
  let d := Units.map (σ (-1)).toRingEquiv.toMonoidHom
  let n := Units.map (Algebra.norm K : E →* K)
  let s := Units.map ((τ u)⁻¹ : Gal(K/ℚ)).toRingEquiv.toMonoidHom
  let Y := X / s X
  have hnorm : c (n X') = n (d X') := by
    apply Units.ext
    have h := norm_cyclotomicConjugate (N := N) (q := q) K E (-1) (X' : E)
    have hneg : ρ (-1) = -1 := by
      apply Units.ext
      rw [show (-1 : (ZMod (q * N))ˣ) = -(1 : (ZMod (q * N))ˣ) by rfl,
        ZMod.unitsMap_val, Units.val_neg, Units.val_one, ZMod.cast_neg (dvd_mul_left N q),
        ZMod.cast_one (dvd_mul_left N q)]
      rfl
    rw [hneg] at h
    exact h.symm
  have hconj : c (s X) = s (c X) := by
    apply Units.ext
    have hcomm : τ (-1) * (τ u)⁻¹ = (τ u)⁻¹ * τ (-1) := by
      apply (Rat.galEquivZMod N K).injective
      simp only [map_mul]
      exact mul_comm _ _
    exact congrArg (fun f : Gal(K/ℚ) => f (X : K)) hcomm
  have hn : n X' * c (n X') = 1 := by
    rw [hnorm, ← map_mul, show X' * d X' = 1 from hX'bar, map_one]
  have hY : Y * c Y = 1 := by
    change (X / s X) * c (X / s X) = 1
    rw [map_div, hconj, div_mul_div_comm, show X * c X = 1 from hXbar, ← map_mul,
      show X * c X = 1 from hXbar, map_one, div_one]
  let ζ := n X' / Y
  have hζI : toPrincipalIdeal (𝓞 K) K ζ = 1 := by
    have hI : toPrincipalIdeal (𝓞 K) K (n X') = toPrincipalIdeal (𝓞 K) K Y :=
      cyclotomicJacobi_principalIdeal_norm_eq K E hq hb u hu I X' X hX' hX
    change toPrincipalIdeal (𝓞 K) K (n X' / Y) = 1
    rw [map_div, hI, div_self']
  have hζ : ζ * c ζ = 1 := by
    change (n X' / Y) * c (n X' / Y) = 1
    rw [map_div, div_mul_div_comm, hn, hY, div_one]
  exact ⟨ζ, pow_eq_one_of_principalIdeal_eq_one K ζ hζI hζ, (div_mul_cancel _ _).symm⟩

end Utilities
