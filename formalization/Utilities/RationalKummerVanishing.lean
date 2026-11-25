module

public import Utilities.KummerClassGroup
public import Utilities.KummerValuation
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField FractionalIdeal IsDedekindDomain groupCohomology
open scoped NumberField nonZeroDivisors

namespace Utilities

/-- A rational unit whose prime ideal exponents are divisible by an odd
integer is a power of that degree. -/
theorem exists_rat_unit_pow_of_dvd_prime_exponents {n : ℕ} (hn : Odd n) (a : ℚˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), (n : ℤ) ∣ count ℚ v (toPrincipalIdeal (𝓞 ℚ) ℚ a).val) :
    ∃ b : ℚˣ, b ^ n = a := by
  let _ : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective
  let f := toPrincipalIdeal (𝓞 ℚ) ℚ
  obtain ⟨J, hJ⟩ := (numberFieldFractionalIdeal_mem_pow_range_iff ℚ n (f a)).mpr h
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal_iff J.val).mp inferInstance
  have hb₀ : b ≠ 0 := fun hzero => J.ne_zero (by simp [hzero] at hb)
  let d : ℚˣ := Units.mk0 b hb₀
  have hd : f d = J := by
    apply Units.ext
    change (toPrincipalIdeal (𝓞 ℚ) ℚ d).val = J.val
    rw [coe_toPrincipalIdeal]
    exact hb.symm
  have hp : f (a / d ^ n) = 1 := by
    rw [map_div, map_pow, hd, show J ^ n = f a from hJ, div_self']
  obtain ⟨u, hu⟩ := exists_unit_of_principal_eq_one ℚ _ hp
  have hfactor : (a : ℚ) = ((u.val : 𝓞 ℚ) : ℚ) * (d : ℚ) ^ n := by
    apply (div_eq_iff (pow_ne_zero _ d.ne_zero)).mp
    have he := congrArg (fun w : ℚˣ => (w : ℚ)) hu
    have hcoe : ((Units.map (algebraMap (𝓞 ℚ) ℚ).toMonoidHom u : ℚˣ) : ℚ) = (u.val : ℚ) := rfl
    rw [hcoe, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at he
    exact he.symm
  have hunit : Rat.ringOfIntegersEquiv u.val * Rat.ringOfIntegersEquiv (u⁻¹).val = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with hone | hneg
  · have he : u.val = 1 := Rat.ringOfIntegersEquiv.injective (by simpa only [map_one] using hone)
    exact ⟨d, Units.ext (by simpa only [he, map_one, one_mul, Units.val_pow_eq_pow_val] using hfactor.symm)⟩
  · have he : u.val = -1 := Rat.ringOfIntegersEquiv.injective (by simpa only [map_neg, map_one] using hneg)
    exact ⟨-d, Units.ext (by
      simpa only [he, map_neg, map_one, neg_one_mul, Units.val_pow_eq_pow_val, Units.val_neg, hn.neg_pow]
        using hfactor.symm)⟩

/-- A rational Kummer cocycle with trivial restrictions to inertia at one
prime above each rational prime is a coboundary in the roots of unity. -/
theorem exists_root_coboundary_of_rational_inertia_vanishing
    {L : Type} [Field L] [Algebra ℚ L] [IsGalois ℚ L]
    (f : Gal(L/ℚ) → Lˣ) (hlc : IsLocallyConstant f) (hc : IsMulCocycle₁ f)
    {n : ℕ} (hn : Odd n) (htors : ∀ σ, f σ ^ n = 1)
    (hI : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ P : Ideal (𝓞 L),
      P.IsPrime ∧ P.LiesOver v.asIdeal ∧ ∀ σ ∈ P.inertia Gal(L/ℚ), f σ = 1) :
    ∃ w : Lˣ, w ^ n = 1 ∧ ∀ σ : Gal(L/ℚ), σ • w / w = f σ := by
  obtain ⟨β, a, hβ, hact⟩ := exists_kummerRadical_of_locallyConstant_mulCocycle f hlc hc n htors
  have ha (v : HeightOneSpectrum (𝓞 ℚ)) :
      (n : ℤ) ∣ count ℚ v (toPrincipalIdeal (𝓞 ℚ) ℚ a).val := by
    obtain ⟨P, hP, hPv, hp⟩ := hI v
    let _ : P.IsPrime := hP
    let _ : P.LiesOver v.asIdeal := hPv
    exact dvd_principalPrimeExponent_of_inertia_fixed v P n (β : L) a hβ fun σ hσ => by
      rw [hact σ, hp σ hσ, Units.val_one, one_mul]
  obtain ⟨b, hb⟩ := exists_rat_unit_pow_of_dvd_prime_exponents hn a ha
  let d := Units.map (algebraMap ℚ L).toMonoidHom b
  refine ⟨β / d, ?_, fun σ => ?_⟩
  · apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_one]
    change ((β : L) / (algebraMap ℚ L (b : ℚ))) ^ n = 1
    have hb' : (b : ℚ) ^ n = (a : ℚ) := congrArg (fun u : ℚˣ => (u : ℚ)) hb
    rw [div_pow, hβ, ← map_pow, hb', div_self ((map_ne_zero (algebraMap ℚ L)).mpr a.ne_zero)]
  · apply Units.ext
    simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass]
    change σ ((β : L) / (algebraMap ℚ L (b : ℚ))) / ((β : L) / (algebraMap ℚ L (b : ℚ))) = (f σ : L)
    rw [map_div₀, hact σ, σ.commutes, mul_div_assoc, mul_div_cancel_right₀]
    exact div_ne_zero β.ne_zero ((map_ne_zero (algebraMap ℚ L)).mpr b.ne_zero)

/-- An unramified rational cocycle with cyclotomic action on `ZMod p`
has an explicit scalar coboundary. -/
theorem exists_zmod_coboundary_of_rational_inertia_vanishing
    {L : Type} [Field L] [Algebra ℚ L] [IsGalois ℚ L] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (η z : Gal(L/ℚ) → ZMod p) (hη : ∀ g, g ζ = ζ ^ (η g).val)
    (hlc : IsLocallyConstant z) (hc : ∀ g h, z (g * h) = η g * z h + z g)
    (hI : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ P : Ideal (𝓞 L),
      P.IsPrime ∧ P.LiesOver v.asIdeal ∧ ∀ σ ∈ P.inertia Gal(L/ℚ), z σ = 0) :
    ∃ w : ZMod p, ∀ g, z g = (η g - 1) * w := by
  have hp₀ := (Fact.out : p.Prime).ne_zero
  let u : Lˣ := (hζ.isUnit hp₀).unit
  have hu : (u : L) = ζ := (hζ.isUnit hp₀).unit_spec
  let f (g : Gal(L/ℚ)) : Lˣ := u ^ (z g).val
  have hfv (g) : (f g : L) = ζ ^ (z g).val := by
    change ((u ^ (z g).val : Lˣ) : L) = _
    rw [Units.val_pow_eq_pow_val, hu]
  have hmod (a b : ℕ) : ζ ^ a = ζ ^ b ↔ (a : ZMod p) = b := by
    rw [(hζ.isOfFinOrder hp₀).pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ZMod.natCast_eq_natCast_iff]
  have hf : IsMulCocycle₁ f := by
    intro g h
    apply Units.ext
    change (f (g * h) : L) = g (f h : L) * (f g : L)
    rw [hfv, hfv, hfv, map_pow, hη, ← pow_mul, ← pow_add]
    apply (hmod _ _).mpr
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hc]
  have htors (g) : f g ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hfv, pow_right_comm, hζ.pow_eq_one, one_pow, Units.val_one]
  have hI' : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ P : Ideal (𝓞 L),
      P.IsPrime ∧ P.LiesOver v.asIdeal ∧ ∀ σ ∈ P.inertia Gal(L/ℚ), f σ = 1 := by
    intro v
    obtain ⟨P, hP, hPv, hz⟩ := hI v
    exact ⟨P, hP, hPv, fun σ hσ => by simp [f, hz σ hσ, ZMod.val_zero]⟩
  obtain ⟨w, hw, hwf⟩ := exists_root_coboundary_of_rational_inertia_vanishing
    f (hlc.comp (fun v => u ^ v.val)) hf hp htors hI'
  have hwn : (w : L) ^ p = 1 := congrArg (fun x : Lˣ => (x : L)) hw
  obtain ⟨j, _, hj⟩ := hζ.eq_pow_of_pow_eq_one hwn
  refine ⟨(j : ZMod p), fun g => ?_⟩
  have he : g (w : L) = (f g : L) * (w : L) := by
    apply (div_eq_iff w.ne_zero).mp
    simpa only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass]
      using congrArg (fun x : Lˣ => (x : L)) (hwf g)
  rw [hfv, ← hj, map_pow, hη, ← pow_mul, ← pow_add] at he
  have h := (hmod _ _).mp he
  rw [Nat.cast_mul, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
  rw [sub_mul, one_mul, h, add_sub_cancel_right]

/-- A normalized rational cocycle with cyclotomic scalar action on
prime torsion vanishes if it vanishes on inertia at one prime above
each rational prime. -/
theorem rational_cyclotomic_nsmul_cocycle_eq_zero
    {L : Type} [Field L] [Algebra ℚ L] [IsGalois ℚ L] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (η : Gal(L/ℚ) → ZMod p) (hη : ∀ g, g ζ = ζ ^ (η g).val)
    {W : Type*} [AddCommGroup W] (hW : ∀ w : W, p • w = 0)
    (f : Gal(L/ℚ) → W) (hlc : IsLocallyConstant f)
    (hf : ∀ g h, f (g * h) = (η g).val • f h + f g)
    (hI : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ P : Ideal (𝓞 L),
      P.IsPrime ∧ P.LiesOver v.asIdeal ∧ ∀ σ ∈ P.inertia Gal(L/ℚ), f σ = 0)
    (t : Gal(L/ℚ)) (ht : η t ≠ 1) (hft : f t = 0) : f = 0 := by
  let _ : Module (ZMod p) W := AddCommGroup.zmodModule hW
  let B := Module.Basis.ofVectorSpace (ZMod p) W
  funext g
  apply B.repr.injective
  apply Finsupp.ext
  intro i
  let F : W →+ ZMod p := (B.coord i).toAddMonoidHom
  change F (f g) = F 0
  rw [map_zero]
  let z (g : Gal(L/ℚ)) := F (f g)
  have hz (s u : Gal(L/ℚ)) : z (s * u) = η s * z u + z s := by
    change F (f (s * u)) = η s * F (f u) + F (f s)
    rw [hf, map_add, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hIz (v : HeightOneSpectrum (𝓞 ℚ)) : ∃ P : Ideal (𝓞 L),
      P.IsPrime ∧ P.LiesOver v.asIdeal ∧ ∀ σ ∈ P.inertia Gal(L/ℚ), z σ = 0 := by
    obtain ⟨P, hP, hPv, hzP⟩ := hI v
    exact ⟨P, hP, hPv, fun σ hσ => by change F (f σ) = 0; rw [hzP σ hσ, map_zero]⟩
  obtain ⟨w, hw⟩ := exists_zmod_coboundary_of_rational_inertia_vanishing
    hp hζ η z hη (hlc.comp (fun w => F w)) hz hIz
  have hwt := hw t
  have hzero : z t = 0 := by change F (f t) = 0; rw [hft, map_zero]
  rw [hzero] at hwt
  have hw₀ := (mul_eq_zero.mp hwt.symm).resolve_left (sub_ne_zero.mpr ht)
  change z g = 0
  rw [hw, hw₀, mul_zero]

end Utilities
