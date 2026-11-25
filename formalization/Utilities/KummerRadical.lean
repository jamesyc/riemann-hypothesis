module

public import Mathlib.FieldTheory.Galois.Infinite
public import Utilities.Hilbert90LocallyConstant
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open Filter
open scoped Topology

namespace Utilities

/-- A locally constant character of a Galois group factors through the
restriction to a finite normal intermediate field. -/
theorem exists_finiteGalois_factorization {K L A : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] [Group A] (χ : Gal(L/K) →* A)
    (hχ : IsLocallyConstant χ) :
    ∃ (E : IntermediateField K L) (_ : FiniteDimensional K E) (_ : Normal K E)
      (ψ : Gal(E/K) →* A), ∀ σ, ψ (σ.restrictNormal E) = χ σ := by
  have hker : (χ.ker : Set Gal(L/K)) ∈ 𝓝 1 :=
    (hχ.isOpen_fiber 1).mem_nhds (map_one χ)
  obtain ⟨E, hfin, hnormal, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K L _).mp hker
  let π : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hπ : π.ker ≤ χ.ker := by
    change (AlgEquiv.restrictNormalHom E (K₁ := L)).ker ≤ χ.ker
    rw [E.restrictNormalHom_ker]
    exact hE
  let e := QuotientGroup.quotientKerEquivOfSurjective π
    (AlgEquiv.restrictNormalHom_surjective L)
  let ψ := (QuotientGroup.lift π.ker χ hπ).comp e.symm.toMonoidHom
  refine ⟨E, hfin, hnormal, ψ, fun σ => ?_⟩
  have he : e (QuotientGroup.mk σ) = π σ := rfl
  change QuotientGroup.lift π.ker χ hπ (e.symm (π σ)) = χ σ
  rw [← he, MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]

/-- A locally constant cocycle with values in the nth roots of unity is
represented by a Kummer radical over the base field. -/
theorem exists_kummerRadical_of_locallyConstant_mulCocycle
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (f : Gal(L/K) → Lˣ) (hlc : IsLocallyConstant f) (hc : groupCohomology.IsMulCocycle₁ f)
    (n : ℕ) (hn : ∀ σ, f σ ^ n = 1) :
    ∃ (β : Lˣ) (a : Kˣ), (β : L) ^ n = algebraMap K L a ∧
      ∀ σ : Gal(L/K), σ (β : L) = (f σ : L) * (β : L) := by
  obtain ⟨β, hb⟩ := isMulCoboundary₁_of_locallyConstant f hlc hc
  have hβ (σ : Gal(L/K)) : σ (β : L) = (f σ : L) * (β : L) := by
    apply (div_eq_iff (Units.ne_zero β)).mp
    simpa only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass]
      using congrArg (fun u : Lˣ => (u : L)) (hb σ)
  have hfixed (σ : Gal(L/K)) : σ ((β : L) ^ n) = (β : L) ^ n := by
    have hroot : (f σ : L) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hn σ, Units.val_one]
    rw [map_pow, hβ, mul_pow, hroot, one_mul]
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed ((β : L) ^ n)).mpr hfixed
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact pow_ne_zero n (Units.ne_zero β) ha.symm
  exact ⟨β, Units.mk0 a ha0, ha.symm, hβ⟩

/-- A locally constant character taking values in the nth roots of unity
of the base field is represented by a Kummer radical. -/
theorem exists_kummerRadical_of_locallyConstant {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] (χ : Gal(L/K) →* Kˣ) (hχ : IsLocallyConstant χ)
    (n : ℕ) (hn : ∀ σ, χ σ ^ n = 1) :
    ∃ (β : Lˣ) (a : Kˣ), (β : L) ^ n = algebraMap K L a ∧
      ∀ σ : Gal(L/K), σ (β : L) = algebraMap K L (χ σ : K) * (β : L) := by
  let j := Units.map (algebraMap K L).toMonoidHom
  let f := j.comp χ
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro s t
    apply Units.ext
    change algebraMap K L (χ (s * t) : K) = s (algebraMap K L (χ t : K)) * algebraMap K L (χ s : K)
    rw [map_mul, Units.val_mul, map_mul, s.commutes, mul_comm]
  exact exists_kummerRadical_of_locallyConstant_mulCocycle f (hχ.comp j) hf n fun σ => by
    change j (χ σ) ^ n = 1
    rw [← map_pow, hn, map_one]

/-- Choosing a primitive root gives radical representatives for locally
constant `ZMod n`-valued characters. -/
theorem exists_kummerRadical_of_zmodCharacter {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (χ : Gal(L/K) →* Multiplicative (ZMod n)) (hχ : IsLocallyConstant χ) :
    ∃ (β : Lˣ) (a : Kˣ), (β : L) ^ n = algebraMap K L a ∧
      ∀ σ : Gal(L/K), σ (β : L) = (algebraMap K L ζ) ^ (Multiplicative.toAdd (χ σ)).val * (β : L) := by
  let u := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n := hζ.isUnit_unit (NeZero.ne n)
  let e : Multiplicative (ZMod n) ≃* Subgroup.zpowers u := hu.zmodEquivZPowers.symm.toMultiplicativeRight.symm
  let φ := (Subgroup.zpowers u).subtype.comp e.toMonoidHom
  have hφ (a : ZMod n) : (φ (Multiplicative.ofAdd a) : K) = ζ ^ a.val := by
    have hcast : ((a.val : ℕ) : ZMod n) = a := ZMod.natCast_zmod_val a
    have hpow := congrArg (fun v : Additive (Subgroup.zpowers u) => ((Additive.toMul v).val : K))
      (hu.zmodEquivZPowers_apply_natCast a.val)
    change ((hu.zmodEquivZPowers (a.val : ZMod n)).toMul.val : K) = ((u ^ a.val : Kˣ) : K) at hpow
    rw [hcast, Units.val_pow_eq_pow_val, (hζ.isUnit (NeZero.ne n)).unit_spec] at hpow
    exact hpow
  have hn (σ : Gal(L/K)) : (φ.comp χ) σ ^ n = 1 := by
    change (φ (χ σ)) ^ n = 1
    rw [← map_pow, show (χ σ) ^ n = 1 by
      change n • (Multiplicative.toAdd (χ σ)) = (0 : ZMod n)
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul], map_one]
  obtain ⟨β, a, hβ, hact⟩ := exists_kummerRadical_of_locallyConstant (φ.comp χ) (hχ.comp φ) n hn
  refine ⟨β, a, hβ, fun σ => ?_⟩
  have hc := hφ (Multiplicative.toAdd (χ σ))
  change (φ (χ σ) : K) = ζ ^ (Multiplicative.toAdd (χ σ)).val at hc
  rw [hact σ]
  change algebraMap K L (φ (χ σ) : K) * (β : L) = _
  rw [hc, map_pow]

/-- Multiplicative power classes of a field. -/
abbrev KummerPowerClass (K : Type*) [Field K] (n : ℕ) :=
  Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range

/-- Two radical representatives of the same power class have the same
character. Their quotient after scaling is a root of unity in the base field. -/
theorem zmodCharacter_eq_of_kummerPowerClass_eq {K L : Type*} [Field K] [Field L]
    [Algebra K L] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (χ ψ : Gal(L/K) →* Multiplicative (ZMod n)) (β γ : Lˣ) (a b : Kˣ)
    (ha : (β : L) ^ n = algebraMap K L a) (hb : (γ : L) ^ n = algebraMap K L b)
    (hχ : ∀ σ : Gal(L/K), σ (β : L) = (algebraMap K L ζ) ^ (Multiplicative.toAdd (χ σ)).val * (β : L))
    (hψ : ∀ σ : Gal(L/K), σ (γ : L) = (algebraMap K L ζ) ^ (Multiplicative.toAdd (ψ σ)).val * (γ : L))
    (hab : (QuotientGroup.mk a : KummerPowerClass K n) = QuotientGroup.mk b) : χ = ψ := by
  obtain ⟨c, hc⟩ := QuotientGroup.eq_iff_div_mem.mp hab
  change c ^ n = a / b at hc
  let i : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  have hβn : β ^ n = i a := Units.ext ha
  have hγn : γ ^ n = i b := Units.ext hb
  let δ := β / (γ * i c)
  have hδn : δ ^ n = 1 := by
    change (β / (γ * i c)) ^ n = 1
    rw [div_pow, mul_pow, hβn, hγn, ← map_pow, hc, ← map_mul]
    simp
  have hζL := hζ.map_of_injective (algebraMap K L).injective
  have hδn' : (δ : L) ^ n = 1 :=
    congrArg (fun u : Lˣ => (u : L)) hδn
  obtain ⟨j, _, hj⟩ := hζL.eq_pow_of_pow_eq_one hδn'
  have hδfix (σ : Gal(L/K)) : σ (δ : L) = (δ : L) := by
    rw [← hj, map_pow, σ.commutes]
  have hβrel : (δ : L) * ((γ : L) * algebraMap K L (c : K)) = (β : L) := by
    change ((β / (γ * i c) * (γ * i c) : Lˣ) : L) = (β : L)
    rw [div_mul_cancel]
  have hβψ (σ : Gal(L/K)) :
      σ (β : L) = (algebraMap K L ζ) ^ (Multiplicative.toAdd (ψ σ)).val * (β : L) := by
    conv_lhs => rw [← hβrel, map_mul, map_mul, hδfix, hψ, σ.commutes]
    rw [← hβrel]
    ring
  ext σ
  apply Multiplicative.toAdd.injective
  apply ZMod.val_injective n
  apply hζL.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact mul_right_cancel₀ (Units.ne_zero β) ((hχ σ).symm.trans (hβψ σ))

end Utilities
