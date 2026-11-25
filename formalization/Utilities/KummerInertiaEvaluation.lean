module

public import Utilities.KummerValuation
public import Utilities.KummerRadicalEquivariance
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
import Utilities.AbsoluteCyclotomicInertia
import Utilities.InertiaRestriction
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.Data.ZMod.Units

@[expose] public section

open NumberField IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors WithZero

namespace Utilities

/-- Inertia fixes a local unit whose inertia ratio is a root of unity
of order prime to the residue characteristic. -/
theorem inertia_fixes_local_unit_of_ratio_pow_eq_one
    {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 L)) {t : Gal(L/K)} (ht : t ∈ v.asIdeal.inertia Gal(L/K))
    {m : ℕ} (hm : (m : 𝓞 L) ∉ v.asIdeal)
    {x : L} (hx : v.valuation L x = 1) (hroot : (t x / x) ^ m = 1) :
    t x = x := by
  let P := v.asIdeal
  let _ : P.IsPrime := v.isPrime
  have hx₀ : x ≠ 0 := fun h => zero_ne_one (by simpa only [h, map_zero] using hx)
  have hm₀ : m ≠ 0 := fun h => hm (by simp [h])
  let ζ : 𝓞 L := ⟨t x / x, IsIntegral.of_pow (Nat.pos_of_ne_zero hm₀) (hroot ▸ isIntegral_one)⟩
  have hζ : ζ ^ m = 1 := RingOfIntegers.ext hroot
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hx.le
  have hb : v.intValuation b.val = 1 := (v.intValuation_eq_one_iff_mem_primeCompl b.val).mpr b.property
  have ha : a ∉ P := by
    apply (v.intValuation_eq_one_iff_mem_primeCompl a).mp
    rw [← v.valuation_of_algebraMap (K := L) a]
    change v.valuation L (algebraMap (𝓞 L) L a) = 1
    rw [← hab, map_mul, hx, v.valuation_of_algebraMap, hb, one_mul]
  have he : ζ * (t • b.val) * a = (t • a) * b.val := by
    apply RingOfIntegers.ext
    change (t x / x) * t (algebraMap (𝓞 L) L b.val) * algebraMap (𝓞 L) L a =
      t (algebraMap (𝓞 L) L a) * algebraMap (𝓞 L) L b.val
    rw [← hab, map_mul]
    calc
      _ = (t x / x * x) * t (algebraMap (𝓞 L) L b.val) * algebraMap (𝓞 L) L b.val := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hx₀]
  let q := Ideal.Quotient.mk P
  have hq (y : 𝓞 L) : q (t • y) = q y := Ideal.Quotient.eq.mpr ((Ideal.mem_inertia.mp ht) y)
  have hh := congrArg q he
  simp only [map_mul, hq] at hh
  have hqζ : q ζ = q 1 := by
    rw [map_one]
    have hb₀ : q b.val ≠ 0 := Ideal.Quotient.eq_zero_iff_mem.not.mpr b.property
    have ha₀ : q a ≠ 0 := Ideal.Quotient.eq_zero_iff_mem.not.mpr ha
    apply mul_right_cancel₀ (mul_ne_zero hb₀ ha₀)
    rw [one_mul, ← mul_assoc, hh, mul_comm]
  have hz := eq_of_pow_eq_one_of_sub_mem_prime P hm hζ (one_pow m) (Ideal.Quotient.eq.mp hqζ)
  exact (div_eq_one_iff_eq hx₀).mp (congrArg (fun u : 𝓞 L => (u : L)) hz)

/-- At a prime where the radicand has prime exponent one, inertia acts
on a prime-power radical by a primitive root of unity. -/
theorem exists_inertia_acts_on_primePower_radical
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    {ℓ r : ℕ} [Fact ℓ.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ (ℓ ^ (r + 1)))
    (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ)
    (ha : count K v (toPrincipalIdeal (𝓞 K) K a).val = 1)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal]
    {ρ : L} (hρ : ρ ^ (ℓ ^ (r + 1)) = algebraMap K L a) :
    ∃ t ∈ P.inertia Gal(L/K), t ρ = algebraMap K L ζ * ρ := by
  have hp : ℓ.Prime := Fact.out
  let M := ℓ ^ (r + 1)
  have hM : M ≠ 0 := pow_ne_zero _ hp.ne_zero
  let _ : NeZero M := ⟨hM⟩
  let z := algebraMap K L ζ
  have hz : IsPrimitiveRoot z M := hζ.map_of_injective (algebraMap K L).injective
  have hA : algebraMap K L (a : K) ≠ 0 :=
    (map_ne_zero (algebraMap K L)).mpr a.ne_zero
  have hρ₀ : ρ ≠ 0 := by
    intro h
    apply hA
    change ρ ^ M = algebraMap K L a at hρ
    simpa only [h, zero_pow hM] using hρ.symm
  have hratio (g : Gal(L/K)) : (g ρ / ρ) ^ M = 1 := by
    rw [div_pow, ← map_pow, show ρ ^ M = algebraMap K L a from hρ, g.commutes, div_self hA]
  have hroots (g : Gal(L/K)) (x : L) (hx : x ^ M = 1) : g x = x := by
    obtain ⟨i, _, rfl⟩ := hz.eq_pow_of_pow_eq_one hx
    change g ((algebraMap K L ζ) ^ i) = (algebraMap K L ζ) ^ i
    rw [map_pow, g.commutes]
  have hex : ∃ t ∈ P.inertia Gal(L/K), ∃ j : ℕ, ¬ ℓ ∣ j ∧ t ρ = z ^ j * ρ := by
    classical
    by_contra hnone
    have hfix (g : Gal(L/K)) (hg : g ∈ P.inertia Gal(L/K)) : g (ρ ^ (ℓ ^ r)) = ρ ^ (ℓ ^ r) := by
      obtain ⟨j, _, hj⟩ := hz.eq_pow_of_pow_eq_one (hratio g)
      have hact : g ρ = z ^ j * ρ := by rw [hj, div_mul_cancel₀ _ hρ₀]
      have hd : ℓ ∣ j := by
        by_contra hj
        exact hnone ⟨g, hg, j, hj, hact⟩
      have he : z ^ (j * ℓ ^ r) = 1 := (hz.pow_eq_one_iff_dvd _).mpr (by
        obtain ⟨k, hk⟩ := hd
        refine ⟨k, ?_⟩
        rw [hk, show M = ℓ ^ (r + 1) from rfl, pow_succ]
        ring)
      rw [map_pow, hact, mul_pow, ← pow_mul, he, one_mul]
    have hb : (ρ ^ (ℓ ^ r)) ^ ℓ = algebraMap K L a := by
      rw [← pow_mul, ← pow_succ, hρ]
    have hh := dvd_principalPrimeExponent_of_inertia_fixed v P ℓ (ρ ^ (ℓ ^ r)) a hb hfix
    rw [ha] at hh
    exact hp.ne_one (Nat.dvd_one.mp (by exact_mod_cast hh))
  obtain ⟨t, ht, j, hj, hact⟩ := hex
  have hcop : j.Coprime M := ((hp.coprime_iff_not_dvd.mpr hj).symm).pow_right _
  let b := ZMod.unitOfCoprime j hcop
  let k := (b⁻¹ : (ZMod M)ˣ).val.val
  have hmod : j * k ≡ 1 [MOD M] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [Nat.cast_mul, show (j : ZMod M) = b.val from (ZMod.coe_unitOfCoprime j hcop).symm]
    change b.val * (((b⁻¹ : (ZMod M)ˣ).val.val : ℕ) : ZMod M) = _
    rw [ZMod.natCast_zmod_val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Nat.cast_one]
  refine ⟨t ^ k, (P.inertia Gal(L/K)).pow_mem ht k, ?_⟩
  rw [algEquiv_pow_apply_radical_eq hρ₀ t (by
    rw [show ρ ^ M = algebraMap K L a from hρ, t.commutes]) (hroots t),
    hact, mul_div_cancel_right₀ _ hρ₀, ← pow_mul]
  have hpow : z ^ (j * k) = z ^ (1 : ℕ) := (hz.isOfFinOrder hM).pow_eq_pow_iff_modEq.mpr (by
    rw [← hz.eq_orderOf]
    exact hmod)
  rw [hpow, pow_one]

/-- A radical of a local unit is fixed by inertia when its exponent is
prime to the residue characteristic. -/
theorem inertia_fixes_radical_of_base_unit
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal]
    {m : ℕ} (hm₀ : m ≠ 0) (hm : (m : 𝓞 L) ∉ P)
    (a : Kˣ) (ha : v.valuation K (a : K) = 1)
    {x : L} (hx : x ^ m = algebraMap K L a)
    {t : Gal(L/K)} (ht : t ∈ P.inertia Gal(L/K)) : t x = x := by
  let C := FiniteGaloisIntermediateField.adjoin K ({x} : Set L)
  let E := C.toIntermediateField
  let _ : NumberField E := NumberField.of_module_finite K E
  let Q := P.under (𝓞 E)
  let _ : Q.IsPrime := inferInstanceAs (P.under (𝓞 E)).IsPrime
  let _ : Q.LiesOver v.asIdeal := ⟨(Ideal.over_def P v.asIdeal).trans (Ideal.under_under P).symm⟩
  let w : HeightOneSpectrum (𝓞 E) := ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  let y : E := ⟨x, FiniteGaloisIntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
  have hy : y ^ m = algebraMap K E a := Subtype.ext hx
  have hyv : w.valuation E y = 1 := by
    apply (pow_eq_one_iff_of_nonneg zero_le hm₀).mp
    rw [← map_pow, hy, ← HeightOneSpectrum.valuation_liesOver E v w, ha, one_pow]
  have hy₀ : y ≠ 0 := fun h => zero_ne_one (by simpa only [h, map_zero] using hyv)
  let t₀ := t.restrictNormal E
  have ht₀ : t₀ ∈ Q.inertia Gal(E/K) :=
    (numberField_inertia_map_restrictNormal_of_isGalois C P) ▸ Subgroup.mem_map_of_mem _ ht
  have hry : (t₀ y / y) ^ m = 1 := by
    rw [div_pow, ← map_pow, hy, t₀.commutes, div_self ((map_ne_zero (algebraMap K E)).mpr a.ne_zero)]
  have hmw : (m : 𝓞 E) ∉ Q := by
    intro h
    apply hm
    change algebraMap (𝓞 E) (𝓞 L) (m : 𝓞 E) ∈ P at h
    simpa only [map_natCast] using h
  have hfix := inertia_fixes_local_unit_of_ratio_pow_eq_one w ht₀ hmw hyv hry
  have he := congrArg (algebraMap E L) hfix
  change algebraMap E L (t.restrictNormal E y) = x at he
  rwa [t.restrictNormal_commutes] at he

/-- A normalized inertia element sends a Kummer radical to the primitive
root raised to the prime exponent of its radicand, times the radical. -/
theorem inertia_acts_on_radical_by_prime_exponent
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal]
    {m : ℕ} (hm₀ : m ≠ 0) (hm : (m : 𝓞 L) ∉ P)
    (a b : Kˣ) (hb : count K v (toPrincipalIdeal (𝓞 K) K b).val = 1)
    {β ρ ζ : L} (hβ : β ^ m = algebraMap K L a) (hρ : ρ ^ m = algebraMap K L b)
    {t : Gal(L/K)} (ht : t ∈ P.inertia Gal(L/K)) (htρ : t ρ = ζ * ρ) :
    t β = ζ ^ count K v (toPrincipalIdeal (𝓞 K) K a).val * β := by
  let k := count K v (toPrincipalIdeal (𝓞 K) K a).val
  let c := a / b ^ k
  let x := β / ρ ^ k
  have hv : v.valuation K (c : K) = 1 := by
    have h : v.valuationOfNeZero c = 1 := by
      apply Multiplicative.toAdd.injective
      change (v.valuationOfNeZero (a / b ^ k)).toAdd = 0
      rw [map_div, map_zpow]
      change (v.valuationOfNeZero a).toAdd - k • (v.valuationOfNeZero b).toAdd = 0
      rw [numberField_valuationOfNeZero_toAdd_eq_neg_count,
        numberField_valuationOfNeZero_toAdd_eq_neg_count, hb]
      change -k - k • (-1 : ℤ) = 0
      ring
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, h, WithZero.coe_one]
  have hx : x ^ m = algebraMap K L c := by
    have hr : (ρ ^ k) ^ m = algebraMap K L (b : K) ^ k := by
      rw [← zpow_natCast (ρ ^ k) m, ← zpow_mul, mul_comm k (m : ℤ), zpow_mul, zpow_natCast, hρ]
    change (β / ρ ^ k) ^ m = algebraMap K L ((a / b ^ k : Kˣ) : K)
    rw [div_pow, hβ, hr, Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, map_div₀, map_zpow₀]
  have hfix := inertia_fixes_radical_of_base_unit v P hm₀ hm c hv hx ht
  have hρ₀ : ρ ≠ 0 := by
    intro h
    apply (map_ne_zero (algebraMap K L)).mpr b.ne_zero
    rw [← hρ, h, zero_pow hm₀]
  have hxρ : x * ρ ^ k = β := div_mul_cancel₀ _ (zpow_ne_zero _ hρ₀)
  calc
    t β = t x * (t ρ) ^ k := by rw [← map_zpow₀, ← map_mul, hxρ]
    _ = ζ ^ k * β := by
      rw [hfix, htρ, mul_zpow, mul_left_comm, hxρ]

/-- A radical produces the additive Kummer character by reading its
ratio in primitive-root coordinates. -/
theorem exists_zmodCharacter_of_radical
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {m : ℕ} [NeZero m] {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (a : Kˣ) {β : L} (hβ : β ^ m = algebraMap K L a) :
    ∃ κ : Additive Gal(L/K) →+ ZMod m, IsLocallyConstant (fun g => κ (Additive.ofMul g)) ∧
      ∀ g : Gal(L/K), g β = (algebraMap K L ζ) ^ (κ (Additive.ofMul g)).val * β := by
  let z := algebraMap K L ζ
  have hz : IsPrimitiveRoot z m := hζ.map_of_injective (algebraMap K L).injective
  have ha : algebraMap K L (a : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr a.ne_zero
  have hβ₀ : β ≠ 0 := fun h => ha (by simpa only [h, zero_pow (NeZero.ne m)] using hβ.symm)
  have hr (g : Gal(L/K)) : (g β / β) ^ m = 1 := by
    rw [div_pow, ← map_pow, hβ, g.commutes, div_self ha]
  have hex (g : Gal(L/K)) : ∃ k : ZMod m, g β = z ^ k.val * β := by
    obtain ⟨j, hj, he⟩ := hz.eq_pow_of_pow_eq_one (hr g)
    refine ⟨j, ?_⟩
    rw [ZMod.val_natCast_of_lt hj, he, div_mul_cancel₀ _ hβ₀]
  classical
  choose k hk using hex
  have hzmod (i j : ℕ) : z ^ i = z ^ j ↔ (i : ZMod m) = j := by
    rw [(hz.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq, ← hz.eq_orderOf,
      ZMod.natCast_eq_natCast_iff]
  let κ : Additive Gal(L/K) →+ ZMod m :=
    { toFun := fun g => k g.toMul
      map_zero' := by
        have he := hk 1
        change β = z ^ (k 1).val * β at he
        have he' := mul_right_cancel₀ hβ₀ ((one_mul β).trans he)
        have h := (hzmod 0 (k 1).val).mp (by rw [pow_zero]; exact he')
        rw [toMul_zero]
        simpa only [Nat.cast_zero, ZMod.natCast_zmod_val] using h.symm
      map_add' := fun g h => by
        change k (g.toMul * h.toMul) = k g.toMul + k h.toMul
        have he := (hk (g.toMul * h.toMul)).symm
        change z ^ (k (g.toMul * h.toMul)).val * β = g.toMul (h.toMul β) at he
        rw [hk h.toMul, map_mul, map_pow] at he
        change z ^ (k (g.toMul * h.toMul)).val * β =
          (g.toMul (algebraMap K L ζ)) ^ (k h.toMul).val * g.toMul β at he
        rw [g.toMul.commutes, hk g.toMul, ← mul_assoc, ← pow_add] at he
        have hh := (hzmod _ _).mp (mul_right_cancel₀ hβ₀ he)
        rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, add_comm] at hh
        exact hh }
  have hβlc : IsLocallyConstant (fun g : Gal(L/K) => g β) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro g
    let H := MulAction.stabilizer Gal(L/K) β
    have hH : IsOpen (H : Set Gal(L/K)) := stabilizer_isOpen_of_isIntegral β
    let U : Set Gal(L/K) := (fun t => g⁻¹ * t) ⁻¹' H
    refine ⟨U, hH.preimage (continuous_const.mul continuous_id), ?_, fun t ht => ?_⟩
    · change g⁻¹ * g ∈ H
      rw [inv_mul_cancel]
      exact H.one_mem
    · have hfix : (g⁻¹ * t) β = β := ht
      change g.symm (t β) = β at hfix
      exact (g.apply_symm_apply (t β)).symm.trans (congrArg g hfix)
  have hfinj : Function.Injective (fun j : ZMod m => z ^ j.val * β) := by
    intro a b h
    exact (ZMod.val_injective m) (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (mul_right_cancel₀ hβ₀ h))
  have hκlc : IsLocallyConstant (fun g => κ (Additive.ofMul g)) := by
    apply IsLocallyConstant.desc _ (fun j : ZMod m => z ^ j.val * β) _ hfinj
    have he : (fun j : ZMod m => z ^ j.val * β) ∘ (fun g => κ (Additive.ofMul g)) =
        (fun g : Gal(L/K) => g β) := funext fun g => (hk g).symm
    rw [he]
    exact hβlc
  exact ⟨κ, hκlc, hk⟩

/-- A Kummer character has zero inertia value where its radicand has
prime exponent zero and its order is prime to the residue characteristic. -/
theorem zmodCharacter_eq_zero_on_inertia_of_prime_exponent_eq_zero
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    {m : ℕ} [NeZero m] {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (havoid : (m : 𝓞 L) ∉ P) (a : Kˣ)
    (ha : count K v (toPrincipalIdeal (𝓞 K) K a).val = 0)
    {β : L} (hβ : β ^ m = algebraMap K L a)
    (κ : Additive Gal(L/K) →+ ZMod m)
    (hκ : ∀ g : Gal(L/K), g β = (algebraMap K L ζ) ^ (κ (Additive.ofMul g)).val * β)
    (t : Gal(L/K)) (ht : t ∈ P.inertia Gal(L/K)) : κ (Additive.ofMul t) = 0 := by
  have hv : v.valuation K (a : K) = 1 := by
    have h : v.valuationOfNeZero a = 1 := by
      apply Multiplicative.toAdd.injective
      change (v.valuationOfNeZero a).toAdd = 0
      rw [numberField_valuationOfNeZero_toAdd_eq_neg_count, ha, neg_zero]
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, h, WithZero.coe_one]
  have hfix := inertia_fixes_radical_of_base_unit v P (NeZero.ne m) havoid a hv hβ ht
  have hβ₀ : β ≠ 0 := fun h =>
    ((map_ne_zero (algebraMap K L)).mpr a.ne_zero) (by simpa only [h, zero_pow (NeZero.ne m)] using hβ.symm)
  have hz := hζ.map_of_injective (algebraMap K L).injective
  apply ZMod.val_injective m
  rw [ZMod.val_zero]
  apply hz.pow_inj (ZMod.val_lt _) (NeZero.pos m)
  rw [pow_zero]
  apply mul_right_cancel₀ hβ₀
  rw [← hκ t, one_mul]
  exact hfix

/-- A Kummer character evaluated at the common normalized inertia
element gives the prime exponent of its radicand. -/
theorem zmodCharacter_inertia_value_eq_prime_exponent
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    {m : ℕ} [NeZero m] {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (havoid : (m : 𝓞 L) ∉ P)
    (a b : Kˣ) (hb : count K v (toPrincipalIdeal (𝓞 K) K b).val = 1)
    {β ρ : L} (hβ : β ^ m = algebraMap K L a) (hρ : ρ ^ m = algebraMap K L b)
    (t : Gal(L/K)) (ht : t ∈ P.inertia Gal(L/K)) (htρ : t ρ = algebraMap K L ζ * ρ)
    (κ : Additive Gal(L/K) →+ ZMod m)
    (hκ : ∀ g : Gal(L/K), g β = (algebraMap K L ζ) ^ (κ (Additive.ofMul g)).val * β) :
    κ (Additive.ofMul t) = (count K v (toPrincipalIdeal (𝓞 K) K a).val : ZMod m) := by
  have hm := NeZero.ne m
  have htβ := inertia_acts_on_radical_by_prime_exponent v P hm havoid a b hb hβ hρ ht htρ
  have hβ₀ : β ≠ 0 := fun h =>
    ((map_ne_zero (algebraMap K L)).mpr a.ne_zero) (by simpa only [h, zero_pow hm] using hβ.symm)
  let j := (κ (Additive.ofMul t)).val
  let k := count K v (toPrincipalIdeal (𝓞 K) K a).val
  let z := algebraMap K L ζ
  have hz : IsPrimitiveRoot z m := hζ.map_of_injective (algebraMap K L).injective
  have he : z ^ j = z ^ k := mul_right_cancel₀ hβ₀ ((hκ t).symm.trans htβ)
  have hd : (m : ℤ) ∣ k - (j : ℤ) := by
    apply (hz.zpow_eq_one_iff_dvd _).mp
    rw [zpow_sub₀ (hz.ne_zero hm), zpow_natCast, he, div_self (zpow_ne_zero _ (hz.ne_zero hm))]
  change κ (Additive.ofMul t) = (k : ZMod m)
  have hk := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mpr hd
  rw [Int.cast_natCast, ZMod.natCast_zmod_val] at hk
  exact hk

/-- For prime-power Kummer coefficients, the initial inertia value of
the character is exactly the prime exponent of the radicand. -/
theorem exists_zmodCharacter_with_inertia_value
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    {ℓ r : ℕ} [Fact ℓ.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ (ℓ ^ (r + 1)))
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (havoid : ((ℓ ^ (r + 1) : ℕ) : 𝓞 L) ∉ P)
    (a b : Kˣ) (hb : count K v (toPrincipalIdeal (𝓞 K) K b).val = 1)
    {β ρ : L} (hβ : β ^ (ℓ ^ (r + 1)) = algebraMap K L a) (hρ : ρ ^ (ℓ ^ (r + 1)) = algebraMap K L b) :
    ∃ t ∈ P.inertia Gal(L/K), ∃ κ : Additive Gal(L/K) →+ ZMod (ℓ ^ (r + 1)),
      IsLocallyConstant (fun g => κ (Additive.ofMul g)) ∧
      κ (Additive.ofMul t) = (count K v (toPrincipalIdeal (𝓞 K) K a).val : ZMod (ℓ ^ (r + 1))) ∧
      ∀ g : Gal(L/K), g β = (algebraMap K L ζ) ^ (κ (Additive.ofMul g)).val * β := by
  let m := ℓ ^ (r + 1)
  have hm : m ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  let _ : NeZero m := ⟨hm⟩
  obtain ⟨t, ht, htρ⟩ := exists_inertia_acts_on_primePower_radical hζ v b hb P hρ
  obtain ⟨κ, hκlc, hκ⟩ := exists_zmodCharacter_of_radical hζ a hβ
  exact ⟨t, ht, κ, hκlc, zmodCharacter_inertia_value_eq_prime_exponent hζ v P havoid a b hb
    hβ hρ t ht htρ κ hκ, hκ⟩

end Utilities
