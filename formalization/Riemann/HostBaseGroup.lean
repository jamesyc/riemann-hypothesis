module

public import Riemann.SelmerWindows
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Utilities.FiniteFourier
import Utilities.ExponentialGrowth

@[expose] public section

open Utilities

namespace Riemann

abbrev SelmerHostBaseUnits (target : BundledDirichletCharacter) (e : ℕ) :=
  (ZMod (selmerBaseModulus target e))ˣ ⧸ selmerBaseFixingUnits target e

/-- The additive base factor `H` of Proposition 5.14. -/
abbrev SelmerHostBaseGroup (target : BundledDirichletCharacter) (e : ℕ) :=
  Additive (SelmerHostBaseUnits target e)

@[instance_reducible]
noncomputable def selmerHostBaseGroupFintype (target : BundledDirichletCharacter) (e : ℕ) :
    Fintype (SelmerHostBaseGroup target e) := by
  let _ : NeZero (selmerBaseModulus target e) := ⟨(selmerBaseModulus_pos target e).ne'⟩
  exact Fintype.ofFinite _

abbrev SelmerDyadicQuotient (e : ℕ) :=
  (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1)

def selmerDyadicMap (target : BundledDirichletCharacter) (e : ℕ) :
    (ZMod (selmerBaseModulus target e))ˣ →* SelmerDyadicQuotient e :=
  (QuotientGroup.mk' _).comp (ZMod.unitsMap (Nat.dvd_lcm_left _ _))

noncomputable def selmerTargetUnitMap (target : BundledDirichletCharacter) (e : ℕ) :
    (ZMod (selmerBaseModulus target e))ˣ →* ℂˣ :=
  target.character.toUnitHom.comp (ZMod.unitsMap (Nat.dvd_lcm_right _ _))

theorem selmerBaseFixingUnits_eq_ker (target : BundledDirichletCharacter) (e : ℕ) :
    selmerBaseFixingUnits target e = ((selmerDyadicMap target e).prod (selmerTargetUnitMap target e)).ker := by
  rw [MonoidHom.ker_prod]
  unfold selmerBaseFixingUnits selmerDyadicMap selmerTargetUnitMap
  simp only [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

set_option backward.isDefEq.respectTransparency false in
/-- The faithful pair of maps from the base factor to the dyadic quotient
and the values of the target character. -/
noncomputable def selmerBaseCombinedMap (target : BundledDirichletCharacter) (e : ℕ) :
    SelmerHostBaseUnits target e →* (SelmerDyadicQuotient e × ℂˣ) :=
  QuotientGroup.lift (M := SelmerDyadicQuotient e × ℂˣ) (selmerBaseFixingUnits target e)
    ((selmerDyadicMap target e).prod (selmerTargetUnitMap target e))
    (selmerBaseFixingUnits_eq_ker target e).le

set_option backward.isDefEq.respectTransparency false in
theorem selmerBaseCombinedMap_injective (target : BundledDirichletCharacter) (e : ℕ) :
    Function.Injective (selmerBaseCombinedMap target e) := by
  unfold selmerBaseCombinedMap
  exact (QuotientGroup.injective_lift_iff (M := SelmerDyadicQuotient e × ℂˣ)
    (selmerBaseFixingUnits target e)
    ((selmerDyadicMap target e).prod (selmerTargetUnitMap target e)) _).mpr
    (selmerBaseFixingUnits_eq_ker target e)

/-- The dyadic coordinate of Proposition 5.14(iii). -/
noncomputable def selmerBaseDyadicReduction (target : BundledDirichletCharacter) (e : ℕ) :
    SelmerHostBaseUnits target e →* SelmerDyadicQuotient e :=
  (MonoidHom.fst (SelmerDyadicQuotient e) ℂˣ).comp (selmerBaseCombinedMap target e)

/-- The descended target character on the base group. -/
noncomputable def selmerBaseTarget (target : BundledDirichletCharacter) (e : ℕ) :
    SelmerHostBaseUnits target e →* ℂˣ :=
  (MonoidHom.snd (SelmerDyadicQuotient e) ℂˣ).comp (selmerBaseCombinedMap target e)

@[simp] theorem selmerBaseTarget_mk (target : BundledDirichletCharacter) (e : ℕ)
    (u : (ZMod (selmerBaseModulus target e))ˣ) :
    selmerBaseTarget target e (QuotientGroup.mk u) = selmerTargetUnitMap target e u := rfl

theorem selmerBaseDyadicReduction_surjective (target : BundledDirichletCharacter) (e : ℕ) :
    Function.Surjective (selmerBaseDyadicReduction target e) := by
  let _ : NeZero (selmerBaseModulus target e) :=
    ⟨(selmerBaseModulus_pos target e).ne'⟩
  have hdvd : 2 ^ (e + 2) ∣ selmerBaseModulus target e := Nat.dvd_lcm_left _ _
  intro z
  obtain ⟨u, hu⟩ := (QuotientGroup.mk'_surjective _).comp
    (ZMod.unitsMap_surjective hdvd) z
  exact ⟨QuotientGroup.mk u, hu⟩

/-- The averaging subgroup `A₀` is the kernel of the descended target character. -/
noncomputable def selmerAveragingSubgroup (target : BundledDirichletCharacter) (e : ℕ) :
    AddSubgroup (SelmerHostBaseGroup target e) :=
  (selmerBaseTarget target e).ker.toAddSubgroup

theorem selmerBaseDyadicReduction_injOn_targetKernel
    (target : BundledDirichletCharacter) (e : ℕ) :
    Set.InjOn (selmerBaseDyadicReduction target e) (selmerBaseTarget target e).ker := by
  intro u hu v hv heq
  have hu₁ : selmerBaseTarget target e u = 1 := hu
  have hv₁ : selmerBaseTarget target e v = 1 := hv
  apply selmerBaseCombinedMap_injective target e
  exact Prod.ext heq (hu₁.trans hv₁.symm)

theorem selmerAveragingSubgroup_isAddCyclic (target : BundledDirichletCharacter) (e : ℕ) :
    IsAddCyclic (selmerAveragingSubgroup target e) := by
  have h : IsCyclic (selmerBaseTarget target e).ker := by
    apply isCyclic_of_injective ((selmerBaseDyadicReduction target e).comp
      (selmerBaseTarget target e).ker.subtype)
    intro u v huv
    exact Subtype.ext (selmerBaseDyadicReduction_injOn_targetKernel target e u.property v.property huv)
  change IsAddCyclic (Additive ((selmerBaseTarget target e).ker))
  exact isAddCyclic_additive_iff.mpr h

theorem selmerBaseTarget_range (target : BundledDirichletCharacter) (e : ℕ) :
    (selmerBaseTarget target e).range = target.character.toUnitHom.range := by
  let _ : NeZero (selmerBaseModulus target e) :=
    ⟨(selmerBaseModulus_pos target e).ne'⟩
  have hdvd : (target.modulus : ℕ) ∣ selmerBaseModulus target e := Nat.dvd_lcm_right _ _
  apply SetLike.ext
  intro w
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
    rw [selmerBaseTarget_mk]
    exact ⟨ZMod.unitsMap hdvd v, rfl⟩
  · rintro ⟨u, hu⟩
    obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hdvd u
    refine ⟨QuotientGroup.mk v, ?_⟩
    rw [selmerBaseTarget_mk]
    change target.character.toUnitHom (ZMod.unitsMap hdvd v) = w
    rwa [hv]

theorem selmerBaseTarget_range_card (target : BundledDirichletCharacter) (e : ℕ) :
    Nat.card (selmerBaseTarget target e).range = orderOf target.character := by
  let _ : NeZero (target.modulus : ℕ) := ⟨target.modulus.pos.ne'⟩
  rw [selmerBaseTarget_range, card_dirichletCharacter_unit_range]

/-- The index of `A₀` is the order of the original character. -/
theorem selmerAveragingSubgroup_index (target : BundledDirichletCharacter) (e : ℕ) :
    (selmerAveragingSubgroup target e).index = orderOf target.character := by
  rw [selmerAveragingSubgroup, Subgroup.index_toAddSubgroup, Subgroup.index_ker,
    selmerBaseTarget_range_card]

/-- The characters of the base factor that are trivial on `A₀` are powers
of the target character, as in Proposition 5.14(iv). -/
theorem selmerBaseCharacter_eq_pow_of_averagingSubgroup
    (target : BundledDirichletCharacter) (e : ℕ)
    (χ : AddChar (SelmerHostBaseGroup target e) ℂ)
    (hχ : ∀ u ∈ selmerAveragingSubgroup target e, χ u = 1) :
    ∃ i < orderOf target.character, ∀ u : SelmerHostBaseGroup target e,
      χ u = (selmerBaseTarget target e u.toMul : ℂ) ^ i := by
  let _ : NeZero (selmerBaseModulus target e) := ⟨(selmerBaseModulus_pos target e).ne'⟩
  let φ : SelmerHostBaseUnits target e →* ℂ :=
    { toFun := fun u => χ (Additive.ofMul u)
      map_one' := χ.map_zero_eq_one
      map_mul' := fun u v => χ.map_add_eq_mul (Additive.ofMul u) (Additive.ofMul v) }
  have hker : (selmerBaseTarget target e).ker ≤ φ.ker := by
    intro u hu
    exact hχ (Additive.ofMul u) hu
  obtain ⟨i, hi, hpow⟩ := character_eq_pow_of_ker_le (selmerBaseTarget target e) φ hker
  exact ⟨i, hi.trans_eq (selmerBaseTarget_range_card target e), fun u => hpow u.toMul⟩

theorem selmerDyadicQuotient_card (e : ℕ) : Nat.card (SelmerDyadicQuotient e) = 2 ^ e := by
  let r := (2 : ℕ) ^ (e + 2)
  have hfour : 4 ≤ r := by
    change (2 : ℕ) ^ 2 ≤ 2 ^ (e + 2)
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  let _ : NeZero r := ⟨by omega⟩
  let _ : Nontrivial (ZMod r) := ZMod.nontrivial_iff.mpr (by omega)
  have horder : orderOf (-1 : (ZMod r)ˣ) = 2 := by
    rw [Units.orderOf_neg_one, ZMod.ringChar_zmod_n, ite_eq_right (by omega : r ≠ 2)]
  have htotal : Nat.card (ZMod r)ˣ = 2 ^ (e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    change (2 ^ ((e + 1) + 1)).totient = _
    simp [Nat.totient_prime_pow_succ Nat.prime_two]
  have hsize := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (-1 : (ZMod r)ˣ))
  rw [htotal, Nat.card_zpowers, horder, pow_succ] at hsize
  exact (Nat.mul_right_cancel (by decide : 0 < 2) hsize).symm

/-- The dyadic degree formula in Proposition 5.14(iii). -/
theorem selmerHostBaseGroup_card (target : BundledDirichletCharacter) (e : ℕ) :
    Nat.card (SelmerHostBaseGroup target e) =
      Nat.card (selmerBaseDyadicReduction target e).ker * 2 ^ e := by
  have h := Subgroup.card_ker_mul_card_of_surjective
    (selmerBaseDyadicReduction_surjective target e)
  rw [selmerDyadicQuotient_card] at h
  exact h.symm

private theorem selmerBaseDyadicKernel_card_eq_target_range
    (target : BundledDirichletCharacter) (e : ℕ) :
    Nat.card (selmerBaseDyadicReduction target e).ker =
      Nat.card ((selmerBaseTarget target e).comp (selmerBaseDyadicReduction target e).ker.subtype).range := by
  let K := (selmerBaseDyadicReduction target e).ker
  let f := (selmerBaseTarget target e).comp K.subtype
  have hf : Function.Injective f := by
    intro u v heq
    apply Subtype.ext
    apply selmerBaseCombinedMap_injective target e
    have hu : selmerBaseDyadicReduction target e u = 1 := u.property
    have hv : selmerBaseDyadicReduction target e v = 1 := v.property
    exact Prod.ext (hu.trans hv.symm) heq
  exact Nat.card_congr (Equiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩)

theorem selmerBaseDyadicReduction_card_ker_dvd_order (target : BundledDirichletCharacter) (e : ℕ) :
    Nat.card (selmerBaseDyadicReduction target e).ker ∣ orderOf target.character := by
  let f := (selmerBaseTarget target e).comp (selmerBaseDyadicReduction target e).ker.subtype
  have hsubset : f.range ≤ (selmerBaseTarget target e).range := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  rw [selmerBaseDyadicKernel_card_eq_target_range, ← selmerBaseTarget_range_card target e]
  exact Subgroup.card_dvd_of_le hsubset

/-- Lowering the dyadic level can only enlarge the target values that are
compatible with a trivial dyadic coordinate. -/
theorem selmerBaseDyadicReduction_card_ker_antitone (target : BundledDirichletCharacter) :
    Antitone (fun e => Nat.card (selmerBaseDyadicReduction target e).ker) := by
  intro e e' he
  let rel (n : ℕ) := (selmerBaseTarget target n).comp (selmerBaseDyadicReduction target n).ker.subtype
  have hcard (n : ℕ) :
      Nat.card (selmerBaseDyadicReduction target n).ker = Nat.card (rel n).range :=
    selmerBaseDyadicKernel_card_eq_target_range target n
  change Nat.card (selmerBaseDyadicReduction target e').ker ≤
    Nat.card (selmerBaseDyadicReduction target e).ker
  rw [hcard, hcard]
  have hle : (rel e').range ≤ (rel e).range := by
    rintro z ⟨⟨u, hu⟩, rfl⟩
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
    have hpow : (2 : ℕ) ^ (e + 2) ∣ 2 ^ (e' + 2) := pow_dvd_pow 2 (by omega)
    have hdiv : selmerBaseModulus target e ∣ selmerBaseModulus target e' :=
      Nat.lcm_dvd_lcm_of_dvd_left _ hpow
    let w := ZMod.unitsMap hdiv v
    have hsmall : (2 : ℕ) ^ (e + 2) ∣ selmerBaseModulus target e := Nat.dvd_lcm_left _ _
    have hbig : (2 : ℕ) ^ (e' + 2) ∣ selmerBaseModulus target e' := Nat.dvd_lcm_left _ _
    have hv : ZMod.unitsMap hbig v ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (e' + 2)))ˣ) := by
      change (QuotientGroup.mk (ZMod.unitsMap hbig v) :
        (ZMod (2 ^ (e' + 2)))ˣ ⧸ Subgroup.zpowers (-1)) = 1 at hu
      exact (QuotientGroup.eq_one_iff _).mp hu
    have hw : QuotientGroup.mk w ∈ (selmerBaseDyadicReduction target e).ker := by
      change (QuotientGroup.mk (ZMod.unitsMap hsmall w) :
        (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1)) = 1
      rw [QuotientGroup.eq_one_iff]
      have heq : ZMod.unitsMap hsmall w = ZMod.unitsMap hpow (ZMod.unitsMap hbig v) := by
        dsimp only [w]
        rw [zmodUnitsMap_comp_apply, zmodUnitsMap_comp_apply]
      rw [heq]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hv
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      rw [← hn, map_zpow, zmodUnitsMap_neg_one]
    refine ⟨⟨QuotientGroup.mk w, hw⟩, ?_⟩
    change selmerBaseTarget target e (QuotientGroup.mk w) = selmerBaseTarget target e' (QuotientGroup.mk v)
    rw [selmerBaseTarget_mk, selmerBaseTarget_mk]
    have ht : (target.modulus : ℕ) ∣ selmerBaseModulus target e := Nat.dvd_lcm_right _ _
    have ht' : (target.modulus : ℕ) ∣ selmerBaseModulus target e' := Nat.dvd_lcm_right _ _
    change target.character.toUnitHom (ZMod.unitsMap ht w) =
      target.character.toUnitHom (ZMod.unitsMap ht' v)
    exact congrArg target.character.toUnitHom (zmodUnitsMap_comp_apply ht hdiv v)
  let _ : NeZero (selmerBaseModulus target e) := ⟨(selmerBaseModulus_pos target e).ne'⟩
  let _ : Finite (rel e).range := Finite.of_surjective (rel e).rangeRestrict (rel e).rangeRestrict_surjective
  exact Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

/-- The coefficient of `2^e` in the host degree is eventually constant.
For Proposition 18.4 only stabilization is required, so monotonicity suffices. -/
theorem selmerHostBaseGroup_card_eventually_dyadic (target : BundledDirichletCharacter) :
    ∃ E c : ℕ, 0 < c ∧ c ∣ orderOf target.character ∧
      ∀ e ≥ E, Nat.card (SelmerHostBaseGroup target e) = c * 2 ^ e := by
  classical
  let f := fun e => Nat.card (selmerBaseDyadicReduction target e).ker
  have hex : ∃ c, ∃ n, f n = c := ⟨f 0, 0, rfl⟩
  obtain ⟨E, hE⟩ := Nat.find_spec hex
  refine ⟨E, f E, ?_, selmerBaseDyadicReduction_card_ker_dvd_order target E, ?_⟩
  · let _ : NeZero (selmerBaseModulus target E) := ⟨(selmerBaseModulus_pos target E).ne'⟩
    exact Nat.card_pos
  · intro e he
    rw [selmerHostBaseGroup_card]
    have hle : f e ≤ f E := selmerBaseDyadicReduction_card_ker_antitone target he
    have hge : f E ≤ f e := hE.symm ▸ Nat.find_min' hex ⟨e, rfl⟩
    exact congrArg (· * 2 ^ e) (hle.antisymm hge)

/-- Choose the host degree in the required dyadic range, uniformly at all
large scales. The coefficient is fixed before applying the rescaled window bound. -/
theorem exists_selmerHostBaseGroup_ambient_choice
    (target : BundledDirichletCharacter) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ (xe c₀ : ℝ) (e : ℝ → ℕ), 1 ≤ xe ∧ 1 ≤ c₀ ∧
      ∀ x ≥ xe, letI := selmerHostBaseGroupFintype target (e x)
        (Fintype.card (SelmerHostBaseGroup target (e x)) : ℝ) = c₀ * (2 : ℝ) ^ e x ∧
        x ^ (2 + 8 * ε) ≤ c₀ * (2 : ℝ) ^ e x ∧
        c₀ * (2 : ℝ) ^ e x ≤ 2 * x ^ (2 + 8 * ε) := by
  classical
  obtain ⟨E, c, hc, _, hstable⟩ := selmerHostBaseGroup_card_eventually_dyadic target
  let A : ℝ := c * (2 : ℝ) ^ E
  have hA₀ : 0 < A := by positivity
  let xe : ℝ := max 1 A
  have hchoice (x : ℝ) : ∃ e ≥ E,
      xe ≤ x → x ^ (2 + 8 * ε) ≤ (c : ℝ) * (2 : ℝ) ^ e ∧
        (c : ℝ) * (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * ε) := by
    by_cases hx : xe ≤ x
    · have hx₁ : 1 ≤ x := (le_max_left _ _).trans hx
      have hxA : A ≤ x ^ (2 + 8 * ε) := by
        refine ((le_max_right _ _).trans hx).trans ?_
        simpa only [Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith : (1 : ℝ) ≤ 2 + 8 * ε))
      obtain ⟨n, hlo, hhi⟩ := exists_dyadic_cover ((one_le_div hA₀).mpr hxA)
      refine ⟨E + n, by omega, fun _ => ⟨?_, ?_⟩⟩
      · have h := (div_le_iff₀ hA₀).mp hlo
        simpa [A, pow_add, mul_assoc, mul_comm, mul_left_comm] using h
      · have h := mul_le_mul_of_nonneg_right hhi hA₀.le
        rw [mul_assoc, div_mul_cancel₀ _ hA₀.ne'] at h
        simpa [A, pow_add, mul_assoc, mul_comm, mul_left_comm] using h
    · exact ⟨E, le_rfl, fun h => (hx h).elim⟩
  let e (x : ℝ) := Classical.choose (hchoice x)
  refine ⟨xe, c, e, le_max_left _ _, by exact_mod_cast hc, ?_⟩
  intro x hx
  obtain ⟨he, hbounds⟩ := Classical.choose_spec (hchoice x)
  let _ := selmerHostBaseGroupFintype target (e x)
  refine ⟨?_, hbounds hx⟩
  rw [← Nat.card_eq_fintype_card, hstable _ he]
  push_cast
  rfl

/-- Couple the rescaled Selmer window and the required host degrees to
auxiliary primes satisfying a uniform selection property at the base scale. -/
theorem exists_ambient_selmer_windows_of_pair_selection
    {lengths : NumberFieldSelmerLengths} (hSelmer : HasRescaledSelmerWindowBound lengths)
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε : ℝ} (hε : 0 < ε) (hε₀ : ε < 1 / 52)
    (P : ℝ → ℝ → ℕ+ → ℕ+ → Prop)
    (hPair : ∀ J ≥ 2, ∃ T : ℝ, ∀ base ≥ T, ∃ q d : ℕ+,
      SelmerWindowPair ε base q d ∧ P J base q d) :
    ∃ J : ℝ, 2 ≤ J ∧ ∀ lower : ℝ,
      ∃ (base Y : ℝ) (q d : ℕ+) (e : ℝ → ℕ),
        max 1 lower ≤ Y ∧ 3 ≤ base ∧ base ≤ Y ∧ Y ^ (2 : ℕ) ≤ base ^ J ∧
        SelmerWindowPair ε base q d ∧ P J base q d ∧
        ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)), letI := selmerHostBaseGroupFintype target (e x)
          x ∈ Set.Icc base (base ^ J) ∧
          x ^ (2 + 8 * ε) ≤ (Fintype.card (SelmerHostBaseGroup target (e x)) : ℝ) ∧
          (Fintype.card (SelmerHostBaseGroup target (e x)) : ℝ) ≤ 2 * x ^ (2 + 8 * ε) ∧
          SelmerLengthBound (lengths (selmerHostField target (e x) q d))
            (Nat.floor (x ^ (400 : ℕ))) (Real.exp (x ^ ε / 2)) := by
  obtain ⟨xe, c, e, hxe, hc, hdegree⟩ := exists_selmerHostBaseGroup_ambient_choice target hε.le
  obtain ⟨J, X₀, hJ, _, hwindow⟩ := hSelmer target hprim ε hε hε₀ xe c hxe hc e
    (fun x hx => (hdegree x hx).2)
  have hJpos : 0 < J := zero_lt_one.trans_le hJ
  have hJ₂ : (2 : ℝ) ≤ J + 1 := by linarith
  obtain ⟨T, hchoose⟩ := hPair (J + 1) hJ₂
  refine ⟨J + 1, hJ₂, fun lower => ?_⟩
  let B := max (max 3 xe) (max lower T)
  let X := max X₀ (B ^ J)
  let base := X ^ (1 / J)
  have hB : (3 : ℝ) ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB₀ : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 3).trans hB
  have hbase : B ≤ base := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hB₀ J) (le_max_right X₀ (B ^ J))
      (one_div_nonneg.mpr hJpos.le)
    rw [one_div, Real.rpow_rpow_inv hB₀ hJpos.ne'] at h
    simpa only [base, X, one_div] using h
  have hbase₃ : (3 : ℝ) ≤ base := hB.trans hbase
  have hxeB : xe ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hTB : T ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨q, d, hpair, hP⟩ := hchoose base (hTB.trans hbase)
  obtain ⟨Y, hY, hYpow, hD6⟩ := hwindow X (le_max_left _ _) q d hpair
  have hY₁ : 1 ≤ Y := (by norm_num : (1 : ℝ) ≤ 3).trans (hbase₃.trans hY)
  have hlowB : lower ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨base, Y, q, d, e, max_le hY₁ (hlowB.trans (hbase.trans hY)),
    hbase₃, hY, hYpow, hpair, hP, ?_⟩
  intro x hx
  have hxb := hY.trans hx.1
  have hpow : Y ^ (3 / 2 : ℝ) ≤ Y ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hY₁ (by norm_num)
  have hmem : x ∈ Set.Icc base (base ^ (J + 1)) := ⟨hxb, hx.2.trans (hpow.trans hYpow)⟩
  obtain ⟨hcard, hlo, hhi⟩ := hdegree x (hxeB.trans (hbase.trans hxb))
  rw [← hcard] at hlo hhi
  exact ⟨hmem, hlo, hhi, hD6 x hx⟩

end Riemann
