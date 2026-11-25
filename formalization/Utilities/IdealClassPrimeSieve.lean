module

public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Logic.Equiv.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

open Filter Ideal IsDedekindDomain NumberField
open NumberField.InfinitePlace NumberField.Units
open scoped NumberField nonZeroDivisors Topology

namespace Utilities

variable (K : Type*) [Field K] [NumberField K]

local notation "I₀" => (Ideal (𝓞 K))⁰
local notation "Primes" => HeightOneSpectrum (𝓞 K)

/-- The nonzero integral ideal underlying a height-one prime. -/
def heightOnePrimeIdeal (v : Primes) : I₀ :=
  ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩

/-- Every prime in the set fails to divide the ideal. -/
def integralIdealAvoids (s : Set Primes) (I : I₀) : Prop :=
  ∀ v ∈ s, ¬ heightOnePrimeIdeal K v ∣ I

/-- Nonzero integral ideals in the given class, of bounded norm, avoiding
the given primes. -/
abbrev boundedClassIdealsAvoiding (s : Set Primes) (C : ClassGroup (𝓞 K)) (x : ℝ) :=
  {I : I₀ // (absNorm I.val : ℝ) ≤ x ∧ ClassGroup.mk0 I = C ∧ integralIdealAvoids K s I}

/-- The leading coefficient for the number of ideals in a fixed class. -/
noncomputable def idealClassCountConstant : ℝ :=
  (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulator K) /
    (torsionOrder K * Real.sqrt |discr K|)

theorem idealClassCountConstant_pos : 0 < idealClassCountConstant K := by
  unfold idealClassCountConstant
  refine div_pos (mul_pos (by positivity) (regulator_pos K)) ?_
  exact mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K))
    (Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))))

theorem finite_nonzeroIntegralIdeals_norm_le (x : ℝ) (hx : 0 ≤ x) :
    Finite {I : I₀ // (absNorm I.val : ℝ) ≤ x} := by
  have h : {I : I₀ | (absNorm I.val : ℝ) ≤ x}.Finite := by
    simpa only [← Nat.le_floor_iff hx] using
      Ring.HasFiniteQuotients.finite_absNorm_le₀ (S := 𝓞 K) ⌊x⌋₊
  exact h.to_subtype

private theorem finite_boundedClassIdealsAvoiding (s : Set Primes) (C : ClassGroup (𝓞 K)) (x : ℝ)
    (hx : 0 ≤ x) : Finite (boundedClassIdealsAvoiding K s C x) := by
  let _ := finite_nonzeroIntegralIdeals_norm_le K x hx
  exact Finite.of_injective
    (fun (I : boundedClassIdealsAvoiding K s C x) =>
      (⟨I.val, I.property.1⟩ : {I : I₀ // (absNorm I.val : ℝ) ≤ x}))
    (fun _ _ h => Subtype.ext (congrArg (fun I : {I : I₀ // (absNorm I.val : ℝ) ≤ x} => I.val) h))

private theorem primeIdeal_not_dvd_of_ne (v w : Primes) (hwv : w ≠ v) :
    ¬heightOnePrimeIdeal K w ∣ heightOnePrimeIdeal K v := by
  intro h
  have h' : w.asIdeal ∣ v.asIdeal := nonZeroDivisors_dvd_iff_dvd_coe.mp h
  exact w.prime.not_isUnit ((w.isCoprime_of_ne v hwv).isRelPrime (dvd_refl _) h')

private theorem avoids_mul_prime_iff (s : Set Primes) (v : Primes) (hv : v ∉ s) (I : I₀) :
    integralIdealAvoids K s (heightOnePrimeIdeal K v * I) ↔ integralIdealAvoids K s I := by
  constructor
  · intro h w hw hd
    have h' : w.asIdeal ∣ I.val := nonZeroDivisors_dvd_iff_dvd_coe.mp hd
    exact h w hw (nonZeroDivisors_dvd_iff_dvd_coe.mpr (dvd_mul_of_dvd_right h' _))
  · intro h w hw hd
    have h' : w.asIdeal ∣ v.asIdeal * I.val := nonZeroDivisors_dvd_iff_dvd_coe.mp hd
    rcases w.prime.dvd_or_dvd h' with h₁ | h₂
    · exact primeIdeal_not_dvd_of_ne K v w (fun he => hv (he ▸ hw))
        (nonZeroDivisors_dvd_iff_dvd_coe.mpr h₁)
    · exact h w hw (nonZeroDivisors_dvd_iff_dvd_coe.mpr h₂)

private theorem card_insert_avoiding (s : Set Primes) (v : Primes) (hv : v ∉ s)
    (C : ClassGroup (𝓞 K)) (x : ℝ) (hx : 0 ≤ x) :
    Nat.card (boundedClassIdealsAvoiding K (insert v s) C x) +
      Nat.card (boundedClassIdealsAvoiding K s ((ClassGroup.mk0 (heightOnePrimeIdeal K v))⁻¹ * C)
        (x / (absNorm v.asIdeal : ℝ))) =
      Nat.card (boundedClassIdealsAvoiding K s C x) := by
  classical
  let P := heightOnePrimeIdeal K v
  let A := boundedClassIdealsAvoiding K s C x
  let A₀ := {I : A // ¬P ∣ I.val}
  let A₁ := {I : A // P ∣ I.val}
  let B := boundedClassIdealsAvoiding K s ((ClassGroup.mk0 P)⁻¹ * C) (x / (absNorm v.asIdeal : ℝ))
  have hN : 0 < (absNorm v.asIdeal : ℝ) :=
    Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors P)
  have h₀ : Nat.card (boundedClassIdealsAvoiding K (insert v s) C x) = Nat.card A₀ := by
    apply Nat.card_congr
    refine (Equiv.subtypeEquiv (Equiv.refl I₀) ?_).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : I₀ => (absNorm I.val : ℝ) ≤ x ∧ ClassGroup.mk0 I = C ∧ integralIdealAvoids K s I)
        (fun I => ¬ P ∣ I)).symm
    intro I
    have hAvoid : integralIdealAvoids K (insert v s) I ↔ integralIdealAvoids K s I ∧ ¬P ∣ I := by
      simp only [integralIdealAvoids, Set.forall_mem_insert, P, and_comm]
    simp only [Equiv.refl_apply, hAvoid, and_assoc]
  have h₁ : Nat.card B = Nat.card A₁ := by
    apply Nat.card_congr
    refine ((Equiv.dvd P).subtypeEquiv ?_).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
        ((Equiv.subtypeEquiv (Equiv.refl I₀) (fun I => and_comm)).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm))
    intro I
    simp only [Equiv.dvd_apply, Equiv.refl_apply]
    have hnorm : (absNorm (P * I : I₀).val : ℝ) ≤ x ↔ (absNorm I.val : ℝ) ≤ x / (absNorm v.asIdeal : ℝ) := by
      change (absNorm (v.asIdeal * I.val) : ℝ) ≤ x ↔ _
      rw [map_mul, Nat.cast_mul, le_div_iff₀ hN, mul_comm (absNorm v.asIdeal : ℝ)]
    have hclass : ClassGroup.mk0 P * ClassGroup.mk0 I = C ↔
        ClassGroup.mk0 I = (ClassGroup.mk0 P)⁻¹ * C := by
      constructor
      · intro h
        rw [← h, inv_mul_cancel_left]
      · intro h
        rw [h, mul_inv_cancel_left]
    rw [hnorm, map_mul, hclass, avoids_mul_prime_iff K s v hv]
  let _ : Finite A := finite_boundedClassIdealsAvoiding K s C x hx
  have hsum : Nat.card A₀ + Nat.card A₁ = Nat.card A := by
    rw [add_comm, ← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun I : A => P ∣ I.val))
  exact congrArg₂ (· + ·) h₀ h₁ |>.trans hsum

/-- Deleting finitely many primes multiplies the ideal-counting constant
of every class by the same product of local factors. -/
theorem tendsto_card_boundedClassIdealsAvoiding_finset
    (s : Finset Primes) (C : ClassGroup (𝓞 K)) :
    Tendsto (fun x : ℝ => (Nat.card (boundedClassIdealsAvoiding K (s : Set Primes) C x) : ℝ) / x)
      atTop (𝓝 (idealClassCountConstant K * ∏ v ∈ s, (1 - (absNorm v.asIdeal : ℝ)⁻¹))) := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty =>
    simpa only [idealClassCountConstant, Finset.coe_empty, Finset.prod_empty, mul_one,
      boundedClassIdealsAvoiding, integralIdealAvoids, Set.forall_mem_empty, and_true] using
      NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K C
  | @insert v s hv ih =>
    let n : ℝ := absNorm v.asIdeal
    have hn : 0 < n := Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors (heightOnePrimeIdeal K v))
    let C' := (ClassGroup.mk0 (heightOnePrimeIdeal K v))⁻¹ * C
    let L := idealClassCountConstant K * ∏ w ∈ s, (1 - (absNorm w.asIdeal : ℝ)⁻¹)
    have hscaled : Tendsto (fun x : ℝ =>
        (Nat.card (boundedClassIdealsAvoiding K (s : Set Primes) C' (x / n)) : ℝ) / x)
        atTop (𝓝 (L / n)) := by
      have hd : Tendsto (fun x : ℝ => x / n) atTop atTop := tendsto_id.atTop_div_const hn
      apply (((ih C').comp hd).div_const n).congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      dsimp only [Function.comp_apply]
      field_simp
    have hL : L - L / n = idealClassCountConstant K *
        ∏ w ∈ insert v s, (1 - (absNorm w.asIdeal : ℝ)⁻¹) := by
      rw [Finset.prod_insert hv]
      dsimp only [L, n]
      ring
    rw [← hL]
    apply ((ih C).sub hscaled).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hc := congrArg (fun m : ℕ => (m : ℝ) / x)
      (card_insert_avoiding K (s : Set Primes) v hv C x hx)
    simp only [Nat.cast_add, add_div] at hc
    simp only [Finset.coe_insert]
    linarith

/-- The leading coefficient for the total number of ideals. -/
noncomputable def integralIdealCountConstant : ℝ :=
  idealClassCountConstant K * (classNumber K : ℝ)

theorem integralIdealCountConstant_pos : 0 < integralIdealCountConstant K :=
  mul_pos (idealClassCountConstant_pos K) (Nat.cast_pos.mpr (classNumber_pos K))

theorem tendsto_card_nonzeroIntegralIdeal_norm_le_div :
    Tendsto (fun x : ℝ => (Nat.card {I : I₀ // (absNorm I.val : ℝ) ≤ x} : ℝ) / x)
      atTop (𝓝 (integralIdealCountConstant K)) := by
  convert NumberField.Ideal.tendsto_norm_le_div_atTop₀ K using 1
  congr 1
  dsimp only [integralIdealCountConstant, idealClassCountConstant]
  ring

/-- The total count of nonzero ideals of norm at most `x` has a uniform
linear bound for `x ≥ 1`. -/
theorem exists_linear_bound_nonzeroIntegralIdealCount :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 1 ≤ x →
      (Nat.card {I : I₀ // (absNorm I.val : ℝ) ≤ x} : ℝ) ≤ B * x := by
  let count (x : ℝ) : ℝ := Nat.card {I : I₀ // (absNorm I.val : ℝ) ≤ x}
  let D := integralIdealCountConstant K
  have hD : 0 < D := integralIdealCountConstant_pos K
  have hlim : Tendsto (fun x : ℝ => count x / x) atTop (𝓝 D) :=
    tendsto_card_nonzeroIntegralIdeal_norm_le_div K
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds (lt_add_one D)))
  let M := max A 1
  let B := D + 1 + count M
  have hB : 0 < B := add_pos_of_pos_of_nonneg (by linarith) (Nat.cast_nonneg _)
  refine ⟨B, hB, fun x hx => ?_⟩
  by_cases hMx : M ≤ x
  · have hbound : count x / x < D + 1 := hA x ((le_max_left _ _).trans hMx)
    change count x ≤ B * x
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hx)).mp
      (hbound.le.trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  · have hxM : x ≤ M := (lt_of_not_ge hMx).le
    let _ := finite_nonzeroIntegralIdeals_norm_le K M (zero_le_one.trans (le_max_right _ _))
    have hcount : count x ≤ count M := by
      apply Nat.cast_le.mpr
      exact Nat.card_le_card_of_injective
        (fun (I : {I : I₀ // (absNorm I.val : ℝ) ≤ x}) =>
          (⟨I.val, I.property.trans hxM⟩ : {I : I₀ // (absNorm I.val : ℝ) ≤ M}))
        (fun _ _ h => Subtype.ext (congrArg (fun (I : {I : I₀ // (absNorm I.val : ℝ) ≤ M}) => I.val) h))
    change count x ≤ B * x
    calc
      _ ≤ count M := hcount
      _ ≤ B := le_add_of_nonneg_left (by linarith)
      _ ≤ B * x := le_mul_of_one_le_right hB.le hx

/-- A summable family of omitted prime norms has a strictly positive
lower bound on all its finite products of sieve factors. -/
theorem exists_pos_le_primeSieve_products (s : Set Primes)
    (hs : Summable (fun v : s => (absNorm v.val.asIdeal : ℝ)⁻¹)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Finset s, δ ≤ ∏ v ∈ t, (1 - (absNorm v.val.asIdeal : ℝ)⁻¹) := by
  let f (v : s) : ℝ := 1 - (absNorm v.val.asIdeal : ℝ)⁻¹
  have hnorm (v : s) : 1 < (absNorm v.val.asIdeal : ℝ) := by
    have hp : 0 < absNorm v.val.asIdeal := absNorm_pos_of_nonZeroDivisors (heightOnePrimeIdeal K v.val)
    have hne : absNorm v.val.asIdeal ≠ 1 := fun he => v.val.isPrime.ne_top (absNorm_eq_one_iff.mp he)
    exact_mod_cast (show 1 < absNorm v.val.asIdeal by omega)
  have hpos (v : s) : 0 < f v := sub_pos.mpr (inv_lt_one_of_one_lt₀ (hnorm v))
  have hle (v : s) : f v ≤ 1 := sub_le_self _ (inv_nonneg.mpr (by positivity))
  have hlog : Summable (fun v : s => Real.log (f v)) := by
    simpa only [f, sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
  have hprod := Real.hasProd_of_hasSum_log hpos hlog.hasSum
  refine ⟨_, Real.exp_pos _, fun t => le_of_tendsto hprod ?_⟩
  filter_upwards [eventually_ge_atTop t] with u hu
  exact Finset.prod_le_prod_of_subset_of_le_one₀ hu (fun v _ => (hpos v).le) (fun v _ _ => hle v)

private theorem card_ideals_le_of_covered {D : Type*}
    (I : D → I₀) (hI : Function.Injective I) (S : Set Primes) [Finite S] (x B : ℝ)
    (hB : ∀ y : ℝ, 1 ≤ y → (Nat.card {I : I₀ // (absNorm I.val : ℝ) ≤ y} : ℝ) ≤ B * y)
    (hN : ∀ v : S, (absNorm v.val.asIdeal : ℝ) ≤ x)
    (hsizeI : ∀ d, (absNorm (I d).val : ℝ) ≤ x)
    (hcover : ∀ d, ∃ v : S, heightOnePrimeIdeal K v.val ∣ I d) :
    (Nat.card D : ℝ) ≤
      B * x * ∑' v : S, (absNorm v.val.asIdeal : ℝ)⁻¹ := by
  classical
  let _ : Fintype S := Fintype.ofFinite _
  let norm (v : S) : ℝ := absNorm v.val.asIdeal
  have hn (v : S) : 0 < norm v := Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors
    (heightOnePrimeIdeal K v.val))
  have hdiv (v : S) : 1 ≤ x / norm v := (le_div_iff₀ (hn v)).mpr (by simpa using hN v)
  let F (v : S) := {I : I₀ // (absNorm I.val : ℝ) ≤ x / norm v}
  let _ (v : S) : Finite (F v) := finite_nonzeroIntegralIdeals_norm_le K _ (zero_le_one.trans (hdiv v))
  choose v hv using hcover
  let J (d : D) : I₀ := (Equiv.dvd (heightOnePrimeIdeal K (v d).val)).symm ⟨I d, hv d⟩
  have hJ (d : D) : heightOnePrimeIdeal K (v d).val * J d = I d :=
    congrArg Subtype.val ((Equiv.dvd (heightOnePrimeIdeal K (v d).val)).apply_symm_apply ⟨I d, hv d⟩)
  have hsize (d : D) : (absNorm (J d).val : ℝ) ≤ x / norm (v d) := by
    apply (le_div_iff₀ (hn (v d))).mpr
    have hm := congrArg (fun a : I₀ => (absNorm a.val : ℝ)) (hJ d)
    change (absNorm ((v d).val.asIdeal * (J d).val) : ℝ) = absNorm (I d).val at hm
    rw [map_mul, Nat.cast_mul, mul_comm] at hm
    exact hm.le.trans (hsizeI d)
  let f (d : D) : Σ v : S, F v := ⟨v d, ⟨J d, hsize d⟩⟩
  have hf : Function.Injective f := by
    intro d d' he
    have hd := congrArg (fun P : Σ v : S, F v => heightOnePrimeIdeal K P.1.val * P.2.val) he
    exact hI ((hJ d).symm.trans (hd.trans (hJ d')))
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sigma] at hcard
  calc
    _ ≤ ∑ v : S, (Nat.card (F v) : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ v : S, B * (x / norm v) := Finset.sum_le_sum fun v _ => hB _ (hdiv v)
    _ = _ := by rw [tsum_fintype, Finset.mul_sum]; simp only [div_eq_mul_inv, mul_assoc, norm]

/-- In each ideal class the ideals avoiding a set with summable inverse
norms have a positive linear lower count. -/
theorem eventually_card_boundedClassIdealsAvoiding_div_ge
    (s : Set Primes) (hs : Summable (fun v : s => (absNorm v.val.asIdeal : ℝ)⁻¹))
    (C : ClassGroup (𝓞 K)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ x : ℝ in atTop,
      d ≤ (Nat.card (boundedClassIdealsAvoiding K s C x) : ℝ) / x := by
  classical
  obtain ⟨B, hB, hbound⟩ := exists_linear_bound_nonzeroIntegralIdealCount K
  obtain ⟨δ, hδ, hprod⟩ := exists_pos_le_primeSieve_products K s hs
  let c := idealClassCountConstant K
  have hc : 0 < c := idealClassCountConstant_pos K
  let f (v : s) : ℝ := (absNorm v.val.asIdeal : ℝ)⁻¹
  let ε := c * δ / (4 * B)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he : ∀ᶠ t : Finset s in atTop, (∑' v : s, f v) - ε < ∑ v ∈ t, f v :=
    hs.hasSum.eventually (Ioi_mem_nhds (sub_lt_self _ hε))
  obtain ⟨t, ht⟩ := he.exists
  let U : Set s := (t : Set s)ᶜ
  have htail : (∑' v : U, f v.val) < ε := by
    have ht' := hs.sum_add_tsum_subtype_compl t
    change (∑ v ∈ t, f v) + (∑' v : U, f v.val) = ∑' v : s, f v at ht'
    linarith
  let t' : Finset Primes := t.map ⟨Subtype.val, Subtype.val_injective⟩
  let L := c * ∏ v ∈ t', (1 - (absNorm v.asIdeal : ℝ)⁻¹)
  have hL : c * δ ≤ L := by
    dsimp only [L, t']
    rw [Finset.prod_map]
    exact mul_le_mul_of_nonneg_left (hprod t) hc.le
  have hhalf : c * δ / 2 < L := lt_of_lt_of_le (by nlinarith [mul_pos hc hδ]) hL
  have hlim := tendsto_card_boundedClassIdealsAvoiding_finset K t' C
  have hlarge : ∀ᶠ x : ℝ in atTop,
      c * δ / 2 < (Nat.card (boundedClassIdealsAvoiding K (t' : Set Primes) C x) : ℝ) / x :=
    hlim.eventually (Ioi_mem_nhds hhalf)
  refine ⟨c * δ / 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlarge] with x hx hxlarge
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  let D := boundedClassIdealsAvoiding K (t' : Set Primes) C x
  let G := {I : D // integralIdealAvoids K s I.val}
  let Bads := {I : D // ¬ integralIdealAvoids K s I.val}
  let _ : Finite D := finite_boundedClassIdealsAvoiding K _ C x hx₀.le
  let _ : Finite (boundedClassIdealsAvoiding K s C x) := finite_boundedClassIdealsAvoiding K s C x hx₀.le
  have hG : Nat.card G ≤ Nat.card (boundedClassIdealsAvoiding K s C x) :=
    Nat.card_le_card_of_injective
      (fun I : G => (⟨I.val.val, I.val.property.1, I.val.property.2.1, I.property⟩ :
        boundedClassIdealsAvoiding K s C x))
      (fun _ _ h => Subtype.ext (Subtype.ext
        (congrArg (fun I : boundedClassIdealsAvoiding K s C x => I.val) h)))
  have hsplit : Nat.card G + Nat.card Bads = Nat.card D := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun I : D => integralIdealAvoids K s I.val))
  let S : Set Primes := {v | ∃ hv : v ∈ s, (⟨v, hv⟩ : s) ∉ t ∧ (absNorm v.asIdeal : ℝ) ≤ x}
  let _ := finite_nonzeroIntegralIdeals_norm_le K x (zero_le_one.trans hx)
  let _ : Finite S := Finite.of_injective
    (fun v : S => (⟨heightOnePrimeIdeal K v.val, v.property.choose_spec.2⟩ :
      {I : I₀ // (absNorm I.val : ℝ) ≤ x}))
    (fun v w heq => Subtype.ext (HeightOneSpectrum.ext (congrArg
      (fun a : {I : I₀ // (absNorm I.val : ℝ) ≤ x} => a.val.val) heq)))
  have hcover (I : Bads) : ∃ v : S, heightOnePrimeIdeal K v.val ∣ I.val.val := by
    have hnot := I.property
    unfold integralIdealAvoids at hnot
    push Not at hnot
    obtain ⟨v, hv, hd⟩ := hnot
    have hvt : (⟨v, hv⟩ : s) ∉ t := by
      intro ht
      exact I.val.property.2.2 v (Finset.mem_map.mpr ⟨⟨v, hv⟩, ht, rfl⟩) hd
    have hn : (absNorm v.asIdeal : ℝ) ≤ x := by
      have hdiv : v.asIdeal ∣ I.val.val.val := nonZeroDivisors_dvd_iff_dvd_coe.mp hd
      exact (Nat.cast_le.mpr (Nat.le_of_dvd (absNorm_pos_of_nonZeroDivisors I.val.val)
        (map_dvd Ideal.absNorm hdiv))).trans I.val.property.1
    exact ⟨⟨v, hv, hvt, hn⟩, hd⟩
  have hcount := card_ideals_le_of_covered K (fun I : Bads => I.val.val)
    (fun _ _ h => Subtype.ext (Subtype.ext h)) S x B hbound
    (fun v => v.property.choose_spec.2) (fun I => I.val.property.1) hcover
  let j (v : S) : U := ⟨⟨v.val, v.property.choose⟩, v.property.choose_spec.1⟩
  have hj : Function.Injective j :=
    fun _ _ heq => Subtype.ext (congrArg (fun u : U => u.val.val) heq)
  have hsum : (∑' v : S, (absNorm v.val.asIdeal : ℝ)⁻¹) ≤ ∑' v : U, f v.val :=
    tsum_comp_le_tsum_of_inj (hs.subtype (fun v => v ∈ U)) (fun _ => inv_nonneg.mpr (by positivity)) hj
  have hbound' : (Nat.card Bads : ℝ) / x ≤
      B * (∑' v : U, f v.val) := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hx)).mpr
    exact hcount.trans ((mul_le_mul_of_nonneg_left hsum (mul_nonneg hB.le (zero_le_one.trans hx))).trans_eq
      (mul_right_comm B x _))
  have hstrict : B * ∑' v : U, f v.val < c * δ / 4 := by
    have hCancel : B * ε = c * δ / 4 := by dsimp [ε]; field_simp
    exact (mul_lt_mul_of_pos_left htail hB).trans_eq hCancel
  have hsplit' : (Nat.card D : ℝ) / x ≤
      (Nat.card (boundedClassIdealsAvoiding K s C x) : ℝ) / x + (Nat.card Bads : ℝ) / x := by
    rw [← add_div, ← Nat.cast_add]
    exact div_le_div_of_nonneg_right (by exact_mod_cast (hsplit.symm.trans_le (Nat.add_le_add_right hG _))) hx₀.le
  linarith [hbound'.trans_lt hstrict]

/-- Every class has a representative avoiding a set of primes whose
inverse norms are summable. -/
theorem exists_integralIdeal_in_class_avoiding_of_summable
    (s : Set Primes) (hs : Summable (fun v : s => (absNorm v.val.asIdeal : ℝ)⁻¹))
    (C : ClassGroup (𝓞 K)) :
    ∃ I : I₀, ClassGroup.mk0 I = C ∧ integralIdealAvoids K s I := by
  obtain ⟨d, hd, hb⟩ := eventually_card_boundedClassIdealsAvoiding_div_ge K s hs C
  obtain ⟨x, hx, hcount⟩ := ((eventually_gt_atTop (0 : ℝ)).and hb).exists
  have h : 0 < Nat.card (boundedClassIdealsAvoiding K s C x) :=
    Nat.cast_pos.mp (by
      have h := (lt_div_iff₀ hx).mp (hd.trans_le hcount)
      simpa only [zero_mul] using h)
  have hn : Nonempty (boundedClassIdealsAvoiding K s C x) := by
    by_contra! he
    let _ : IsEmpty (boundedClassIdealsAvoiding K s C x) := he
    simp at h
  obtain ⟨I⟩ := hn
  exact ⟨I.val, I.property.2.1, I.property.2.2⟩

/-- The classes of the primes outside a set with summable inverse norms
generate the whole class group. -/
theorem closure_primeClasses_compl_eq_top_of_summable (s : Set Primes)
    (hs : Summable (fun v : s => (absNorm v.val.asIdeal : ℝ)⁻¹)) :
    Subgroup.closure (Set.range fun v : ↥(sᶜ : Set Primes) => ClassGroup.mk0 (heightOnePrimeIdeal K v.val)) = ⊤ := by
  classical
  apply eq_top_iff.mpr
  intro C _
  obtain ⟨I, rfl, hI⟩ := exists_integralIdeal_in_class_avoiding_of_summable K s hs C
  have hI₀ : I.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  let n (v : Primes) := (Associates.mk v.asIdeal).count (Associates.mk I.val).factors
  let F (v : Primes) : I₀ := heightOnePrimeIdeal K v ^ n v
  have hsupport : Function.HasFiniteMulSupport F :=
    (Ideal.finite_factors hI₀).subset (fun v hv => (Associates.count_ne_zero_iff_dvd hI₀ v.irreducible).mp
      (fun hn => hv (by change heightOnePrimeIdeal K v ^ n v = 1; rw [show n v = 0 from hn, pow_zero])))
  have hfac : (∏ᶠ v, F v) = I := by
    apply Subtype.ext
    change (nonZeroDivisors (Ideal (𝓞 K))).subtype (∏ᶠ v, F v) = I.val
    rw [map_finprod _ hsupport]
    simp only [F, map_pow]
    exact Ideal.finprod_heightOneSpectrum_factorization hI₀
  rw [← hfac, finprod_eq_finsetProd_of_mulSupport_subset F
    (fun _ h => hsupport.mem_toFinset.mpr h), map_prod]
  apply Subgroup.prod_mem
  intro v hv
  rw [show F v = heightOnePrimeIdeal K v ^ n v from rfl, map_pow]
  apply Subgroup.pow_mem _ _ _
  have hv' : v ∉ s := by
    intro hvs
    have hn : n v ≠ 0 := by
      intro he
      have hm := hsupport.mem_toFinset.mp hv
      apply hm
      change heightOnePrimeIdeal K v ^ n v = 1
      rw [he, pow_zero]
    exact hI v hvs (nonZeroDivisors_dvd_iff_dvd_coe.mpr
      ((Associates.count_ne_zero_iff_dvd hI₀ v.irreducible).mp hn))
  exact Subgroup.subset_closure ⟨⟨v, hv'⟩, rfl⟩

end Utilities
