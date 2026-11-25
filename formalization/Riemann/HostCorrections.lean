module

public import Riemann.HostAveraging
public import Riemann.SmoothedVariation
public import Utilities.CosetEquidistribution
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

open Filter Utilities
open scoped BigOperators Classical

namespace Riemann

/-- A single growth constant works for zeta and for all primitive powers
of the fixed target. The constant is independent of the auxiliary primes. -/
theorem exists_selmerFixedNormBound (target : BundledDirichletCharacter)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ≥ 1,
      |smoothedZetaSum x| ≤ B * x ^ (1 + ε) ∧
      ∀ i : Fin (orderOf target.character),
        ‖complexSmoothedCharacterSum (selmerFixedCharacter target i) x‖ ≤ B * x ^ (1 + ε) := by
  classical
  have ha : 1 < 1 + ε := lt_add_of_pos_right 1 hε
  obtain ⟨B₀, hB₀, hz⟩ := abs_smoothedZetaSum_le_rpow ha
  choose C hC hchar using fun i : Fin (orderOf target.character) =>
    norm_complexSmoothedCharacterSum_le_rpow (selmerFixedCharacter target i) ha
  let B := 1 + B₀ + ∑ i, C i
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC i
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB₀B : B₀ ≤ B := by dsimp [B]; linarith
  refine ⟨B, hB, fun x hx => ⟨(hz x hx).trans (mul_le_mul_of_nonneg_right hB₀B (by positivity)), ?_⟩⟩
  intro i
  have hi : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have hCB : C i ≤ B := by dsimp [B]; linarith
  exact (hchar i x hx).trans (mul_le_mul_of_nonneg_right hCB (by positivity))

section NormAndVariation

variable (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
  [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime] [Fintype (SelmerHostBaseGroup target e)]
  (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3)
  (hq : (selmerBaseModulus target e).Coprime q)
  (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
  (avg : ExcessAverageData (SelmerHostBaseGroup target e))
  (hgroup : avg.subgroup = selmerAveragingSubgroup target e)
  (hkept : avg.kept = selmerKeptCharacters target e)
  (prime : PrimeExcessData (SelmerHostBaseGroup target e))
  (hprime : HostInducingConditions prime
    (selmerHostInducingCharacter (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm))
  {x ε B : ℝ}

include hgroup hkept hprime in
/-- The fixed-family bound and the moving auxiliary estimates together
control every survivor at the base of the local-variation estimate. -/
theorem selmerSurvivors_norm_le
    (hx : 1 ≤ x) (hB : 1 ≤ B)
    (hz : |smoothedZetaSum x| ≤ B * x ^ (1 + ε))
    (hfixed : ∀ i : Fin (orderOf target.character),
      ‖complexSmoothedCharacterSum (selmerFixedCharacter target i) x‖ ≤ B * x ^ (1 + ε))
    (haux : ∀ i, ‖complexSmoothedCharacterSum (selmerAuxiliaryCharacter target q d hq₄ hd₄ i) x‖ ≤
      x ^ (1 / 2 + ε)) :
    ∀ ψ ∈ avg.survivors, ‖prime.smoothed ψ x‖ ≤ B * x ^ (1 + ε) := by
  classical
  intro ψ hψ
  by_cases hzero : ψ = 0
  · rwa [hzero, prime.smoothed_zero, Complex.norm_real, Real.norm_eq_abs]
  by_cases hmem : ψ ∈ avg.kept
  · rw [hkept, selmerKeptCharacters, Finset.mem_map] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    rw [← hi] at hzero ⊢
    rw [hprime.smoothed_eq_inducing hzero]
    change ‖complexSmoothedCharacterSum (selmerHostInducingCharacter
      (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm
      (selmerSurvivor target e i false false)) x‖ ≤ _
    rw [selmerHostInducingCharacter_untwisted]
    exact hfixed i
  have hauxMem := Finset.mem_sdiff.mpr ⟨hψ, hmem⟩
  rw [selmerSurvivingAuxiliary_eq avg hgroup hkept, Finset.mem_map] at hauxMem
  obtain ⟨i, _, hi⟩ := hauxMem
  rw [← hi] at hzero ⊢
  rw [hprime.smoothed_eq_inducing hzero]
  change ‖complexSmoothedCharacterSum (selmerHostInducingCharacter
    (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm
    (selmerSurvivor target e i.1 i.2.val.1 i.2.val.2)) x‖ ≤ _
  rw [selmerHostInducingCharacter_eq_twistedCharacter]
  calc
    _ ≤ x ^ (1 / 2 + ε) := haux i
    _ ≤ x ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ ≤ B * x ^ (1 + ε) := le_mul_of_one_le_left (by positivity) hB

include hprime in
theorem selmerSurvivors_localVariation_le
    (hx : 3 ≤ x)
    (hG : ∀ ψ ∈ avg.survivors, ‖prime.smoothed ψ x‖ ≤ B * x ^ (1 + ε)) :
    ∀ ψ ∈ avg.survivors, ∀ y : ℝ, |y - x| ≤ 1 →
      ‖prime.smoothed ψ y - prime.smoothed ψ x‖ ≤ 4 + B * x ^ ε := by
  intro ψ hψ y hy
  have hx₀ : 0 < x := by linarith
  have hpower : (B * x ^ ε) * x = B * x ^ (1 + ε) := by
    calc
      _ = B * (x ^ (1 : ℝ) * x ^ ε) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hx₀]
  exact hprime.localVariation_le ψ hx hy (hpower.symm ▸ hG ψ hψ)

end NormAndVariation

local instance selmerHostBaseGroup_isAddCommutative
    (target : BundledDirichletCharacter) (e : ℕ) :
    IsAddCommutative (SelmerHostBaseGroup target e) := ⟨⟨fun a b => add_comm a b⟩⟩

/-- The coset-count condition of Lemma 5.18 for the host top set. -/
def HasSelmerHostCosetCounts {target : BundledDirichletCharacter} {e : ℕ}
    (avg : ExcessAverageData (SelmerHostBaseGroup target e)) (E : ℝ) : Prop :=
  HasCosetEquidistribution avg.tops
    (QuotientAddGroup.mk' (selmerAveragingSubgroup target e)) avg.mainWeight E

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 5.18 turns the (4:3) proportions of the top set on the cosets
of the averaging subgroup into the required character bound. -/
theorem selmerKept_equidistribution_of_coset_counts
    {target : BundledDirichletCharacter} {e : ℕ}
    [Fintype (SelmerHostBaseGroup target e)]
    (avg : ExcessAverageData (SelmerHostBaseGroup target e))
    (hgroup : avg.subgroup = selmerAveragingSubgroup target e)
    (hkept : avg.kept = selmerKeptCharacters target e) (E : ℝ)
    (hcount : HasSelmerHostCosetCounts avg E) :
    ∀ ψ ∈ avg.kept, (∃ t : SelmerHostBaseGroup target e, ψ (0, 0, t) ≠ 1) →
      ‖(∑ t ∈ avg.tops, ψ (0, 0, t)) - ((avg.mainWeight * (avg.tops.card : ℝ) : ℝ) : ℂ)‖ ≤
        orderOf target.character * E := by
  classical
  let H := SelmerHostBaseGroup target e
  let A := selmerAveragingSubgroup target e
  let Q := H ⧸ A
  let f := QuotientAddGroup.mk' A
  let _ : Fintype Q := Fintype.ofFinite _
  intro ψ hψ hnt
  let φ : H →+ Additive ℂ := (ψ.toAddMonoidHom.comp
    ((AddMonoidHom.inr (ZMod 2) (ZMod 2 × H)).comp (AddMonoidHom.inr (ZMod 2) H)))
  have hφ : A ≤ φ.ker := by
    intro u hu
    have hψK : ψ ∈ selmerKeptCharacters target e := hkept ▸ hψ
    have hsurv := selmerKeptCharacters_subset_survivors avg hgroup hψK
    have h := ((avg.mem_survivors ψ).mp hsurv) u (hgroup.symm ▸ hu)
    exact h
  let χ : AddChar Q ℂ := AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift A φ hφ)
  have hval (u : H) : χ (f u) = ψ (0, 0, u) := rfl
  have hχ : χ ≠ 0 := by
    intro h
    obtain ⟨u, hu⟩ := hnt
    exact hu (by rw [← hval, h, AddChar.zero_apply])
  have hcard : Fintype.card Q = orderOf target.character := by
    rw [← Nat.card_eq_fintype_card]
    exact selmerAveragingSubgroup_index target e
  have h := norm_sum_character_sub_expected_le (Q := Q) (fun u : H => f u) χ hχ
    avg.tops avg.mainWeight E hcount
  simpa only [hval, hcard] using h

private theorem edgeLoss_div_normalization_le {H : Type} [AddCommGroup H] [Fintype H]
    (avg : ExcessAverageData H) {x ε : ℝ} (hsizes : ExcessSizeBounds avg.budget x ε)
    (hε : ε ≤ 1 / 52) (hambient : (Fintype.card H : ℝ) ≤ 2 * x ^ (2 + 8 * ε))
    (htail : avg.tailSlope ≤ x ^ (-6 : ℝ)) (hnodes : avg.nodeError ≤ avg.b * x ^ (-6 : ℝ)) :
    avg.edgeLoss x / avg.budget.normalization ≤ 128 := by
  let n : ℝ := Fintype.card H
  let δ := avg.budget.thickDensity
  have hx₁ : 1 ≤ x := by linarith [hsizes.scale_ge_three]
  have hx₀ : 0 < x := zero_lt_one.trans_le hx₁
  have hn : 0 < n := by
    change 0 < (Fintype.card H : ℝ)
    exact_mod_cast hsizes.ambient_pos
  have ht : 0 < (avg.tops.card : ℝ) := by exact_mod_cast hsizes.top_pos
  have hsteps : 0 < (avg.steps : ℝ) := by exact_mod_cast hsizes.steps_pos
  have hthick : 0 < (avg.thickPositions.card : ℝ) := by exact_mod_cast hsizes.thick_pos
  have hb : 0 < avg.b := hsizes.b_pos
  have hδ₀ : 0 < δ := div_pos hthick hn
  have hδ : δ⁻¹ ≤ x := by
    have hlower : x ^ (-ε) ≤ δ := (le_div_iff₀ hn).mpr hsizes.thick_lower
    calc
      _ ≤ (x ^ (-ε))⁻¹ := (inv_le_inv₀ hδ₀ (Real.rpow_pos_of_pos hx₀ _)).mpr hlower
      _ = x ^ ε := by rw [Real.rpow_neg hx₀.le, inv_inv]
      _ ≤ x := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hx₁ (show ε ≤ 1 by linarith)
  have hn₃ : n ≤ 2 * x ^ (3 : ℕ) := by
    apply hambient.trans
    rw [← Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx₁ (by push_cast; linarith : 2 + 8 * ε ≤ ((3 : ℕ) : ℝ)))
      (by norm_num)
  have hnodes' : avg.nodeError / avg.b ≤ x ^ (-6 : ℝ) :=
    (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hnodes)
  have hcard : (Fintype.card (ExcessNode H) : ℝ) = 2 * n := by
    simp [ExcessNode, Fintype.card_prod, ZMod.card, n]
  have hnormal :
      avg.edgeLoss x / avg.budget.normalization =
        8 * n * (x + 1) * avg.tailSlope * δ⁻¹ +
          24 * n * (x + 1) * (avg.nodeError / avg.b) * δ⁻¹ := by
    rw [ExcessAverageData.edgeLoss, ExcessAverageData.edgeLossPerPair, hcard]
    change (avg.tops.card : ℝ) * avg.steps *
      (2 * (2 * n) * avg.tailSlope * (x + 1) * avg.b +
        6 * (2 * n) * (x + 1) * avg.nodeError) /
        ((avg.tops.card : ℝ) * avg.steps * avg.b * δ / 2) = _
    field_simp [ht.ne', hsteps.ne', hb.ne', hδ₀.ne']
    ring
  rw [hnormal]
  calc
    _ ≤ 8 * n * (x + 1) * x ^ (-6 : ℝ) * δ⁻¹ +
        24 * n * (x + 1) * x ^ (-6 : ℝ) * δ⁻¹ := by
      have hδn : 0 ≤ δ⁻¹ := by positivity
      have h8 : 0 ≤ 8 * n * (x + 1) := by positivity
      have h24 : 0 ≤ 24 * n * (x + 1) := by positivity
      exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail h8) hδn)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnodes' h24) hδn)
    _ = 32 * n * (x + 1) * x ^ (-6 : ℝ) * δ⁻¹ := by ring
    _ ≤ 32 * (2 * x ^ (3 : ℕ)) * (2 * x) * x ^ (-6 : ℝ) * x := by
      have hx' : x + 1 ≤ 2 * x := by linarith
      gcongr
    _ = 128 / x := by
      rw [Real.rpow_neg hx₀.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
      norm_num
    _ ≤ 128 := (div_le_iff₀ hx₀).mpr (by linarith)

private theorem survivor_correction_le (target : BundledDirichletCharacter) {e : ℕ}
    [Fintype (SelmerHostBaseGroup target e)]
    (avg : ExcessAverageData (SelmerHostBaseGroup target e))
    (G : ExcessCharacter (SelmerHostBaseGroup target e) → ℝ → ℂ)
    {x ε B : ℝ} (hx₁ : 1 ≤ x) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hgroup : avg.subgroup = selmerAveragingSubgroup target e)
    (hkept : avg.kept = selmerKeptCharacters target e)
    (hequi : avg.equidistributionError ≤ (orderOf target.character : ℝ) * x ^ (-1 + ε))
    (hlocal : avg.localVariation ≤ 4 + B * x ^ ε)
    (hnorm : ∀ ψ ∈ avg.kept, ‖G ψ x‖ ≤ B * x ^ (1 + ε)) :
    avg.correction G x ≤
      ((orderOf target.character : ℝ) ^ 2 * B +
        4 * (orderOf target.character : ℝ) * (4 + B)) * x ^ (2 * ε) := by
  let o : ℝ := orderOf target.character
  have ho : 0 ≤ o := by positivity
  have hx₀ := zero_lt_one.trans_le hx₁
  have hK : (avg.kept.card : ℝ) = o := by
    simp [hkept, selmerKeptCharacters, o]
  have hS : (avg.survivors.card : ℝ) = 4 * o := by
    rw [selmerSurvivors_card avg hgroup hkept]
    push_cast
    rfl
  have hsum₀ : 0 ≤ ∑ ψ ∈ avg.kept, ‖G ψ x‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsum : (∑ ψ ∈ avg.kept, ‖G ψ x‖) ≤ o * (B * x ^ (1 + ε)) := by
    calc
      _ ≤ ∑ _ψ ∈ avg.kept, B * x ^ (1 + ε) := Finset.sum_le_sum hnorm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hK]
  have hfirst :
      avg.equidistributionError * (∑ ψ ∈ avg.kept, ‖G ψ x‖) ≤ o ^ 2 * B * x ^ (2 * ε) := by
    calc
      _ ≤ (o * x ^ (-1 + ε)) * (o * (B * x ^ (1 + ε))) :=
        mul_le_mul hequi hsum hsum₀ (by positivity)
      _ = o ^ 2 * B * (x ^ (-1 + ε) * x ^ (1 + ε)) := by ring
      _ = _ := by rw [← Real.rpow_add hx₀, show -1 + ε + (1 + ε) = 2 * ε by ring]
  have hone : 1 ≤ x ^ (2 * ε) := Real.one_le_rpow hx₁ (by positivity)
  have hxε : x ^ ε ≤ x ^ (2 * ε) := Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)
  have hsecond : avg.localVariation ≤ (4 + B) * x ^ (2 * ε) := by
    apply hlocal.trans
    rw [add_mul]
    exact add_le_add (by linarith [mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 4)])
      (mul_le_mul_of_nonneg_left hxε hB)
  rw [ExcessAverageData.correction, hS]
  calc
    _ ≤ o ^ 2 * B * x ^ (2 * ε) + 4 * o * ((4 + B) * x ^ (2 * ε)) :=
      add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ = _ := by ring

/-- Polynomially small node and tail errors and the coset equidistribution
bound suffice for the normalization allowance in Corollary 4.4. The
threshold is uniform in the dyadic exponent and the moving host. -/
theorem selmerCorrections_eventually_le (target : BundledDirichletCharacter) {ε C B : ℝ}
    (hε : 0 < ε) (hε₀ : ε ≤ 1 / 52) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∀ᶠ x in atTop, ∀ (e : ℕ) [Fintype (SelmerHostBaseGroup target e)]
      (avg : ExcessAverageData (SelmerHostBaseGroup target e))
      (G : ExcessCharacter (SelmerHostBaseGroup target e) → ℝ → ℂ),
      ExcessSizeBounds avg.budget x ε →
      (Fintype.card (SelmerHostBaseGroup target e) : ℝ) ≤ 2 * x ^ (2 + 8 * ε) →
      avg.subgroup = selmerAveragingSubgroup target e → avg.kept = selmerKeptCharacters target e →
      avg.tailSlope ≤ x ^ (-6 : ℝ) → avg.nodeError ≤ avg.b * x ^ (-6 : ℝ) →
      avg.equidistributionError ≤ (orderOf target.character : ℝ) * x ^ (-1 + ε) →
      avg.localVariation ≤ 4 + B * x ^ ε →
      (∀ ψ ∈ avg.kept, ‖G ψ x‖ ≤ B * x ^ (1 + ε)) →
      avg.edgeLoss x / avg.budget.normalization + avg.correction G x ≤
        (3 / 13 : ℝ) * x ^ (1 / 2 + (C + 3) * ε) := by
  let o : ℝ := orderOf target.character
  let K := o ^ 2 * B + 4 * o * (4 + B)
  have hε' : 0 < (1 / 2 : ℝ) + ε := by linarith
  have hgrow : ∀ᶠ x in atTop, (128 + K) * (13 / 3 : ℝ) ≤ x ^ (1 / 2 + ε) :=
    (tendsto_rpow_atTop hε').eventually_ge_atTop _
  filter_upwards [hgrow] with x hx e inst avg G hs hambient hgroup hkept htail hnodes hequi hlocal hnorm
  have hx₁ : 1 ≤ x := by linarith [hs.scale_ge_three]
  have hx₀ : 0 < x := zero_lt_one.trans_le hx₁
  have hEdge := edgeLoss_div_normalization_le avg hs hε₀ hambient htail hnodes
  have hCorr := survivor_correction_le target avg G hx₁ hε.le hB hgroup hkept hequi hlocal hnorm
  have hpow : 1 ≤ x ^ (2 * ε) := Real.one_le_rpow hx₁ (by positivity)
  have hK : 128 + K ≤ (3 / 13 : ℝ) * x ^ (1 / 2 + ε) := by linarith
  calc
    _ ≤ 128 + K * x ^ (2 * ε) := add_le_add hEdge hCorr
    _ ≤ (128 + K) * x ^ (2 * ε) := by rw [add_mul]; linarith
    _ ≤ (3 / 13 : ℝ) * x ^ (1 / 2 + ε) * x ^ (2 * ε) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (3 / 13 : ℝ) * x ^ (1 / 2 + 3 * ε) := by
      rw [mul_assoc, ← Real.rpow_add hx₀, show 1 / 2 + ε + 2 * ε = 1 / 2 + 3 * ε by ring]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le hx₁ (by nlinarith)

/-- The target tail slope in §6.3 eventually meets the polynomial slack
used in the edge error estimate. -/
theorem eventually_selmerTailSlope_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-(x ^ (ε / 8))) ≤ x ^ (-6 : ℝ) := by
  have hlog := (isLittleO_log_rpow_atTop (show 0 < ε / 8 by positivity)).bound
    (by norm_num : (0 : ℝ) < 1 / 6)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℝ)] with x h hx
  have hx₀ := zero_lt_one.trans_le hx
  rw [Real.norm_of_nonneg (Real.log_nonneg hx), Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _)] at h
  rw [Real.rpow_def_of_pos hx₀ (-6)]
  exact Real.exp_le_exp.mpr (by linarith)

end Riemann
