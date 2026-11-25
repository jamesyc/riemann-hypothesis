module

public import Riemann.ChainRecord
public import Riemann.PrimeExcess
public import Mathlib.Algebra.Order.BigOperators.Expect

@[expose] public section

open Utilities
open scoped BigOperators Classical

namespace Riemann

/-- The data used in the finite-group averaging step at a single scale. -/
structure ExcessAverageData (H : Type*) [AddCommGroup H] where
  subgroup : AddSubgroup H
  tops : Finset H
  thickPositions : Finset H
  kept : Finset (ExcessCharacter H)
  steps : ℕ
  a : ℝ
  b : ℝ
  k : ℝ
  thinScale : ℝ
  thinCutoff : ℝ
  nodeError : ℝ
  tailSlope : ℝ
  localVariation : ℝ
  mainWeight : ℝ
  equidistributionError : ℝ
  topWeight : H → ℝ
  nodeWeight : H → Fin steps → ExcessNode H → ℝ

namespace ExcessAverageData

variable {H : Type*} [AddCommGroup H] [Fintype H]

def budget (d : ExcessAverageData H) : ExcessBudget where
  ambientCount := Fintype.card H
  topCount := d.tops.card
  thickCount := d.thickPositions.card
  steps := d.steps
  a := d.a
  b := d.b
  k := d.k

def IsThick (d : ExcessAverageData H) (u : H) (g : ExcessNode H) : Prop :=
  g.1 = 1 ∧ g.2 - u ∈ d.thickPositions

noncomputable def survivors (d : ExcessAverageData H) : Finset (ExcessCharacter H) := by
  classical
  exact Finset.univ.filter fun ψ => ∀ u ∈ d.subgroup, ψ (0, 0, u) = 1

@[simp] theorem mem_survivors (d : ExcessAverageData H) (ψ : ExcessCharacter H) :
    ψ ∈ d.survivors ↔ ∀ u ∈ d.subgroup, ψ (0, 0, u) = 1 := by
  classical
  simp [survivors]

noncomputable def coefficient (d : ExcessAverageData H) (ψ : ExcessCharacter H) : ℝ := by
  classical
  exact if ∀ t : H, ψ (0, 0, t) = 1 then 1 else d.mainWeight

noncomputable def mainValue (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ)
    (x : ℝ) : ℝ :=
  ∑ ψ ∈ d.kept, d.coefficient ψ * (G ψ x).re

noncomputable def auxiliaryValue (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ)
    (x : ℝ) : ℝ := by
  classical
  exact ∑ ψ ∈ d.survivors \ d.kept, ‖G ψ x‖

noncomputable def correction (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ)
    (x : ℝ) : ℝ :=
  d.equidistributionError * (∑ ψ ∈ d.kept, ‖G ψ x‖) +
    (d.survivors.card : ℝ) * d.localVariation

noncomputable def edgeLossPerPair (d : ExcessAverageData H) (x : ℝ) : ℝ :=
  2 * Fintype.card (ExcessNode H) * d.tailSlope * (x + 1) * d.b +
    6 * Fintype.card (ExcessNode H) * (x + 1) * d.nodeError

noncomputable def edgeLoss (d : ExcessAverageData H) (x : ℝ) : ℝ :=
  (d.tops.card : ℝ) * d.steps * d.edgeLossPerPair x

/-- The excess with each thick node frozen at `b` and the thin nodes omitted. -/
noncomputable def frozenThickExcess (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ)
    (u t : H) : ℂ := by
  classical
  exact (Fintype.card (ExcessNode H) : ℂ)⁻¹ * ∑ g : ExcessNode H,
    ∑ ψ : ExcessCharacter H, star (ψ (1, g)) *
      (if d.IsThick u (translateExcessNode t g) then
        (d.b : ℂ) * G ψ (d.topWeight t / d.b) else 0)

noncomputable def excessAt (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ)
    (u : H) : ℝ :=
  ∑ t ∈ d.tops, ∑ j : Fin d.steps, (excessSum G (d.topWeight t) t (d.nodeWeight u j)).re

noncomputable def averagedExcess (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ) :
    ℝ :=
  𝔼 u ∈ subgroupElements d.subgroup, d.excessAt G u

private theorem subgroupElements_nonempty (d : ExcessAverageData H) :
    (subgroupElements d.subgroup).Nonempty :=
  ⟨0, mem_subgroupElements.mpr d.subgroup.zero_mem⟩

theorem averagedExcess_le_of_pointwise (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ)
    {bound : ℝ} (h : ∀ u ∈ d.subgroup, d.excessAt G u ≤ bound) :
    d.averagedExcess G ≤ bound :=
  Finset.expect_le d.subgroupElements_nonempty fun u hu => h u (mem_subgroupElements.mp hu)

noncomputable def accountingTopMass (d : ExcessAverageData H) : ℝ :=
  ∑ t ∈ d.tops, d.topWeight t

noncomputable def accountingBaseTerm (d : ExcessAverageData H) (v ell : ℝ) : ℝ :=
  let logOmega := Real.eulerMascheroniConstant + Real.log (Real.pi / v) - ell
  (d.steps : ℝ) * ∑ t ∈ d.tops, d.topWeight t * (Real.log (d.topWeight t) - 1 - logOmega)

noncomputable def accountingNodeLogSum (d : ExcessAverageData H) (u : H) (v : ℝ) : ℝ :=
  ∑ j : Fin d.steps,
    (∑ ρ : ExcessNode H, Real.log (d.nodeWeight u j ρ * v / Real.pi)) /
      Fintype.card (ExcessNode H)

noncomputable def meanNodeLog (d : ExcessAverageData H) (u : H) (j : Fin d.steps) : ℝ :=
  averageLogNode (d.nodeWeight u j)

/-- The main term of (3.8), also obtained by summing the main terms in (3.10). -/
noncomputable def primeMainTerm (d : ExcessAverageData H) (u : H) (ell : ℝ) : ℝ :=
  ∑ j : Fin d.steps, ∑ t ∈ d.tops, excessMainTerm (d.topWeight t) ell (d.nodeWeight u j)

noncomputable def primeSumOf (d : ExcessAverageData H) (prime : PrimeExcessData H)
    (u : H) : ℝ :=
  ∑ j : Fin d.steps, ∑ t ∈ d.tops,
    prime.primeSide (d.topWeight t) t (d.nodeWeight u j)

theorem primeSumOf_eq_main_add_excess (d : ExcessAverageData H) {prime : PrimeExcessData H}
    (hprime : PrimeExcessHypotheses prime) (u : H)
    (htop : ∀ t ∈ d.tops, 0 < d.topWeight t) (hnode : ∀ j ρ, 0 < d.nodeWeight u j ρ) :
    d.primeSumOf prime u = d.primeMainTerm u (prime.logDerivativeAtOne prime.quadratic).re +
      d.excessAt prime.smoothed u := by
  have hswap : (∑ j : Fin d.steps, ∑ t ∈ d.tops,
      (excessSum prime.smoothed (d.topWeight t) t (d.nodeWeight u j)).re) =
      d.excessAt prime.smoothed u := by
    unfold excessAt
    exact Finset.sum_comm
  calc
    d.primeSumOf prime u =
      ∑ j : Fin d.steps, ∑ t ∈ d.tops,
        (excessMainTerm (d.topWeight t) (prime.logDerivativeAtOne prime.quadratic).re
          (d.nodeWeight u j) +
          (excessSum prime.smoothed (d.topWeight t) t (d.nodeWeight u j)).re) := by
      unfold primeSumOf
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t ht =>
        primeSide_eq_main_add_excess hprime (htop t ht) t (hnode j)
    _ = _ := by
      simp_rw [primeMainTerm, ← hswap, Finset.sum_add_distrib]

theorem accounting_mainTerm_eq_primeMainTerm (d : ExcessAverageData H) (u : H)
    {v : ℝ} (hv : 0 < v) (ell : ℝ) (hnode : ∀ j ρ, 0 < d.nodeWeight u j ρ) :
    d.accountingBaseTerm v ell - d.accountingTopMass * d.accountingNodeLogSum u v =
      d.primeMainTerm u ell := by
  let f : ℝ := Fintype.card (ExcessNode H)
  let periodLog := Real.log (v / Real.pi)
  let logOmega := Real.eulerMascheroniConstant + Real.log (Real.pi / v) - ell
  have hf : f ≠ 0 := by
    dsimp [f]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ExcessNode H) ≠ 0)
  have hperiod : logOmega + periodLog = Real.eulerMascheroniConstant - ell := by
    dsimp [logOmega, periodLog]
    rw [Real.log_div Real.pi_ne_zero hv.ne', Real.log_div hv.ne' Real.pi_ne_zero]
    ring
  have hmean (j : Fin d.steps) :
      (∑ ρ : ExcessNode H, Real.log (d.nodeWeight u j ρ * v / Real.pi)) / f =
        d.meanNodeLog u j + periodLog := by
    have hlog (ρ : ExcessNode H) :
        Real.log (d.nodeWeight u j ρ * v / Real.pi) =
          Real.log (d.nodeWeight u j ρ) + periodLog := by
      rw [mul_div_assoc, Real.log_mul (hnode j ρ).ne' (div_pos hv Real.pi_pos).ne']
    simp_rw [hlog]
    rw [Finset.sum_add_distrib, add_div]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold meanNodeLog averageLogNode
    change (∑ ρ : ExcessNode H, Real.log (d.nodeWeight u j ρ)) / f +
      f * periodLog / f = (∑ ρ : ExcessNode H, Real.log (d.nodeWeight u j ρ)) / f + periodLog
    rw [mul_comm f periodLog, mul_div_cancel_right₀ _ hf]
  let base := ∑ t ∈ d.tops, d.topWeight t * (Real.log (d.topWeight t) - 1 - logOmega)
  have hrow (j : Fin d.steps) :
      (∑ t ∈ d.tops, d.topWeight t *
        (Real.log (d.topWeight t) - 1 - Real.eulerMascheroniConstant + ell - d.meanNodeLog u j)) =
        base - d.accountingTopMass * (d.meanNodeLog u j + periodLog) := by
    dsimp only [base, accountingTopMass]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [← mul_sub]
    congr 1
    linarith
  unfold accountingBaseTerm accountingNodeLogSum primeMainTerm excessMainTerm
  change (d.steps : ℝ) * base - d.accountingTopMass *
    (∑ j : Fin d.steps, (∑ ρ : ExcessNode H,
      Real.log (d.nodeWeight u j ρ * v / Real.pi)) / f) =
      ∑ j : Fin d.steps, ∑ t ∈ d.tops, d.topWeight t *
        (Real.log (d.topWeight t) - 1 - Real.eulerMascheroniConstant + ell - d.meanNodeLog u j)
  simp_rw [hmean, hrow, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [nsmul_eq_mul]

end ExcessAverageData

/-- The node, character, and local-variation assumptions of Theorem 4.2. -/
structure ExcessAverageHypotheses {H : Type*} [AddCommGroup H] [Fintype H]
    (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ) (x : ℝ) : Prop where
  scale_ge_three : 3 ≤ x
  tops_nonempty : d.tops.Nonempty
  thick_nonempty : d.thickPositions.Nonempty
  thick_subset : ∀ u ∈ d.thickPositions, u ∈ d.subgroup
  kept_subset : d.kept ⊆ d.survivors
  kept_zero : 0 ∈ d.kept
  kept_sign : ∀ ψ ∈ d.kept, ψ (1, 0, 0) = 1
  weight_nonneg : 0 ≤ d.mainWeight
  equidistribution_nonneg : 0 ≤ d.equidistributionError
  equidistribution : ∀ ψ ∈ d.kept,
    (∃ t : H, ψ (0, 0, t) ≠ 1) →
    ‖(∑ t ∈ d.tops, ψ (0, 0, t)) - ((d.mainWeight * (d.tops.card : ℝ) : ℝ) : ℂ)‖ ≤
      d.equidistributionError * d.tops.card
  b_pos : 0 < d.b
  thinScale_pos : 0 < d.thinScale
  thinCutoff_pos : 0 < d.thinCutoff
  thin_size : d.thinScale * d.thinCutoff ≤ x * d.b
  nodeError_nonneg : 0 ≤ d.nodeError
  nodeError_le : d.nodeError ≤ d.b
  tailSlope_nonneg : 0 ≤ d.tailSlope
  variation_nonneg : 0 ≤ d.localVariation
  steps_pos : 0 < d.steps
  topWeight_pos : ∀ t ∈ d.tops, 0 < d.topWeight t
  topWeight_close : ∀ t ∈ d.tops, |d.topWeight t / d.b - x| ≤ 1
  nodeWeight_pos : ∀ u ∈ d.subgroup, ∀ j : Fin d.steps, ∀ g, 0 < d.nodeWeight u j g
  thick_bounds : ∀ u ∈ d.subgroup, ∀ j : Fin d.steps, ∀ g, d.IsThick u g →
    d.b ≤ d.nodeWeight u j g ∧ d.nodeWeight u j g ≤ d.b + d.nodeError
  thin_bound : ∀ u ∈ d.subgroup, ∀ j : Fin d.steps, ∀ g, ¬d.IsThick u g →
    d.nodeWeight u j g ≤ 2 * d.thinScale
  weightedVariation : ∀ (ψ : ExcessCharacter H) (A w w' : ℝ),
    0 < A → 0 < w → w ≤ A → 0 < w' → w' ≤ A →
    ‖(w : ℂ) * G ψ (A / w) - (w' : ℂ) * G ψ (A / w')‖ ≤
      3 * A * |w - w'| / min w w'
  local_bound : ∀ (ψ : ExcessCharacter H), ψ ∈ d.survivors → ∀ y : ℝ, |y - x| ≤ 1 →
    ‖G ψ y - G ψ x‖ ≤ d.localVariation
  tail_bound : ∀ (ψ : ExcessCharacter H) (y : ℝ), d.thinCutoff / 3 ≤ y →
    ‖G ψ y‖ ≤ d.tailSlope * y

/-- Thin nodes may be discarded and thick nodes frozen with the loss in (4.5). -/
private theorem norm_excessSum_sub_frozenThickExcess_le
    {H : Type*} [AddCommGroup H] [Fintype H]
    {d : ExcessAverageData H} {G : ExcessCharacter H → ℝ → ℂ} {x : ℝ}
    (h : ExcessAverageHypotheses d G x) {u t : H} (hu : u ∈ d.subgroup) (ht : t ∈ d.tops)
    (j : Fin d.steps) :
    ‖excessSum G (d.topWeight t) t (d.nodeWeight u j) - d.frozenThickExcess G u t‖ ≤
      d.edgeLossPerPair x := by
  classical
  let A := d.topWeight t
  let f := (Fintype.card (ExcessNode H) : ℝ)
  let thinLoss := d.tailSlope * (x + 1) * d.b
  let thickLoss := 3 * (x + 1) * d.nodeError
  have hA : 0 < A := h.topWeight_pos t ht
  have hx : 0 ≤ x + 1 := by linarith [h.scale_ge_three]
  have hthinLoss : 0 ≤ thinLoss := mul_nonneg (mul_nonneg h.tailSlope_nonneg hx) h.b_pos.le
  have hthickLoss : 0 ≤ thickLoss := mul_nonneg (mul_nonneg (by norm_num) hx) h.nodeError_nonneg
  have hf : 0 < f := Nat.cast_pos.mpr Fintype.card_pos
  have hchar : (Fintype.card (ExcessCharacter H) : ℝ) = 2 * f := by
    rw [AddChar.card_eq]
    change (Fintype.card (ZMod 2 × ExcessNode H) : ℝ) = _
    rw [Fintype.card_prod, Nat.cast_mul, ZMod.card]
    norm_num [f]
  have hclose := abs_le.mp (h.topWeight_close t ht)
  have hbelow : (x - 1) * d.b ≤ A :=
    (le_div_iff₀ h.b_pos).mp (by linarith [hclose.1])
  have habove : A ≤ (x + 1) * d.b :=
    (div_le_iff₀ h.b_pos).mp (by linarith [hclose.2])
  let w (g : ExcessNode H) := d.nodeWeight u j (translateExcessNode t g)
  let actual (g : ExcessNode H) (ψ : ExcessCharacter H) := (w g : ℂ) * G ψ (A / w g)
  let frozen (g : ExcessNode H) (ψ : ExcessCharacter H) :=
    if d.IsThick u (translateExcessNode t g) then (d.b : ℂ) * G ψ (A / d.b) else 0
  have hterm (g : ExcessNode H) (ψ : ExcessCharacter H) :
      ‖actual g ψ - frozen g ψ‖ ≤ thinLoss + thickLoss := by
    have hw : 0 < w g := h.nodeWeight_pos u hu j _
    by_cases hg : d.IsThick u (translateExcessNode t g)
    · have ⟨hwb, hbw⟩ := h.thick_bounds u hu j _ hg
      change d.b ≤ w g at hwb
      change w g ≤ d.b + d.nodeError at hbw
      have htwo : 2 * d.b ≤ A := by
        apply le_trans _ hbelow
        exact mul_le_mul_of_nonneg_right (by linarith [h.scale_ge_three]) h.b_pos.le
      have hwA : w g ≤ A := by linarith [h.nodeError_le]
      have hbA : d.b ≤ A := hwb.trans hwA
      have hchange := h.weightedVariation ψ A (w g) d.b hA hw hwA h.b_pos hbA
      rw [min_eq_right hwb, abs_of_nonneg (sub_nonneg.mpr hwb)] at hchange
      simp only [actual, frozen, ite_eq_left hg]
      calc
        _ ≤ 3 * A * (w g - d.b) / d.b := hchange
        _ ≤ 3 * A * d.nodeError / d.b :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) h.b_pos.le
        _ = 3 * (A / d.b) * d.nodeError := by ring
        _ ≤ thickLoss := by
          dsimp only [thickLoss]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ((div_le_iff₀ h.b_pos).mpr habove) (by norm_num))
            h.nodeError_nonneg
        _ ≤ _ := le_add_of_nonneg_left hthinLoss
    · have hsmall : w g ≤ 2 * d.thinScale := h.thin_bound u hu j _ hg
      have hratio : d.thinCutoff / 3 ≤ A / w g := by
        apply (le_div_iff₀ hw).mpr
        calc
          _ ≤ d.thinCutoff / 3 * (2 * d.thinScale) :=
            mul_le_mul_of_nonneg_left hsmall (by positivity [h.thinCutoff_pos])
          _ = (2 / 3 : ℝ) * (d.thinScale * d.thinCutoff) := by ring
          _ ≤ (2 / 3 : ℝ) * (x * d.b) := mul_le_mul_of_nonneg_left h.thin_size (by norm_num)
          _ = (2 / 3 * x) * d.b := by ring
          _ ≤ (x - 1) * d.b :=
            mul_le_mul_of_nonneg_right (by linarith [h.scale_ge_three]) h.b_pos.le
          _ ≤ A := hbelow
      simp only [actual, frozen, ite_eq_right hg, sub_zero, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hw.le]
      calc
        _ ≤ w g * (d.tailSlope * (A / w g)) :=
          mul_le_mul_of_nonneg_left (h.tail_bound ψ _ hratio) hw.le
        _ = d.tailSlope * A := by field_simp [hw.ne']
        _ ≤ thinLoss := by
          dsimp only [thinLoss]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left habove h.tailSlope_nonneg
        _ ≤ _ := le_add_of_nonneg_right hthickLoss
  let term (g : ExcessNode H) (ψ : ExcessCharacter H) :=
    star (ψ (1, g)) * (actual g ψ - frozen g ψ)
  have hbound : ‖∑ g : ExcessNode H, ∑ ψ : ExcessCharacter H, term g ψ‖ ≤
      f * (2 * f) * (thinLoss + thickLoss) := by
    calc
      _ ≤ ∑ _g : ExcessNode H, ∑ _ψ : ExcessCharacter H, (thinLoss + thickLoss) := by
        refine norm_sum_le_of_le _ fun g _ => norm_sum_le_of_le _ fun ψ _ => ?_
        simpa only [term, norm_mul, Complex.star_def, Complex.norm_conj, ψ.norm_apply, one_mul]
          using hterm g ψ
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hchar, f]
        ring
  have heq : excessSum G A t (d.nodeWeight u j) - d.frozenThickExcess G u t =
      (Fintype.card (ExcessNode H) : ℂ)⁻¹ *
        ∑ g : ExcessNode H, ∑ ψ : ExcessCharacter H, term g ψ := by
    unfold excessSum ExcessAverageData.frozenThickExcess
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ψ _ => by
      simp only [term, actual, frozen, A, w]
      ring
  calc
    _ = f⁻¹ * ‖∑ g : ExcessNode H, ∑ ψ : ExcessCharacter H, term g ψ‖ := by
      rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ f⁻¹ * (f * (2 * f) * (thinLoss + thickLoss)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hf.le)
    _ = _ := by
      rw [mul_assoc f, inv_mul_cancel_left₀ hf.ne']
      dsimp only [thinLoss, thickLoss, f, ExcessAverageData.edgeLossPerPair]
      ring

/-- The thick outside nodes are indexed by the translated thick positions. -/
private theorem sum_thick_positions
    {H : Type*} [AddCommGroup H] [Fintype H] (d : ExcessAverageData H) (u t : H)
    (F : ExcessNode H → ℂ) :
    (∑ g : ExcessNode H, if d.IsThick u (translateExcessNode t g) then F g else 0) =
      ∑ s ∈ d.thickPositions, F (0, s + u - t) := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun s _ => (0, s + u - t)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro s hs
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ⟨by simp [translateExcessNode], by simpa [translateExcessNode] using hs⟩
  · intro s _ s' _ h
    have heq : s + u - t = s' + u - t := congrArg Prod.snd h
    exact add_right_cancel (sub_left_inj.mp heq)
  · intro g hg
    have hg' := (Finset.mem_filter.mp hg).2
    have hfst : g.1 + 1 = 1 := hg'.1
    refine ⟨g.2 + t - u, hg'.2, Prod.ext ?_ ?_⟩
    · exact (add_right_cancel (show g.1 + 1 = 0 + 1 by simpa using hfst)).symm
    · simp

private theorem frozenThickExcess_eq_sum
    {H : Type*} [AddCommGroup H] [Fintype H] (d : ExcessAverageData H)
    (G : ExcessCharacter H → ℝ → ℂ) (u t : H) :
    d.frozenThickExcess G u t =
      (Fintype.card (ExcessNode H) : ℂ)⁻¹ * ∑ ψ : ExcessCharacter H,
        (∑ s ∈ d.thickPositions, star (ψ (1, 0, s + u - t))) *
          ((d.b : ℂ) * G ψ (d.topWeight t / d.b)) := by
  classical
  unfold ExcessAverageData.frozenThickExcess
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [← sum_thick_positions d u t (fun g => star (ψ (1, g)))]
  simp only [Finset.sum_mul, ite_mul, mul_ite, zero_mul, mul_zero]

private noncomputable def thickPhase {H : Type*} [AddCommGroup H]
    (ψ : ExcessCharacter H) (t : H) : ℂ :=
  star (ψ (1, 0, 0)) * ψ (0, 0, t)

private theorem norm_thickPhase {H : Type*} [AddCommGroup H] [Fintype H]
    (ψ : ExcessCharacter H) (t : H) : ‖thickPhase ψ t‖ = 1 := by
  simp only [thickPhase, norm_mul, Complex.star_def, Complex.norm_conj, ψ.norm_apply, mul_one]

/-- Averaging a thick coefficient kills the characters nontrivial on the subgroup. -/
private theorem mean_thick_character
    {H : Type*} [AddCommGroup H] [Fintype H]
    {d : ExcessAverageData H} {G : ExcessCharacter H → ℝ → ℂ} {x : ℝ}
    (h : ExcessAverageHypotheses d G x) (ψ : ExcessCharacter H) (t : H) :
    (𝔼 u ∈ subgroupElements d.subgroup, ∑ s ∈ d.thickPositions, star (ψ (1, 0, s + u - t))) =
      if ψ ∈ d.survivors then (d.thickPositions.card : ℂ) * thickPhase ψ t else 0 := by
  classical
  let incl : H →+ ExcessGroup H :=
    { toFun := fun v => (0, 0, v)
      map_zero' := rfl
      map_add' := fun _ _ => by simp [Prod.mk_add_mk] }
  let χ := ψ.compAddMonoidHom incl
  let sign := star (ψ (1, 0, 0))
  have hphase (s u : H) :
      star (ψ (1, 0, s + u - t)) = sign * (-χ) (s - t + u) := by
    have heq : ((1, 0, s + u - t) : ExcessGroup H) = (1, 0, 0) + (0, 0, s - t + u) := by
      have hlast : s + u - t = s - t + u := by abel
      simp [Prod.mk_add_mk, hlast]
    rw [heq, ψ.map_add_eq_mul, star_mul]
    have hstar : star (ψ (0, 0, s - t + u)) = (-χ) (s - t + u) := by
      rw [Complex.star_def, AddChar.neg_apply, χ.map_neg_eq_conj]
      rfl
    rw [hstar, mul_comm]
  have htriv : (∀ v ∈ d.subgroup, (-χ) v = 1) ↔ ψ ∈ d.survivors := by
    rw [d.mem_survivors]
    have hvalue (v : H) : χ v = ψ (0, 0, v) := rfl
    simp only [AddChar.neg_apply', inv_eq_one, hvalue]
  have hshift (s : H) (hs : s ∈ d.thickPositions) (hψ : ψ ∈ d.survivors) :
      (-χ) (s - t) = ψ (0, 0, t) := by
    rw [AddChar.neg_apply, neg_sub]
    change χ (t - s) = χ t
    have hs1 : χ s = 1 := (d.mem_survivors ψ).mp hψ s (h.thick_subset s hs)
    rw [χ.map_sub_eq_div, hs1, div_one]
  calc
    _ = ∑ s ∈ d.thickPositions, sign * characterCosetAverage d.subgroup (s - t) (-χ) := by
      rw [Finset.expect_sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [characterCosetAverage, Finset.expect_eq_sum_div_card, div_eq_inv_mul, hphase,
        ← Finset.mul_sum]
      ring
    _ = _ := by
      simp_rw [characterCosetAverage_eq_ite, htriv]
      by_cases hψ : ψ ∈ d.survivors
      · rw [ite_eq_left hψ]
        calc
          _ = ∑ _s ∈ d.thickPositions, sign * ψ (0, 0, t) := by
            exact Finset.sum_congr rfl fun s hs => by simp [hψ, hshift s hs hψ]
          _ = _ := by simp [thickPhase, sign, nsmul_eq_mul]
      · simp [hψ]

private noncomputable def thickScale {H : Type*} [AddCommGroup H] [Fintype H]
    (d : ExcessAverageData H) : ℝ :=
  (d.thickPositions.card : ℝ) * d.b / Fintype.card (ExcessNode H)

/-- The mean frozen thick contribution at one top position. -/
private theorem mean_frozenThickExcess
    {H : Type*} [AddCommGroup H] [Fintype H]
    {d : ExcessAverageData H} {G : ExcessCharacter H → ℝ → ℂ} {x : ℝ}
    (h : ExcessAverageHypotheses d G x) (t : H) :
    (𝔼 u ∈ subgroupElements d.subgroup, (d.frozenThickExcess G u t).re) =
      thickScale d * ∑ ψ ∈ d.survivors, (thickPhase ψ t * G ψ (d.topWeight t / d.b)).re := by
  classical
  have hcomplex :
      (𝔼 u ∈ subgroupElements d.subgroup, d.frozenThickExcess G u t) =
        (thickScale d : ℂ) * ∑ ψ ∈ d.survivors, thickPhase ψ t * G ψ (d.topWeight t / d.b) := by
    simp_rw [frozenThickExcess_eq_sum, ← Finset.mul_expect, Finset.expect_sum_comm,
      ← Finset.expect_mul, mean_thick_character h, ite_mul, zero_mul]
    have hfilter : (Finset.univ.filter (· ∈ d.survivors)) = d.survivors := by
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Finset.sum_filter, hfilter, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [thickScale, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]
    ring
  simpa only [Complex.re_expect, Complex.re_ofReal_mul, Complex.re_sum] using
    congrArg Complex.re hcomplex

/-- The top-position sum after replacing the arguments by the common scale. -/
private theorem mainValue_le_fixedTopSum
    {H : Type*} [AddCommGroup H] [Fintype H]
    {d : ExcessAverageData H} {G : ExcessCharacter H → ℝ → ℂ} {x : ℝ}
    (h : ExcessAverageHypotheses d G x) :
    (d.tops.card : ℝ) * (d.mainValue G x -
      d.equidistributionError * (∑ ψ ∈ d.kept, ‖G ψ x‖) - d.auxiliaryValue G x) ≤
      ∑ t ∈ d.tops, ∑ ψ ∈ d.survivors, (thickPhase ψ t * G ψ x).re := by
  classical
  let N := (d.tops.card : ℝ)
  let S (ψ : ExcessCharacter H) := ∑ t ∈ d.tops, ψ (0, 0, t)
  let P (ψ : ExcessCharacter H) := star (ψ (1, 0, 0)) * S ψ
  let R (ψ : ExcessCharacter H) := (P ψ * G ψ x).re
  have hfixed : (∑ t ∈ d.tops, ∑ ψ ∈ d.survivors, (thickPhase ψ t * G ψ x).re) =
      ∑ ψ ∈ d.survivors, R ψ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [R, P, S, thickPhase, Finset.mul_sum, Finset.sum_mul, Complex.re_sum]
  have hkept (ψ : ExcessCharacter H) (hψ : ψ ∈ d.kept) :
      N * (d.coefficient ψ * (G ψ x).re - d.equidistributionError * ‖G ψ x‖) ≤ R ψ := by
    let c := d.coefficient ψ * N
    have hcoef : ‖P ψ - (c : ℂ)‖ ≤ d.equidistributionError * N := by
      simp only [P, h.kept_sign ψ hψ, star_one, one_mul, c, ExcessAverageData.coefficient]
      split_ifs with ht
      · simp only [S, ht, N, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul,
          Complex.ofReal_natCast, sub_self, norm_zero]
        exact mul_nonneg h.equidistribution_nonneg (Nat.cast_nonneg _)
      · exact h.equidistribution ψ hψ (not_forall.mp ht)
    have hdiff : ‖(c : ℂ) * G ψ x - P ψ * G ψ x‖ ≤
        d.equidistributionError * N * ‖G ψ x‖ := by
      rw [← sub_mul, norm_mul, norm_sub_rev (c : ℂ) (P ψ)]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    have hre := (Complex.re_le_norm _).trans hdiff
    simp only [Complex.sub_re, Complex.re_ofReal_mul] at hre
    change N * (d.coefficient ψ * (G ψ x).re - d.equidistributionError * ‖G ψ x‖) ≤
      (P ψ * G ψ x).re
    dsimp only [c] at hre
    nlinarith only [hre]
  have hrest (ψ : ExcessCharacter H) : -N * ‖G ψ x‖ ≤ R ψ := by
    have hS : ‖S ψ‖ ≤ N := by
      calc
        _ ≤ ∑ t ∈ d.tops, ‖ψ (0, 0, t)‖ := norm_sum_le _ _
        _ = N := by simp [N, ψ.norm_apply, nsmul_eq_mul]
    have hP : ‖P ψ‖ ≤ N := by
      simpa only [P, norm_mul, Complex.star_def, Complex.norm_conj, ψ.norm_apply, one_mul] using hS
    have hnorm : ‖-(P ψ * G ψ x)‖ ≤ N * ‖G ψ x‖ := by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    have hre := (Complex.re_le_norm _).trans hnorm
    rw [Complex.neg_re] at hre
    change -(R ψ) ≤ _ at hre
    linarith only [hre]
  have hsplit := Finset.sum_sdiff h.kept_subset (f := R)
  have hloKept : N * (∑ ψ ∈ d.kept, d.coefficient ψ * (G ψ x).re) -
      N * d.equidistributionError * (∑ ψ ∈ d.kept, ‖G ψ x‖) ≤ ∑ ψ ∈ d.kept, R ψ := by
    calc
      _ = ∑ ψ ∈ d.kept, N * (d.coefficient ψ * (G ψ x).re -
          d.equidistributionError * ‖G ψ x‖) := by
        simp only [Finset.mul_sum, mul_sub, mul_assoc, Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum hkept
  have hloRest := Finset.sum_le_sum (s := d.survivors \ d.kept) fun ψ _ => hrest ψ
  rw [← Finset.mul_sum] at hloRest
  rw [hfixed, ← hsplit]
  unfold ExcessAverageData.mainValue ExcessAverageData.auxiliaryValue
  change N * (_ - _ - _) ≤ _
  nlinarith only [hloKept, hloRest]

/-- The common argument contributes the local-variation allowance per survivor and top. -/
private theorem mainValue_le_variableTopSum
    {H : Type*} [AddCommGroup H] [Fintype H]
    {d : ExcessAverageData H} {G : ExcessCharacter H → ℝ → ℂ} {x : ℝ}
    (h : ExcessAverageHypotheses d G x) :
    (d.tops.card : ℝ) * (d.mainValue G x - d.correction G x - d.auxiliaryValue G x) ≤
      ∑ t ∈ d.tops, ∑ ψ ∈ d.survivors, (thickPhase ψ t * G ψ (d.topWeight t / d.b)).re := by
  have hpair (t : H) (ht : t ∈ d.tops) (ψ : ExcessCharacter H) (hψ : ψ ∈ d.survivors) :
      (thickPhase ψ t * G ψ x).re - d.localVariation ≤
        (thickPhase ψ t * G ψ (d.topWeight t / d.b)).re := by
    have hnorm : ‖thickPhase ψ t * G ψ x - thickPhase ψ t * G ψ (d.topWeight t / d.b)‖ ≤
        d.localVariation := by
      rw [← mul_sub, norm_mul, norm_thickPhase, one_mul, norm_sub_rev (G ψ x)]
      exact h.local_bound ψ hψ _ (h.topWeight_close t ht)
    have hre := (Complex.re_le_norm _).trans hnorm
    rw [Complex.sub_re] at hre
    linarith
  have hlocal : (∑ t ∈ d.tops, ∑ ψ ∈ d.survivors,
        ((thickPhase ψ t * G ψ x).re - d.localVariation)) ≤ _ :=
    Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun ψ hψ => hpair t ht ψ hψ
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hlocal
  have hfixed := mainValue_le_fixedTopSum h
  unfold ExcessAverageData.correction
  nlinarith only [hfixed, hlocal]

/-- Inequality (4.5) before normalizing by the size factor. -/
theorem finiteExcess_averaging {H : Type*} [AddCommGroup H] [Fintype H]
    {d : ExcessAverageData H} {G : ExcessCharacter H → ℝ → ℂ} {x : ℝ}
    (h : ExcessAverageHypotheses d G x) :
    d.budget.normalization * (d.mainValue G x - d.correction G x - d.auxiliaryValue G x) ≤
      d.averagedExcess G + d.edgeLoss x := by
  classical
  let U := subgroupElements d.subgroup
  let frozen (u : H) := ∑ t ∈ d.tops, ∑ _j : Fin d.steps, (d.frozenThickExcess G u t).re
  have hpoint (u : H) (hu : u ∈ U) : frozen u ≤ d.excessAt G u + d.edgeLoss x := by
    calc
      _ ≤ ∑ t ∈ d.tops, ∑ j : Fin d.steps,
          ((excessSum G (d.topWeight t) t (d.nodeWeight u j)).re + d.edgeLossPerPair x) := by
        refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => ?_
        have herror := (Complex.abs_re_le_norm _).trans
          (norm_excessSum_sub_frozenThickExcess_le h (mem_subgroupElements.mp hu) ht j)
        rw [Complex.sub_re, abs_le] at herror
        linarith only [herror.1]
      _ = _ := by
        simp only [ExcessAverageData.excessAt, ExcessAverageData.edgeLoss,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hupper : (𝔼 u ∈ U, frozen u) ≤ d.averagedExcess G + d.edgeLoss x := by
    calc
      _ ≤ (𝔼 u ∈ U, (d.excessAt G u + d.edgeLoss x)) := Finset.expect_le_expect hpoint
      _ = _ := by
        rw [Finset.expect_add_distrib U (d.excessAt G) (fun _ => d.edgeLoss x),
          Finset.expect_const d.subgroupElements_nonempty]
        rfl
  let topTerm (t : H) := ∑ ψ ∈ d.survivors, (thickPhase ψ t * G ψ (d.topWeight t / d.b)).re
  let scale := (d.steps : ℝ) * thickScale d
  have hmean : (𝔼 u ∈ U, frozen u) = scale * ∑ t ∈ d.tops, topTerm t := by
    dsimp only [U, frozen, scale, topTerm]
    simp_rw [Finset.expect_sum_comm, mean_frozenThickExcess h]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_assoc, ← Finset.mul_sum]
  have hnormal : scale * (d.tops.card : ℝ) = d.budget.normalization := by
    have hcard : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hnode : Fintype.card (ExcessNode H) = 2 * Fintype.card H := by
      simp [ExcessNode, Fintype.card_prod, ZMod.card]
    dsimp only [scale, thickScale, ExcessAverageData.budget, ExcessBudget.normalization,
      ExcessBudget.thickDensity]
    rw [hnode, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hcard]
  have hscale : 0 ≤ scale := by
    dsimp only [scale, thickScale]
    positivity [h.b_pos]
  calc
    _ = scale * ((d.tops.card : ℝ) *
        (d.mainValue G x - d.correction G x - d.auxiliaryValue G x)) := by rw [← mul_assoc, hnormal]
    _ ≤ scale * ∑ t ∈ d.tops, topTerm t :=
      mul_le_mul_of_nonneg_left (mainValue_le_variableTopSum h) hscale
    _ = 𝔼 u ∈ U, frozen u := hmean.symm
    _ ≤ _ := hupper

/-- The accounting inputs projected from a chain record for each translation. -/
def HasPointwiseAccountingBound {H : Type*} [AddCommGroup H] [Fintype H]
    (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ) (bound : ℝ) : Prop :=
  ∃ (prime : PrimeExcessData H) (v g : ℝ), PrimeExcessHypotheses prime ∧
    G = prime.smoothed ∧ 0 < v ∧ ∀ u ∈ d.subgroup,
    ∃ (U : Type) (a : AccountingData U) (e : AccountingErrors),
      AccountingHypotheses a e ∧
      a.topMass = d.accountingTopMass ∧
      a.baseTerm = d.accountingBaseTerm v (prime.logDerivativeAtOne prime.quadratic).re ∧
      a.nodeLogSum = d.accountingNodeLogSum u v ∧
      a.localLog = (d.steps : ℝ) * g ∧
      a.primeSum = d.primeSumOf prime u ∧
      e.total a.topMass ≤ bound

theorem HasPointwiseAccountingBound.averagedExcess_le {H : Type*} [AddCommGroup H] [Fintype H]
    {d : ExcessAverageData H} {G : ExcessCharacter H → ℝ → ℂ} {bound : ℝ}
    (h : HasPointwiseAccountingBound d G bound)
    (htop : ∀ t ∈ d.tops, 0 < d.topWeight t)
    (hnode : ∀ u ∈ d.subgroup, ∀ j ρ, 0 < d.nodeWeight u j ρ) :
    d.averagedExcess G ≤ bound := by
  obtain ⟨prime, v, _, hprime, hG, hv, hp⟩ := h
  let ell := (prime.logDerivativeAtOne prime.quadratic).re
  apply d.averagedExcess_le_of_pointwise G
  intro u hu
  obtain ⟨_, a, _, haccounting, hmass, hbase, hlog, _, hidentity, herror⟩ := hp u hu
  have hmain : a.mainTerm = d.primeMainTerm u ell := by
    unfold AccountingData.mainTerm
    rw [hmass, hbase, hlog]
    exact d.accounting_mainTerm_eq_primeMainTerm u hv ell (hnode u hu)
  have hexcess : a.primeSum = a.mainTerm + d.excessAt G u := by
    rw [hidentity, hmain, hG]
    exact d.primeSumOf_eq_main_add_excess hprime u htop (hnode u hu)
  exact (accounting_excess_le haccounting hexcess).trans herror

noncomputable def ExcessAverageData.chainInputs {H : Type*} [AddCommGroup H] [Fintype H]
    (d : ExcessAverageData H) (prime : PrimeExcessData H) (u : H)
    (x ε rootDiscriminant localLog : ℝ) : ChainInputs where
  budget := d.budget
  x := x
  ε := ε
  thinScale := d.thinScale
  thinCutoff := d.thinCutoff
  rootDiscriminant := rootDiscriminant
  topMass := d.accountingTopMass
  localLog := localLog
  baseTerm := d.accountingBaseTerm (rootDiscriminant / 2)
    (prime.logDerivativeAtOne prime.quadratic).re
  nodeLogSum := d.accountingNodeLogSum u (rootDiscriminant / 2)
  primeSum := d.primeSumOf prime u

/-- The numerical chain records for all translations, with the same constants. -/
def HasPointwiseChainRecords {H : Type*} [AddCommGroup H] [Fintype H]
    (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ) (x ε C : ℝ) : Prop :=
  ∃ (prime : PrimeExcessData H) (rootDiscriminant g : ℝ) (c : ChainConstants),
    PrimeExcessHypotheses prime ∧ G = prime.smoothed ∧ 0 < rootDiscriminant ∧ c.Valid ∧
    c.errorExponent ≤ C ∧ ∀ u ∈ d.subgroup,
      let p := d.chainInputs prime u x ε rootDiscriminant g
      ∃ (U : Type) (r : ChainRecord U p.budget.steps),
        ChainConditions p c r ∧ ChainErrorSizes p c r.indices.card

theorem HasPointwiseChainRecords.to_accounting {H : Type*} [AddCommGroup H] [Fintype H]
    {d : ExcessAverageData H} {G : ExcessCharacter H → ℝ → ℂ} {x ε C : ℝ}
    (h : HasPointwiseChainRecords d G x ε C) :
    HasPointwiseAccountingBound d G (x ^ (C * ε) * d.budget.total x ε) := by
  obtain ⟨prime, rootDiscriminant, g, c, hprime, hG, hroot, hc, hC, hrecord⟩ := h
  refine ⟨prime, rootDiscriminant / 2, g, hprime, hG, by positivity, fun u hu => ?_⟩
  let p := d.chainInputs prime u x ε rootDiscriminant g
  obtain ⟨U, r, hr, hs⟩ := hrecord u hu
  refine ⟨U, r.toAccountingData p, p.errors c r.indices.card,
    hr.to_accounting hc hs, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hx : 1 ≤ p.x := by linarith [hs.base.scale_ge_three]
  have hexp := mul_le_mul_of_nonneg_right hC hs.base.epsilon_pos.le
  exact (chain_errors_total_le hc hs).trans
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx hexp) hs.base.total_nonneg)

/-- The numerical inputs supplied by averaging and the arithmetic theorem at one scale. -/
def HasFiniteExcessWitness (x ε C main auxiliary : ℝ) : Prop :=
  ∃ (H : Type) (group : AddCommGroup H) (finite : Fintype H),
    letI : AddCommGroup H := group
    letI : Fintype H := finite
    ∃ (d : ExcessAverageData H) (G : ExcessCharacter H → ℝ → ℂ),
      ExcessAverageHypotheses d G x ∧ ExcessSizeBounds d.budget x ε ∧
      d.mainValue G x = main ∧ d.auxiliaryValue G x = auxiliary ∧
      HasPointwiseChainRecords d G x ε C ∧
      d.edgeLoss x / d.budget.normalization + d.correction G x ≤
        (3 / 13 : ℝ) * x ^ (1 / 2 + (C + 3) * ε)

theorem HasFiniteExcessWitness.combination_le {x ε C main auxiliary : ℝ}
    (h : HasFiniteExcessWitness x ε C main auxiliary) (hC : 0 ≤ C) :
    main ≤ x ^ (1 / 2 + (C + 3) * ε) + auxiliary := by
  obtain ⟨H, group, finite, d, G, havg, hsize, hmain, haux, herr, hcorrection⟩ := h
  let localGroup : AddCommGroup H := group
  let localFinite : Fintype H := finite
  have hscale := finiteExcess_averaging havg
  rw [hmain, haux, mul_comm] at hscale
  have hnormalized := (le_div_iff₀ hsize.normalization_pos).2 hscale
  rw [add_div] at hnormalized
  exact combination_le_of_normalizedExcess hsize hC hnormalized
    (herr.to_accounting.averagedExcess_le havg.topWeight_pos havg.nodeWeight_pos) hcorrection

end Riemann
