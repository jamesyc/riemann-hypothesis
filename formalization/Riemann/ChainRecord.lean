module

public import Riemann.Accounting
public import Riemann.ExcessBudget
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Utilities
open scoped BigOperators

namespace Riemann

structure ChainConstants where
  scaleConstant : ℝ
  heightExponent : ℝ
  degreeExponent : ℝ
  lossExponent : ℝ

structure ChainConstants.Valid (c : ChainConstants) : Prop where
  scale_ge_one : 1 ≤ c.scaleConstant
  height_nonneg : 0 ≤ c.heightExponent
  degree_nonneg : 0 ≤ c.degreeExponent
  loss_nonneg : 0 ≤ c.lossExponent

noncomputable def ChainConstants.baseErrorExponent (c : ChainConstants) : ℝ :=
  max 2 (max c.degreeExponent (c.lossExponent + 1))

noncomputable def ChainConstants.errorExponent (c : ChainConstants) : ℝ :=
  c.baseErrorExponent + 1

/-- The common numerical inputs of Definition 18.9 for one translation. -/
structure ChainInputs where
  budget : ExcessBudget
  x : ℝ
  ε : ℝ
  thinScale : ℝ
  thinCutoff : ℝ
  rootDiscriminant : ℝ
  topMass : ℝ
  localLog : ℝ
  baseTerm : ℝ
  nodeLogSum : ℝ
  primeSum : ℝ

noncomputable def ChainInputs.logSize (p : ChainInputs) : ℝ :=
  Real.log (p.budget.a * p.rootDiscriminant)

noncomputable def ChainInputs.scaledCutoff (p : ChainInputs) : ℝ :=
  p.x * p.budget.ambientCount * p.thinCutoff

noncomputable def ChainInputs.scalePower (p : ChainInputs) : ℝ := p.x ^ p.ε

/-- The rank, slope, height and local-error projections of the lattice data. -/
structure ChainRecord (U : Type*) (steps : ℕ) where
  indices : Finset U
  nonempty : indices.Nonempty
  rank : U → ℕ
  auxiliaryPrime : U → ℕ
  inputSlope : U → ℝ
  inputMaxSlope : U → ℝ
  referenceSlope : U → ℝ
  referenceMaxSlope : U → ℝ
  height : U → ℝ
  targetSlope : ℝ
  targetMinSlope : ℝ
  primalMaxSlope : ℝ
  localError : U → Fin steps → ℝ
  commonLoss : ℝ
  gain : ℝ
  indexLoss : ℝ
  δ : ℝ
  η : ℝ
  frameError : ℝ

namespace ChainRecord

variable {U : Type*} {steps : ℕ}

noncomputable def logPrime (r : ChainRecord U steps) (u : U) : ℝ :=
  Real.log (r.auxiliaryPrime u)

noncomputable def finiteLoss (r : ChainRecord U steps) (u : U) : ℝ :=
  ∑ j : Fin steps, r.localError u j

noncomputable def meanSlope (r : ChainRecord U steps) : ℝ :=
  r.indices.centerMass (fun u => (r.rank u : ℝ)) (fun u => r.inputSlope u - r.height u)

noncomputable def spread (r : ChainRecord U steps) : ℝ :=
  r.indices.sup' r.nonempty (fun u => r.inputMaxSlope u - r.height u) - r.meanSlope

noncomputable def pointLoss (r : ChainRecord U steps) (p : ChainInputs)
    (c : ChainConstants) (u : U) : ℝ :=
  c.scaleConstant * r.indexLoss +
    c.scaleConstant * p.budget.topCount * p.budget.steps *
      (p.budget.a / p.budget.k + p.thinScale) * r.logPrime u +
    c.scaleConstant * p.scaledCutoff + 1

noncomputable def toAccountingData (p : ChainInputs) (r : ChainRecord U p.budget.steps) :
    AccountingData U where
  indices := r.indices
  rankWeight u := r.rank u
  inputSlope := r.inputSlope
  referenceSlope := r.referenceSlope
  height := r.height
  finiteLoss := r.finiteLoss
  logPrime := r.logPrime
  primeSum := p.primeSum
  gain := r.gain
  commonLoss := r.commonLoss
  targetSlope := r.targetSlope
  baseTerm := p.baseTerm
  topMass := p.topMass
  nodeLogSum := p.nodeLogSum
  localLog := (p.budget.steps : ℝ) * p.localLog

end ChainRecord

noncomputable def ChainInputs.lossError (p : ChainInputs) (c : ChainConstants) : ℝ :=
  c.scaleConstant ^ 2 * p.budget.topCount * p.budget.steps * p.budget.b *
      p.x ^ (c.lossExponent * p.ε) +
    c.scaleConstant ^ 2 * p.budget.topCount * (p.budget.steps : ℝ) ^ 2 *
      (p.budget.a / p.budget.k + p.thinScale) * p.scalePower +
    c.scaleConstant * p.scaledCutoff + 1

noncomputable def ChainInputs.spreadBound (p : ChainInputs) (c : ChainConstants) : ℝ :=
  c.scaleConstant * p.budget.topCount * p.budget.a * p.logSize *
      (3 + (p.budget.steps : ℝ) / p.budget.k) +
    4 * c.scaleConstant * p.budget.steps * p.budget.liftCost p.x p.ε +
    c.scaleConstant * p.topMass * Real.log p.budget.k + p.lossError c

noncomputable def ChainInputs.errors (p : ChainInputs) (c : ChainConstants)
    (indexCount : ℕ) : AccountingErrors where
  e1 := c.scaleConstant * p.budget.topCount * p.budget.steps * p.budget.b *
    p.x ^ (c.lossExponent * p.ε)
  e2 := p.lossError c
  e3 := Real.log (indexCount : ℝ) + 8 * Real.log (1 + p.x ^ c.heightExponent) *
    (p.spreadBound c + p.budget.b) + 12 * p.budget.b
  e4 := c.scaleConstant * p.budget.topCount * p.budget.a * p.logSize +
    c.scaleConstant * p.budget.steps * (p.budget.liftCost p.x p.ε + p.budget.congruenceCost p.x p.ε) *
      p.x ^ (c.degreeExponent * p.ε)
  e5 := c.scaleConstant * p.budget.steps * p.budget.liftCost p.x p.ε
  e6 := c.scaleConstant * p.logSize * (1 + (p.budget.steps : ℝ) ^ 2 / p.budget.k)
  e7 := c.scaleConstant * p.budget.topCount * p.budget.a * p.logSize *
    (1 + (p.budget.steps : ℝ) / p.budget.k)

/-- Conditions (K1)–(K8) on the numerical projection of a chain record. -/
structure ChainConditions {U : Type*} (p : ChainInputs) (c : ChainConstants)
    (r : ChainRecord U p.budget.steps) : Prop where
  rank_pos : ∀ u ∈ r.indices, 0 < r.rank u
  primalPrime : ∀ u ∈ r.indices, (r.auxiliaryPrime u).Prime
  index_count : (r.indices.card : ℝ) ≤ 2 ^ (p.budget.k - 3)
  k1 : p.primeSum - r.gain ≤ (p.errors c r.indices.card).e1 ∧
    0 ≤ r.indexLoss ∧ r.indexLoss ≤ (p.errors c r.indices.card).e1
  k2 : ∀ u ∈ r.indices,
    r.inputMaxSlope u ≤ r.referenceMaxSlope u + r.gain + r.commonLoss - r.finiteLoss u +
      (p.errors c r.indices.card).e5 ∧
    r.referenceSlope u + r.gain + r.commonLoss - r.finiteLoss u - r.pointLoss p c u ≤
      r.inputSlope u
  k3_delta : 0 ≤ r.δ ∧ r.δ ≤ 1 / 2
  k3_eta : 0 ≤ r.η
  k3_frame : 0 ≤ r.frameError ∧ r.frameError ≤ 1 / 4
  k3_small : (r.η + 4 * Real.sqrt r.frameError) * p.x ^ c.heightExponent ≤ 6
  k3 : ∀ H : ℝ, 0 < H → r.meanSlope - r.targetMinSlope ≤ H →
    r.meanSlope - Real.log (r.indices.card : ℝ) -
      (1 - r.δ)⁻¹ * (4 * r.spread * Real.log (1 + H / r.spread) +
        (r.η + 4 * Real.sqrt r.frameError) * H) ≤ r.targetSlope
  k4_dual : r.targetMinSlope = -r.primalMaxSlope
  k4_ceiling : r.meanSlope + r.primalMaxSlope ≤ p.x ^ c.heightExponent * p.budget.b
  k4 : ∀ u ∈ r.indices, r.targetSlope + r.height u - r.commonLoss ≤
    p.baseTerm - p.topMass * r.logPrime u + (p.errors c r.indices.card).e4
  k5 : ∀ u ∈ r.indices, ∀ j : Fin p.budget.steps,
    |r.localError u j - p.topMass * p.localLog| ≤ c.scaleConstant * p.budget.liftCost p.x p.ε
  k6 : ∀ u ∈ r.indices, ∀ q ∈ r.indices,
    |(r.height u + p.topMass * r.logPrime u) - (r.height q + p.topMass * r.logPrime q)| ≤
      c.scaleConstant * (p.budget.topCount * p.budget.a * p.logSize +
        p.budget.steps * p.budget.liftCost p.x p.ε)
  k7 : ∀ u ∈ r.indices,
    p.nodeLogSum + (p.budget.steps : ℝ) * p.localLog - (p.errors c r.indices.card).e6 ≤
      r.logPrime u ∧ r.logPrime u ≤ c.scaleConstant * p.budget.steps * p.scalePower
  k7_variation : ∀ u ∈ r.indices, ∀ q ∈ r.indices,
    |r.logPrime u - r.logPrime q| ≤ c.scaleConstant * Real.log p.budget.k
  k8 : ∀ u ∈ r.indices, -(p.errors c r.indices.card).e7 ≤ r.referenceSlope u ∧
    r.referenceMaxSlope u ≤ c.scaleConstant * p.budget.topCount * p.budget.a * p.logSize ∧
    r.inputSlope u ≤ r.inputMaxSlope u

/-- The size estimates of Lemma 18.15 and the threshold in Proposition 18.16. -/
structure ChainErrorSizes (p : ChainInputs) (c : ChainConstants) (indexCount : ℕ) : Prop where
  base : ExcessSizeBounds p.budget p.x p.ε
  thin_nonneg : 0 ≤ p.thinScale
  cutoff_nonneg : 0 ≤ p.scaledCutoff
  one_le_b : 1 ≤ p.budget.b
  b_le_a : p.budget.b ≤ p.budget.a
  steps_le_x : (p.budget.steps : ℝ) ≤ p.x
  steps_mul_b_le_a : p.budget.steps * p.budget.b ≤ p.budget.a
  k_upper : p.budget.k ≤ p.x ^ (5 : ℕ)
  k_le_a : p.budget.k ≤ p.budget.a
  thin_mul_k_le_a : p.budget.k * p.thinScale ≤ p.budget.a
  cutoff_le_a : p.scaledCutoff ≤ p.budget.a
  logSize_nonneg : 0 ≤ p.logSize
  logSize_upper : p.logSize ≤ 2 * p.scalePower
  log_x_le : Real.log p.x ≤ p.scalePower
  log_k_le : Real.log p.budget.k ≤ 5 * p.scalePower
  log_height_le : Real.log (1 + p.x ^ c.heightExponent) ≤ (1 + c.heightExponent) * p.scalePower
  mass_nonneg : 0 ≤ p.topMass
  mass_upper : p.topMass ≤ 2 * p.budget.topCount * p.budget.a
  log_count_le : Real.log (indexCount : ℝ) ≤ p.budget.k
  power_threshold : 260 * (1 + c.heightExponent) * c.scaleConstant ^ 2 ≤ p.scalePower

/-- The bound for the logarithmic term in the frame inequality, Lemma 18.12. -/
theorem chain_frame_log_le {u U b X H : ℝ} (hu : 0 ≤ u) (huU : u ≤ U) (hb : 0 < b)
    (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X * b) :
    u * Real.log (1 + H / u) ≤ Real.log (1 + X) * (U + b) := by
  have hX₁ : 0 < 1 + X := by linarith
  have hlogX : 0 ≤ Real.log (1 + X) := Real.log_nonneg (by linarith)
  rcases eq_or_lt_of_le hu with hzero | hupos
  · have hUb : 0 ≤ U + b := by linarith
    rw [← hzero, zero_mul]
    exact mul_nonneg hlogX hUb
  · have hinner : 0 < 1 + H / u := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hinner hX₁)
    rw [Real.log_div hinner.ne' hX₁.ne'] at hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog hupos.le
    have hsplit : u * ((1 + H / u) / (1 + X) - 1) =
        H / (1 + X) - u * X / (1 + X) := by
      field_simp
      ring
    rw [hsplit] at hscaled
    have hdiv := div_le_div_of_nonneg_right hHX hX₁.le
    have hrewrite : X * b / (1 + X) = b * (1 - (1 + X)⁻¹) := by
      field_simp
      ring
    rw [hrewrite] at hdiv
    have htail := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hX₁) hb.le
    have hmass := mul_le_mul_of_nonneg_right huU hlogX
    have hterm : 0 ≤ u * X / (1 + X) := by positivity
    linarith

theorem chain_pointLoss_le {U : Type*} {p : ChainInputs} {c : ChainConstants}
    {r : ChainRecord U p.budget.steps} (hc : c.Valid) (hk : ChainConditions p c r)
    (hs : ChainErrorSizes p c r.indices.card) (u : U) (hu : u ∈ r.indices) :
    r.pointLoss p c u ≤ (p.errors c r.indices.card).e2 := by
  have hc₀ : 0 ≤ c.scaleConstant := by linarith [hc.scale_ge_one]
  have ha := hs.base.a_pos
  have hthin := hs.thin_nonneg
  have hpositive := hs.base.k_pos
  have hscale : 0 ≤ c.scaleConstant * p.budget.topCount * p.budget.steps *
      (p.budget.a / p.budget.k + p.thinScale) := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hk.k1.2.2 hc₀
  have h₂ := mul_le_mul_of_nonneg_left (hk.k7 u hu).2 hscale
  simp only [ChainInputs.errors] at h₁
  unfold ChainRecord.pointLoss ChainInputs.errors ChainInputs.lossError
  dsimp only
  ring_nf at h₁ h₂ ⊢
  linarith

/-- The spread of the weighted input slopes, as bounded in Lemma 18.13. -/
theorem chain_spread_bounds {U : Type*} {p : ChainInputs} {c : ChainConstants}
    {r : ChainRecord U p.budget.steps} (hc : c.Valid) (hk : ChainConditions p c r)
    (hs : ChainErrorSizes p c r.indices.card) :
    0 ≤ r.spread ∧ r.spread ≤ p.spreadBound c := by
  let input (u : U) := r.inputSlope u - r.height u
  let inputMax (u : U) := r.inputMaxSlope u - r.height u
  let weight (u : U) : ℝ := r.rank u
  let maxSlope := r.indices.sup' r.nonempty inputMax
  have hwpos (u : U) (hu : u ∈ r.indices) : 0 < weight u := by
    dsimp [weight]
    exact_mod_cast hk.rank_pos u hu
  have hweight : ∀ u ∈ r.indices, 0 ≤ weight u := fun u hu => (hwpos u hu).le
  have hsum : (∑ u ∈ r.indices, weight u) ≠ 0 :=
    (Finset.sum_pos hwpos r.nonempty).ne'
  have hnonneg : r.meanSlope ≤ maxSlope := by
    change r.indices.centerMass weight input ≤ maxSlope
    refine centerMass_le_const_real hweight hsum fun u hu => ?_
    have hl : input u ≤ inputMax u := sub_le_sub_right (hk.k8 u hu).2.2 _
    exact hl.trans (Finset.le_sup' inputMax hu)
  have hpair (u : U) (hu : u ∈ r.indices) (q : U) (hq : q ∈ r.indices) :
      inputMax u - p.spreadBound c ≤ input q := by
    have hfinite : r.finiteLoss q - r.finiteLoss u ≤
        2 * c.scaleConstant * p.budget.steps * p.budget.liftCost p.x p.ε := by
      calc
        _ = ∑ j : Fin p.budget.steps, (r.localError q j - r.localError u j) := by
          simp only [ChainRecord.finiteLoss, Finset.sum_sub_distrib]
        _ ≤ ∑ _ : Fin p.budget.steps, 2 * c.scaleConstant * p.budget.liftCost p.x p.ε :=
          Finset.sum_le_sum fun j _ => by
            have hlu := (abs_le.mp (hk.k5 u hu j)).1
            have hlq := (abs_le.mp (hk.k5 q hq j)).2
            linarith
        _ = _ := by
          simp [nsmul_eq_mul]
          ring
    have hheight : r.height q - r.height u ≤
        c.scaleConstant * (p.budget.topCount * p.budget.a * p.logSize +
          p.budget.steps * p.budget.liftCost p.x p.ε) +
        c.scaleConstant * p.topMass * Real.log p.budget.k := by
      have hv := (abs_le.mp (hk.k6 q hq u hu)).2
      have hl := mul_le_mul_of_nonneg_left (abs_le.mp (hk.k7_variation u hu q hq)).2
        hs.mass_nonneg
      linarith
    have hmax := (hk.k2 u hu).1
    have hin := (hk.k2 q hq).2
    have hrefmax := (hk.k8 u hu).2.1
    have href := (hk.k8 q hq).1
    have hloss := chain_pointLoss_le hc hk hs q hq
    simp only [ChainInputs.errors] at hmax href hloss
    dsimp [inputMax, input, ChainInputs.spreadBound]
    linarith
  have hmax : maxSlope ≤ r.meanSlope + p.spreadBound c := by
    change r.indices.sup' r.nonempty inputMax ≤ _
    apply (Finset.sup'_le_iff r.nonempty inputMax).mpr
    intro u hu
    have hmean : inputMax u - p.spreadBound c ≤ r.meanSlope := by
      change inputMax u - p.spreadBound c ≤ r.indices.centerMass weight input
      exact const_le_centerMass_real hweight hsum (hpair u hu)
    linarith
  change 0 ≤ maxSlope - r.meanSlope ∧ maxSlope - r.meanSlope ≤ p.spreadBound c
  exact ⟨sub_nonneg.mpr hnonneg, by linarith⟩

theorem chain_frame_bound {U : Type*} {p : ChainInputs} {c : ChainConstants}
    {r : ChainRecord U p.budget.steps} (hc : c.Valid) (hk : ChainConditions p c r)
    (hs : ChainErrorSizes p c r.indices.card) :
    r.meanSlope - (p.errors c r.indices.card).e3 ≤ r.targetSlope := by
  let X := p.x ^ c.heightExponent
  let H := X * p.budget.b
  have hx : 0 < p.x := by linarith [hs.base.scale_ge_three]
  have hX : 0 < X := Real.rpow_pos_of_pos hx _
  have hb := hs.base.b_pos
  have hH : 0 < H := mul_pos hX hb
  have hHbound : r.meanSlope - r.targetMinSlope ≤ H := by
    rw [hk.k4_dual, sub_neg_eq_add]
    exact hk.k4_ceiling
  obtain ⟨hspread, hbound⟩ := chain_spread_bounds hc hk hs
  have hlog := chain_frame_log_le hspread hbound hb hX hH (le_rfl : H ≤ X * p.budget.b)
  let slopeLog := r.spread * Real.log (1 + H / r.spread)
  let coefficient := r.η + 4 * Real.sqrt r.frameError
  have hlog₀ : 0 ≤ slopeLog := by
    have hf : 0 ≤ H / r.spread := div_nonneg hH.le hspread
    exact mul_nonneg hspread (Real.log_nonneg (by linarith))
  have hcoeff₀ : 0 ≤ coefficient := by
    dsimp [coefficient]
    have hη := hk.k3_eta
    positivity
  have hcoeff : coefficient * H ≤ 6 * p.budget.b := by
    change coefficient * (X * p.budget.b) ≤ 6 * p.budget.b
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hk.k3_small hb.le
  let frameLoss := 4 * slopeLog + coefficient * H
  have hframe₀ : 0 ≤ frameLoss := by
    dsimp [frameLoss]
    positivity
  have hframe : frameLoss ≤
      4 * Real.log (1 + X) * (p.spreadBound c + p.budget.b) + 6 * p.budget.b := by
    change slopeLog ≤ Real.log (1 + X) * (p.spreadBound c + p.budget.b) at hlog
    dsimp [frameLoss]
    linarith
  have hδ := hk.k3_delta.2
  have hden : 0 < 1 - r.δ := by linarith
  have hinv : (1 - r.δ)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hbounded := mul_le_mul_of_nonneg_right hinv hframe₀
  have htarget := hk.k3 H hH hHbound
  have hactual : 4 * r.spread * Real.log (1 + H / r.spread) + coefficient * H = frameLoss := by
    dsimp [frameLoss, slopeLog]
    ring
  change r.meanSlope - Real.log (r.indices.card : ℝ) -
    (1 - r.δ)⁻¹ * (4 * r.spread * Real.log (1 + H / r.spread) + coefficient * H) ≤
    r.targetSlope at htarget
  rw [hactual] at htarget
  change r.meanSlope - (Real.log (r.indices.card : ℝ) +
    8 * Real.log (1 + X) * (p.spreadBound c + p.budget.b) + 12 * p.budget.b) ≤ r.targetSlope
  linarith

/-- Proposition 18.14, from the numerical chain record to the seven accounting hypotheses. -/
theorem ChainConditions.to_accounting {U : Type*} {p : ChainInputs} {c : ChainConstants}
    {r : ChainRecord U p.budget.steps} (hk : ChainConditions p c r) (hc : c.Valid)
    (hs : ChainErrorSizes p c r.indices.card) :
    AccountingHypotheses (r.toAccountingData p) (p.errors c r.indices.card) := by
  have hloss := chain_pointLoss_le hc hk hs
  have hframe := chain_frame_bound hc hk hs
  refine ⟨r.nonempty, ?_, hs.mass_nonneg, ?_, ?_, hframe, hk.k4, ?_, ?_, ?_⟩
  · intro u hu
    change 0 < (r.rank u : ℝ)
    exact_mod_cast hk.rank_pos u hu
  · have hgain := hk.k1.1
    change p.primeSum ≤ r.gain + (p.errors c r.indices.card).e1
    linarith
  · intro u hu
    have hb := (hk.k2 u hu).2
    have hl := hloss u hu
    change r.referenceSlope u + r.gain + r.commonLoss - r.finiteLoss u -
      (p.errors c r.indices.card).e2 ≤ r.inputSlope u
    linarith
  · intro u hu
    change r.finiteLoss u ≤ p.topMass * ((p.budget.steps : ℝ) * p.localLog) +
      c.scaleConstant * p.budget.steps * p.budget.liftCost p.x p.ε
    unfold ChainRecord.finiteLoss
    calc
      _ ≤ ∑ _ : Fin p.budget.steps, (p.topMass * p.localLog +
          c.scaleConstant * p.budget.liftCost p.x p.ε) := Finset.sum_le_sum fun j _ => by
        have hj := (abs_le.mp (hk.k5 u hu j)).2
        linarith
      _ = _ := by
        simp [nsmul_eq_mul]
        ring
  · exact fun u hu => (hk.k7 u hu).1
  · exact fun u hu => (hk.k8 u hu).1

private theorem chain_one_le_scalePower {p : ChainInputs}
    (h : ExcessSizeBounds p.budget p.x p.ε) : 1 ≤ p.scalePower :=
  Real.one_le_rpow (by linarith [h.scale_ge_three]) h.epsilon_pos.le

private theorem chain_scalePower_rpow {p : ChainInputs}
    (h : ExcessSizeBounds p.budget p.x p.ε) (s : ℝ) :
    p.x ^ (s * p.ε) = p.scalePower ^ s := by
  unfold ChainInputs.scalePower
  rw [← Real.rpow_mul (by linarith [h.scale_ge_three] : 0 ≤ p.x), mul_comm s p.ε]

private theorem chain_budget_parts {d : ExcessBudget} {x ε : ℝ}
    (h : ExcessSizeBounds d x ε) :
    (d.topCount : ℝ) * d.a * (1 + (d.steps : ℝ) ^ 2 / d.k) ≤ d.total x ε ∧
      (d.steps : ℝ) * d.liftCost x ε ≤ d.total x ε ∧
      (d.steps : ℝ) * (d.liftCost x ε + d.congruenceCost x ε) ≤ d.total x ε := by
  have hx : 0 < x := by linarith [h.scale_ge_three]
  have ha := h.a_pos
  have hb := h.b_pos
  have hk := h.k_pos
  have hleft : 0 ≤ (d.topCount : ℝ) * d.a * (1 + (d.steps : ℝ) ^ 2 / d.k) := by positivity
  have hlift : 0 ≤ d.liftCost x ε := by unfold ExcessBudget.liftCost; positivity
  have hcong : 0 ≤ d.congruenceCost x ε := by unfold ExcessBudget.congruenceCost; positivity
  unfold ExcessBudget.total
  have hright : 0 ≤ (d.steps : ℝ) * (d.liftCost x ε + d.congruenceCost x ε) := by positivity
  have hstep : (d.steps : ℝ) * (d.liftCost x ε + d.congruenceCost x ε) ≤
      (d.topCount : ℝ) * d.a * (1 + (d.steps : ℝ) ^ 2 / d.k) +
        (d.steps : ℝ) * (d.liftCost x ε + d.congruenceCost x ε) := le_add_of_nonneg_left hleft
  exact ⟨le_add_of_nonneg_right hright,
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hcong) (Nat.cast_nonneg _)).trans hstep,
    hstep⟩

private theorem chain_topWeight_le_budget {d : ExcessBudget} {x ε : ℝ}
    (h : ExcessSizeBounds d x ε) : (d.topCount : ℝ) * d.a ≤ d.total x ε := by
  have hratio : 1 ≤ 1 + (d.steps : ℝ) ^ 2 / d.k := by
    linarith [div_nonneg (sq_nonneg (d.steps : ℝ)) h.k_pos.le]
  exact (le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) h.a_pos.le) hratio).trans
    (chain_budget_parts h).1

private theorem chain_a_le_budget {p : ChainInputs} {c : ChainConstants} {indexCount : ℕ}
    (hs : ChainErrorSizes p c indexCount) : p.budget.a ≤ p.budget.total p.x p.ε := by
  have ht : 1 ≤ (p.budget.topCount : ℝ) := by exact_mod_cast hs.base.top_pos
  exact (le_mul_of_one_le_left hs.base.a_pos.le ht).trans (chain_topWeight_le_budget hs.base)

private theorem chain_steps_div_k_le_one {p : ChainInputs}
    (h : ExcessSizeBounds p.budget p.x p.ε) : (p.budget.steps : ℝ) / p.budget.k ≤ 1 := by
  have hx : 1 ≤ p.x := by linarith [h.scale_ge_three]
  exact (div_le_one h.k_pos).mpr
    ((le_mul_of_one_le_left (Nat.cast_nonneg _) hx).trans h.k_lower)

private theorem ChainConstants.Valid.scale_le_sq {c : ChainConstants} (hc : c.Valid) :
    c.scaleConstant ≤ c.scaleConstant ^ 2 := by
  rw [pow_two]
  exact le_mul_of_one_le_right (zero_le_one.trans hc.scale_ge_one) hc.scale_ge_one

/-- The point loss is bounded at exponent `max 1 eL`, before the height
logarithm introduces the extra power in the frame error. -/
private theorem chain_lossError_le {p : ChainInputs} {c : ChainConstants} {indexCount : ℕ}
    (hc : c.Valid) (hs : ChainErrorSizes p c indexCount) :
    p.lossError c ≤ 5 * c.scaleConstant ^ 2 *
      (p.scalePower ^ max 1 c.lossExponent * p.budget.total p.x p.ε) := by
  let d := p.budget
  let y := p.scalePower
  let z := y ^ max 1 c.lossExponent
  let B := d.total p.x p.ε
  let C := c.scaleConstant
  have hC₀ : 0 ≤ C := zero_le_one.trans hc.scale_ge_one
  have hC : C ≤ C ^ 2 := hc.scale_le_sq
  have hy : 1 ≤ y := chain_one_le_scalePower hs.base
  have hyz : y ≤ z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy (le_max_left 1 c.lossExponent)
  have hz : 1 ≤ z := hy.trans hyz
  have hp : p.x ^ (c.lossExponent * p.ε) ≤ z := by
    rw [chain_scalePower_rpow hs.base]
    exact Real.rpow_le_rpow_of_exponent_le hy (le_max_right 1 c.lossExponent)
  have hB : 0 ≤ B := hs.base.total_nonneg
  have hBW : B ≤ z * B := le_mul_of_one_le_left hB hz
  have h₁B : (d.topCount : ℝ) * d.steps * d.b ≤ B := by
    calc
      _ = (d.topCount : ℝ) * (d.steps * d.b) := mul_assoc _ _ _
      _ ≤ (d.topCount : ℝ) * d.a := mul_le_mul_of_nonneg_left hs.steps_mul_b_le_a (Nat.cast_nonneg _)
      _ ≤ B := chain_topWeight_le_budget hs.base
  have h₂B : (d.topCount : ℝ) * (d.steps : ℝ) ^ 2 * (d.a / d.k + p.thinScale) ≤ 2 * B := by
    have hthin : p.thinScale ≤ d.a / d.k :=
      (le_div_iff₀ hs.base.k_pos).mpr (by simpa only [mul_comm] using hs.thin_mul_k_le_a)
    have htop : 0 ≤ (d.topCount : ℝ) * d.a := mul_nonneg (Nat.cast_nonneg _) hs.base.a_pos.le
    have hleft := (chain_budget_parts hs.base).1
    change (d.topCount : ℝ) * d.a * (1 + (d.steps : ℝ) ^ 2 / d.k) ≤ B at hleft
    have hterm : (d.topCount : ℝ) * d.a * ((d.steps : ℝ) ^ 2 / d.k) ≤ B :=
      (mul_le_mul_of_nonneg_left (by linarith : (d.steps : ℝ) ^ 2 / d.k ≤
        1 + (d.steps : ℝ) ^ 2 / d.k) htop).trans hleft
    calc
      _ ≤ (d.topCount : ℝ) * (d.steps : ℝ) ^ 2 * (2 * (d.a / d.k)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      _ = 2 * ((d.topCount : ℝ) * d.a * ((d.steps : ℝ) ^ 2 / d.k)) := by ring
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left hterm (by norm_num)
  have h₁ : C ^ 2 * (d.topCount : ℝ) * d.steps * d.b * p.x ^ (c.lossExponent * p.ε) ≤
      C ^ 2 * (z * B) := by
    have hb := hs.base.b_pos
    calc
      _ = C ^ 2 * (p.x ^ (c.lossExponent * p.ε) * ((d.topCount : ℝ) * d.steps * d.b)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hp h₁B
        (by positivity) (zero_le_one.trans hz)) (sq_nonneg C)
  have h₂ : C ^ 2 * (d.topCount : ℝ) * (d.steps : ℝ) ^ 2 *
      (d.a / d.k + p.thinScale) * y ≤ 2 * (C ^ 2 * (z * B)) := by
    have ha := hs.base.a_pos
    have hk := hs.base.k_pos
    have hthin := hs.thin_nonneg
    calc
      _ = C ^ 2 * (y * ((d.topCount : ℝ) * (d.steps : ℝ) ^ 2 * (d.a / d.k + p.thinScale))) := by ring
      _ ≤ C ^ 2 * (z * (2 * B)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hyz h₂B (by positivity) (zero_le_one.trans hz)) (sq_nonneg C)
      _ = _ := by ring
  have h₃ : C * p.scaledCutoff ≤ C ^ 2 * (z * B) :=
    mul_le_mul hC (hs.cutoff_le_a.trans ((chain_a_le_budget hs).trans hBW)) hs.cutoff_nonneg (sq_nonneg C)
  have hB₁ : 1 ≤ B := hs.one_le_b.trans (hs.b_le_a.trans (chain_a_le_budget hs))
  have h₄ : 1 ≤ C ^ 2 * (z * B) := by
    exact (hB₁.trans hBW).trans (le_mul_of_one_le_left
      (mul_nonneg (zero_le_one.trans hz) hB) (hc.scale_ge_one.trans hC))
  change C ^ 2 * (d.topCount : ℝ) * d.steps * d.b * p.x ^ (c.lossExponent * p.ε) +
      C ^ 2 * (d.topCount : ℝ) * (d.steps : ℝ) ^ 2 * (d.a / d.k + p.thinScale) * y +
      C * p.scaledCutoff + 1 ≤ 5 * C ^ 2 * (z * B)
  rw [show 5 * C ^ 2 * (z * B) = 5 * (C ^ 2 * (z * B)) by ring]
  linarith

/-- The six non-frame terms in the proof of Proposition 18.16. -/
theorem chain_nonFrameErrors_le {p : ChainInputs} {c : ChainConstants} {indexCount : ℕ}
    (hc : c.Valid) (hs : ChainErrorSizes p c indexCount) :
    let e := p.errors c indexCount
    e.e1 + e.e2 + e.e4 + e.e5 + p.topMass * e.e6 + e.e7 ≤
      18 * c.scaleConstant ^ 2 *
        (p.scalePower ^ c.baseErrorExponent * p.budget.total p.x p.ε) := by
  let d := p.budget
  let C := c.scaleConstant
  let y := p.scalePower
  let Y := y ^ c.baseErrorExponent
  let B := d.total p.x p.ε
  let W := C ^ 2 * (Y * B)
  let e := p.errors c indexCount
  have hC₀ : 0 ≤ C := zero_le_one.trans hc.scale_ge_one
  have hC : C ≤ C ^ 2 := hc.scale_le_sq
  have hy : 1 ≤ y := chain_one_le_scalePower hs.base
  have hdegree : c.degreeExponent ≤ c.baseErrorExponent :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hloss : c.lossExponent + 1 ≤ c.baseErrorExponent :=
    (le_max_right _ _).trans (le_max_right _ _)
  have htwo : 2 ≤ c.baseErrorExponent := le_max_left _ _
  have hmax : max 1 c.lossExponent ≤ c.baseErrorExponent := max_le
    (by linarith) (by linarith)
  have hyY : y ≤ Y := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy
      (show (1 : ℝ) ≤ c.baseErrorExponent by linarith)
  have hY₀ : 0 ≤ Y := zero_le_one.trans (hy.trans hyY)
  have hpow (s : ℝ) (hsκ : s ≤ c.baseErrorExponent) : p.x ^ (s * p.ε) ≤ Y := by
    rw [chain_scalePower_rpow hs.base]
    exact Real.rpow_le_rpow_of_exponent_le hy hsκ
  have ha := hs.base.a_pos
  have hb := hs.base.b_pos
  have hk := hs.base.k_pos
  have hx : 0 < p.x := by linarith [hs.base.scale_ge_three]
  have hB : 0 ≤ B := hs.base.total_nonneg
  have htop : (d.topCount : ℝ) * d.a ≤ B := chain_topWeight_le_budget hs.base
  have htop₀ : 0 ≤ (d.topCount : ℝ) * d.a := by positivity
  obtain ⟨hleft, hlift, hright⟩ := chain_budget_parts hs.base
  have hproduct {v b : ℝ} (hv : v ≤ Y) (hbB : b ≤ B) (hb₀ : 0 ≤ b) : C * (v * b) ≤ W :=
    (mul_le_mul_of_nonneg_left (mul_le_mul hv hbB hb₀ hY₀) hC₀).trans
      (mul_le_mul_of_nonneg_right hC (mul_nonneg hY₀ hB))
  have hyW : C * (y * B) ≤ W := hproduct hyY le_rfl hB
  have h₁ : e.e1 ≤ W := by
    have hmass : (d.topCount : ℝ) * (d.steps * d.b) ≤ B :=
      (mul_le_mul_of_nonneg_left hs.steps_mul_b_le_a (Nat.cast_nonneg _)).trans htop
    calc
      _ = C * (p.x ^ (c.lossExponent * p.ε) * ((d.topCount : ℝ) * (d.steps * d.b))) := by
        dsimp [e, ChainInputs.errors, d, C]
        ring
      _ ≤ _ := hproduct (hpow c.lossExponent (by linarith)) hmass (by positivity)
  have h₂ : e.e2 ≤ 5 * W := by
    have hz := Real.rpow_le_rpow_of_exponent_le hy hmax
    have hl := chain_lossError_le hc hs
    exact hl.trans (by
      change 5 * C ^ 2 * (y ^ max 1 c.lossExponent * B) ≤ 5 * W
      rw [show 5 * W = 5 * C ^ 2 * (Y * B) by dsimp [W]; ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hz hB) (by positivity))
  have hlog : C * (d.topCount : ℝ) * d.a * p.logSize ≤ 2 * W := by
    calc
      _ ≤ C * (d.topCount : ℝ) * d.a * (2 * y) :=
        mul_le_mul_of_nonneg_left hs.logSize_upper (by positivity)
      _ = 2 * (C * (y * ((d.topCount : ℝ) * d.a))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hproduct hyY htop htop₀) (by norm_num)
  have h₄ : e.e4 ≤ 3 * W := by
    have hright₀ : 0 ≤ (d.steps : ℝ) * (d.liftCost p.x p.ε + d.congruenceCost p.x p.ε) := by
      unfold ExcessBudget.liftCost ExcessBudget.congruenceCost
      positivity
    have hterm := hproduct (hpow c.degreeExponent hdegree) hright hright₀
    have hscaled : C * d.steps * (d.liftCost p.x p.ε + d.congruenceCost p.x p.ε) *
        p.x ^ (c.degreeExponent * p.ε) ≤ W := by
      calc
        _ = C * (p.x ^ (c.degreeExponent * p.ε) *
            (d.steps * (d.liftCost p.x p.ε + d.congruenceCost p.x p.ε))) := by ring
        _ ≤ W := hterm
    change C * (d.topCount : ℝ) * d.a * p.logSize +
      C * d.steps * (d.liftCost p.x p.ε + d.congruenceCost p.x p.ε) *
        p.x ^ (c.degreeExponent * p.ε) ≤ 3 * W
    linarith
  have h₅ : e.e5 ≤ W := by
    have hlift₀ : 0 ≤ (d.steps : ℝ) * d.liftCost p.x p.ε := by
      unfold ExcessBudget.liftCost
      positivity
    have hterm := hproduct (hy.trans hyY) hlift hlift₀
    change C * (d.steps : ℝ) * d.liftCost p.x p.ε ≤ W
    simpa only [one_mul, mul_assoc] using hterm
  have h₆ : p.topMass * e.e6 ≤ 4 * W := by
    have hfactor : 0 ≤ 1 + (d.steps : ℝ) ^ 2 / d.k := by positivity
    have hmass : p.topMass * (1 + (d.steps : ℝ) ^ 2 / d.k) ≤ 2 * B := by
      calc
        _ ≤ (2 * d.topCount * d.a) * (1 + (d.steps : ℝ) ^ 2 / d.k) :=
          mul_le_mul_of_nonneg_right hs.mass_upper hfactor
        _ = 2 * ((d.topCount : ℝ) * d.a * (1 + (d.steps : ℝ) ^ 2 / d.k)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hleft (by norm_num)
    calc
      _ = C * (p.logSize * (p.topMass * (1 + (d.steps : ℝ) ^ 2 / d.k))) := by
        dsimp [e, ChainInputs.errors, d, C]
        ring
      _ ≤ C * ((2 * y) * (2 * B)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hs.logSize_upper hmass (mul_nonneg hs.mass_nonneg hfactor) (by linarith)) hC₀
      _ = 4 * (C * (y * B)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hyW (by norm_num)
  have h₇ : e.e7 ≤ 4 * W := by
    have hr : 1 + (d.steps : ℝ) / d.k ≤ 2 := by
      have hratio := chain_steps_div_k_le_one hs.base
      change (d.steps : ℝ) / d.k ≤ 1 at hratio
      linarith
    have hlog₀ := hs.logSize_nonneg
    change C * (d.topCount : ℝ) * d.a * p.logSize * (1 + (d.steps : ℝ) / d.k) ≤ 4 * W
    have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ C * (d.topCount : ℝ) * d.a * p.logSize by positivity)
    linarith
  change e.e1 + e.e2 + e.e4 + e.e5 + p.topMass * e.e6 + e.e7 ≤ 18 * C ^ 2 * (Y * B)
  rw [show 18 * C ^ 2 * (Y * B) = 18 * W by dsimp [W]; ring]
  linarith

/-- The contribution of the frame error in the proof of Proposition 18.16. -/
theorem chain_frameError_le {p : ChainInputs} {c : ChainConstants} {indexCount : ℕ}
    (hc : c.Valid) (hs : ChainErrorSizes p c indexCount) :
    (p.errors c indexCount).e3 ≤ 237 * (1 + c.heightExponent) * c.scaleConstant ^ 2 *
      (p.scalePower ^ c.baseErrorExponent * p.budget.total p.x p.ε) := by
  let d := p.budget
  let C := c.scaleConstant
  let y := p.scalePower
  let z := y ^ max 1 c.lossExponent
  let B := d.total p.x p.ε
  let W := C ^ 2 * (z * B)
  let V := (1 + c.heightExponent) * C ^ 2 * (y ^ c.baseErrorExponent * B)
  have ha : 0 < d.a := hs.base.a_pos
  have hk : 0 < d.k := hs.base.k_pos
  have hC₀ : 0 ≤ C := zero_le_one.trans hc.scale_ge_one
  have hC : C ≤ C ^ 2 := hc.scale_le_sq
  have hy : 1 ≤ y := chain_one_le_scalePower hs.base
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hyz : y ≤ z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy (le_max_left 1 c.lossExponent)
  have hB : 0 ≤ B := hs.base.total_nonneg
  have hprod : B ≤ y * B := le_mul_of_one_le_left hB hy
  have hCy : C * (y * B) ≤ W :=
    mul_le_mul hC (mul_le_mul_of_nonneg_right hyz hB) (mul_nonneg hy₀.le hB) (sq_nonneg C)
  have hCB : C * B ≤ W := (mul_le_mul_of_nonneg_left hprod hC₀).trans hCy
  have hBW : B ≤ W := (le_mul_of_one_le_left hB hc.scale_ge_one).trans hCB
  have htop : (d.topCount : ℝ) * d.a ≤ B := chain_topWeight_le_budget hs.base
  have htopCy : C * (y * ((d.topCount : ℝ) * d.a)) ≤ W :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htop hy₀.le) hC₀).trans hCy
  have hratio : 3 + (d.steps : ℝ) / d.k ≤ 4 := by
    have h := chain_steps_div_k_le_one hs.base
    change (d.steps : ℝ) / d.k ≤ 1 at h
    linarith
  have hSize := hs.logSize_nonneg
  have hfirst : C * (d.topCount : ℝ) * d.a * p.logSize * (3 + (d.steps : ℝ) / d.k) ≤ 8 * W := by
    calc
      _ ≤ C * (d.topCount : ℝ) * d.a * (2 * y) * 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs.logSize_upper (by positivity)) hratio
          (by positivity) (by positivity)
      _ = 8 * (C * (y * ((d.topCount : ℝ) * d.a))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htopCy (by norm_num)
  have hlift : (d.steps : ℝ) * d.liftCost p.x p.ε ≤ B := (chain_budget_parts hs.base).2.1
  have hsecond : 4 * C * d.steps * d.liftCost p.x p.ε ≤ 4 * W := by
    calc
      _ = 4 * (C * (d.steps * d.liftCost p.x p.ε)) := by ring
      _ ≤ 4 * (C * B) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlift hC₀) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hCB (by norm_num)
  have hthird : C * p.topMass * Real.log d.k ≤ 10 * W := by
    calc
      _ = C * (Real.log d.k * p.topMass) := by ring
      _ ≤ C * ((5 * y) * (2 * d.topCount * d.a)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hs.log_k_le hs.mass_upper hs.mass_nonneg (by positivity)) hC₀
      _ = 10 * (C * (y * ((d.topCount : ℝ) * d.a))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htopCy (by norm_num)
  have hloss : p.lossError c ≤ 5 * W := by
    convert chain_lossError_le hc hs using 1
    dsimp [W]
    ring
  have hbB : d.b ≤ B := hs.b_le_a.trans (chain_a_le_budget hs)
  have hspread : p.spreadBound c + d.b ≤ 28 * W := by
    have hbW := hbB.trans hBW
    change C * (d.topCount : ℝ) * d.a * p.logSize * (3 + (d.steps : ℝ) / d.k) +
      4 * C * d.steps * d.liftCost p.x p.ε + C * p.topMass * Real.log d.k +
      p.lossError c + d.b ≤ 28 * W
    linarith
  have hκ : 1 + max 1 c.lossExponent ≤ c.baseErrorExponent := by
    rw [add_max]
    apply max_le
    · exact (by norm_num : (1 : ℝ) + 1 ≤ 2).trans (le_max_left _ _)
    · rw [add_comm]
      exact (le_max_right _ _).trans (le_max_right _ _)
  have hyzκ : y * z ≤ y ^ c.baseErrorExponent := by
    calc
      y * z = y ^ (1 + max 1 c.lossExponent) := by dsimp [z]; rw [Real.rpow_add hy₀, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hy hκ
  have hH : 1 ≤ 1 + c.heightExponent := by linarith [hc.height_nonneg]
  have hBV : B ≤ V := by
    have hyz₁ : 1 ≤ y * z := one_le_mul_of_one_le_of_one_le hy (hy.trans hyz)
    have hfactor : 1 ≤ (1 + c.heightExponent) * C ^ 2 :=
      one_le_mul_of_one_le_of_one_le hH (hc.scale_ge_one.trans hC)
    exact (le_mul_of_one_le_left hB (hyz₁.trans hyzκ)).trans
      (le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans (hyz₁.trans hyzκ)) hB) hfactor)
  have hx : 0 < p.x := by linarith [hs.base.scale_ge_three]
  have hlog₀ : 0 ≤ Real.log (1 + p.x ^ c.heightExponent) :=
    Real.log_nonneg (by linarith [Real.rpow_nonneg hx.le c.heightExponent])
  have hframe : Real.log (1 + p.x ^ c.heightExponent) * (p.spreadBound c + d.b) ≤ 28 * V := by
    calc
      _ ≤ Real.log (1 + p.x ^ c.heightExponent) * (28 * W) :=
        mul_le_mul_of_nonneg_left hspread hlog₀
      _ ≤ ((1 + c.heightExponent) * y) * (28 * W) :=
        mul_le_mul_of_nonneg_right hs.log_height_le (by dsimp [W]; positivity)
      _ = 28 * ((1 + c.heightExponent) * C ^ 2 * ((y * z) * B)) := by dsimp [W]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hyzκ hB) (mul_nonneg (zero_le_one.trans hH) (sq_nonneg C)))
        (by norm_num)
  have hcount : Real.log (indexCount : ℝ) ≤ V := hs.log_count_le.trans
    (hs.k_le_a.trans ((chain_a_le_budget hs).trans hBV))
  have hbV : d.b ≤ V := hbB.trans hBV
  change Real.log (indexCount : ℝ) + 8 * Real.log (1 + p.x ^ c.heightExponent) *
    (p.spreadBound c + d.b) + 12 * d.b ≤ 237 * (1 + c.heightExponent) * C ^ 2 *
      (y ^ c.baseErrorExponent * B)
  rw [show 237 * (1 + c.heightExponent) * C ^ 2 * (y ^ c.baseErrorExponent * B) =
    237 * V by dsimp [V]; ring]
  have hframe' := mul_le_mul_of_nonneg_left hframe (show (0 : ℝ) ≤ 8 by norm_num)
  rw [← mul_assoc] at hframe'
  linarith

/-- Proposition 18.16, bounding the combined seven errors by the common budget. -/
theorem chain_errors_total_le {p : ChainInputs} {c : ChainConstants} {indexCount : ℕ}
    (hc : c.Valid) (hs : ChainErrorSizes p c indexCount) :
    (p.errors c indexCount).total p.topMass ≤
      p.x ^ (c.errorExponent * p.ε) * p.budget.total p.x p.ε := by
  let y := p.scalePower
  let κ := c.baseErrorExponent
  let B := p.budget.total p.x p.ε
  let e := p.errors c indexCount
  have hx : 0 < p.x := by linarith [hs.base.scale_ge_three]
  have hy : 0 < y := Real.rpow_pos_of_pos hx _
  have hB : 0 ≤ B := hs.base.total_nonneg
  have hweighted : 0 ≤ y ^ κ * B := mul_nonneg (Real.rpow_nonneg hy.le _) hB
  have hfactor : 0 ≤ (1 + c.heightExponent) * c.scaleConstant ^ 2 := by
    have hh := hc.height_nonneg
    positivity
  have h₁₈ : 18 * c.scaleConstant ^ 2 ≤ 18 * ((1 + c.heightExponent) * c.scaleConstant ^ 2) := by
    have hh : 1 ≤ 1 + c.heightExponent := by linarith [hc.height_nonneg]
    have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg c.scaleConstant)
    linarith
  have hcoefficient : 18 * c.scaleConstant ^ 2 +
      237 * (1 + c.heightExponent) * c.scaleConstant ^ 2 ≤ y := by
    have hthreshold := hs.power_threshold
    change 260 * (1 + c.heightExponent) * c.scaleConstant ^ 2 ≤ y at hthreshold
    linarith
  have hyκ : y * y ^ κ = p.x ^ (c.errorExponent * p.ε) := by
    calc
      y * y ^ κ = y ^ κ * y := mul_comm _ _
      _ = y ^ (κ + 1) := by rw [Real.rpow_add hy, Real.rpow_one]
      _ = _ := by
        dsimp [y, κ, ChainInputs.scalePower, ChainConstants.errorExponent]
        rw [← Real.rpow_mul hx.le]
        congr 1
        ring
  change e.total p.topMass ≤ p.x ^ (c.errorExponent * p.ε) * B
  calc
    e.total p.topMass = (e.e1 + e.e2 + e.e4 + e.e5 + p.topMass * e.e6 + e.e7) + e.e3 := by
      unfold AccountingErrors.total
      ring
    _ ≤ 18 * c.scaleConstant ^ 2 * (y ^ κ * B) +
      (237 * (1 + c.heightExponent) * c.scaleConstant ^ 2) * (y ^ κ * B) :=
        add_le_add (chain_nonFrameErrors_le hc hs) (chain_frameError_le hc hs)
    _ = (18 * c.scaleConstant ^ 2 + 237 * (1 + c.heightExponent) * c.scaleConstant ^ 2) *
        (y ^ κ * B) := by rw [add_mul]
    _ ≤ y * (y ^ κ * B) := mul_le_mul_of_nonneg_right hcoefficient hweighted
    _ = _ := by rw [← mul_assoc, hyκ]

end Riemann
