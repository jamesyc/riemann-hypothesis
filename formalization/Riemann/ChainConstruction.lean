module

public import Riemann.ChainLevelPrimes
import Riemann.ChainFrameSizes

@[expose] public section

open scoped BigOperators

namespace Riemann

/-- Shared dimensions and short intervals for the primes of one chain.
The target dimension and frame normalization are common to every index. -/
structure ChainLevelPlacement {U : Type*} (p : ChainInputs) (c : ChainConstants)
    (r : ChainRecord U p.budget.steps) where
  frameRank : ℝ
  targetDimension : ℝ
  sourceDimension : U → ℝ
  normalization : ℝ
  dimensionError : ℝ
  frameRank_pos : 0 < frameRank
  targetDimension_pos : 0 < targetDimension
  normalization_pos : 0 < normalization
  logNormalization_le : Real.log normalization ≤ frameRank
  dimensionError_nonneg : 0 ≤ dimensionError
  dimensionError_le : dimensionError + 2 ≤ c.scaleConstant
  logSize_ge : p.scalePower ≤ p.logSize
  sourceDimension_pos : ∀ u ∈ r.indices, 0 < sourceDimension u
  dimension_lower : ∀ u ∈ r.indices,
    p.nodeLogSum + (p.budget.steps : ℝ) * p.localLog -
        dimensionError * p.scalePower * (1 + (p.budget.steps : ℝ) ^ 2 / p.budget.k) ≤
      (Real.log targetDimension - Real.log (sourceDimension u)) / frameRank
  interval : ∀ u ∈ r.indices,
    let T := (targetDimension / sourceDimension u) ^ frameRank⁻¹ *
      normalization ^ (-2 / frameRank)
    T ≤ (r.auxiliaryPrime u : ℝ) ∧
      (r.auxiliaryPrime u : ℝ) ≤ (1 + frameRank⁻¹) * T
  center_upper : ∀ u ∈ r.indices,
    (Real.log targetDimension - Real.log (sourceDimension u) - 2 * Real.log normalization) /
        frameRank + frameRank⁻¹ ≤ c.scaleConstant * p.budget.steps * p.scalePower
  dimension_variation : ∀ u ∈ r.indices, ∀ v ∈ r.indices,
    |Real.log (sourceDimension u) - Real.log (sourceDimension v)| / frameRank + frameRank⁻¹ ≤
      c.scaleConstant * Real.log p.budget.k

theorem ChainLevelPlacement.log_bounds {U : Type*} {p : ChainInputs} {c : ChainConstants}
    {r : ChainRecord U p.budget.steps} (h : ChainLevelPlacement p c r)
    (hk : 0 < p.budget.k) (hx : 1 ≤ p.scalePower) (u : U) (hu : u ∈ r.indices) :
    p.nodeLogSum + (p.budget.steps : ℝ) * p.localLog - (p.errors c r.indices.card).e6 ≤
      r.logPrime u ∧ r.logPrime u ≤ c.scaleConstant * p.budget.steps * p.scalePower := by
  obtain ⟨hl, hr⟩ := h.interval u hu
  refine ⟨chainRecord_logPrime_lower_of_dimensionBudget r u h.frameRank_pos
    h.targetDimension_pos (h.sourceDimension_pos u hu) h.normalization_pos h.logNormalization_le
    h.dimensionError_nonneg h.dimensionError_le hk hx h.logSize_ge (h.dimension_lower u hu)
    hl hr, ?_⟩
  have hh := (chainLevel_log_bounds h.frameRank_pos h.targetDimension_pos
    (h.sourceDimension_pos u hu) h.normalization_pos h.logNormalization_le hl hr).2.2
  change Real.log (r.auxiliaryPrime u : ℝ) ≤ _
  linarith [h.center_upper u hu]

theorem ChainLevelPlacement.log_variation {U : Type*} {p : ChainInputs} {c : ChainConstants}
    {r : ChainRecord U p.budget.steps} (h : ChainLevelPlacement p c r)
    (u : U) (hu : u ∈ r.indices) (v : U) (hv : v ∈ r.indices) :
    |r.logPrime u - r.logPrime v| ≤ c.scaleConstant * Real.log p.budget.k := by
  obtain ⟨hul, hur⟩ := h.interval u hu
  obtain ⟨hvl, hvr⟩ := h.interval v hv
  exact (chainLevel_log_variation h.frameRank_pos h.targetDimension_pos
    (h.sourceDimension_pos u hu) (h.sourceDimension_pos v hv)
    h.normalization_pos h.logNormalization_le hul hur hvl hvr).trans
      (h.dimension_variation u hu v hv)

/-- The frame parameters from the Bessel realization at the auxiliary
levels. The constants `C` and `f` are the common multiplicity denominator
and the half-degree from Lemma 13.19. -/
structure ChainFrameProjection {U : Type*} (p : ChainInputs) (c : ChainConstants)
    (r : ChainRecord U p.budget.steps) (C : ℝ) (f : ℕ) where
  dimension : ℝ
  sourceDimension : U → ℝ
  eta₀ : ℝ
  eta₁ : ℝ
  gramError : ℝ
  dimension_pos : 0 < dimension
  sourceDimension_lower : ∀ u ∈ r.indices, dimension / C ≤ sourceDimension u
  level_ge : ∀ u ∈ r.indices, p.budget.b ≤ (r.auxiliaryPrime u : ℝ)
  rank_eq : ∀ u ∈ r.indices,
    (r.rank u : ℝ) = sourceDimension u * (1 - ((r.auxiliaryPrime u : ℝ) - 1)⁻¹) ^ f
  eta₀_bound : eta₀ ≤ Real.exp (-(p.x ^ p.ε / 8))
  eta₁_bound : eta₁ ≤ Real.exp (-(p.x ^ p.ε / 8))
  gramError_nonneg : 0 ≤ gramError
  gramError_bound : Real.sqrt gramError ≤ Real.exp (-(p.x ^ p.ε / 8))
  eta_eq : r.η = 5 * (p.x ^ c.heightExponent)⁻¹ + 3 * Real.sqrt (2 * (f : ℝ) / p.budget.b)
  frameError_eq : r.frameError = 2 * gramError

/-- Lemma 13.19 gives the dimension inequalities and the three scalar
bounds for (K3) on the numerical chain record. -/
theorem ChainFrameProjection.bounds {U : Type*} {p : ChainInputs} {c : ChainConstants}
    {r : ChainRecord U p.budget.steps} {C : ℝ} {f : ℕ}
    (h : ChainFrameProjection p c r C f)
    (hC : 0 < C) (hb : 3 ≤ p.budget.b) (hX : 20 ≤ p.x ^ c.heightExponent)
    (hslack : 11 * Real.exp (-(p.x ^ p.ε / 8)) * p.x ^ c.heightExponent ≤ 1)
    (hf : 4 * (f : ℝ) ≤ p.budget.b * Real.exp (-(p.x ^ p.ε / 8)) ^ (2 : ℕ))
    (hcount : C * p.x ^ c.heightExponent ≤ (r.indices.card : ℝ)) :
    h.dimension ≤ (p.x ^ c.heightExponent)⁻¹ * ∑ u ∈ r.indices, h.sourceDimension u ∧
    (∑ u ∈ r.indices, (h.sourceDimension u - (r.rank u : ℝ))) ≤
      (2 * (f : ℝ) / p.budget.b) * ∑ u ∈ r.indices, h.sourceDimension u ∧
    0 ≤ r.η ∧ (0 ≤ r.frameError ∧ r.frameError ≤ 1 / 4) ∧
    (r.η + 4 * Real.sqrt r.frameError) * p.x ^ c.heightExponent ≤ 6 := by
  obtain ⟨hcover, hloss, hσ, _, _, _, he, _, hsmall⟩ :=
    chainFrame_sizeBounds_of_wordCount r.indices hX hb hC h.dimension_pos h.gramError_nonneg
      h.eta₀_bound h.eta₁_bound h.gramError_bound hslack hf hcount h.sourceDimension_lower h.level_ge
  refine ⟨hcover, ?_, ?_, ?_, ?_⟩
  · calc
      _ = ∑ u ∈ r.indices,
          (h.sourceDimension u - h.sourceDimension u * (1 - ((r.auxiliaryPrime u : ℝ) - 1)⁻¹) ^ f) := by
        exact Finset.sum_congr rfl fun u hu => by rw [h.rank_eq u hu]
      _ ≤ _ := hloss
  · rw [h.eta_eq]
    positivity [hσ.1]
  · rw [h.frameError_eq]
    constructor <;> linarith [h.gramError_nonneg]
  · rw [h.eta_eq, h.frameError_eq]
    simpa only [add_assoc] using hsmall

/-- Numerical conclusions on the common lattice record in Proposition 18.11.
The slope and frame estimates retain their stronger forms before the slack
in the accounting inequalities is added. -/
structure ChainConstructionCoreConditions {U : Type*} (p : ChainInputs) (c : ChainConstants)
    (r : ChainRecord U p.budget.steps) : Prop where
  rank_pos : ∀ u ∈ r.indices, 0 < r.rank u
  primalPrime : ∀ u ∈ r.indices, (r.auxiliaryPrime u).Prime
  scale_ge_six : 6 ≤ c.scaleConstant
  gain : p.primeSum - r.gain ≤ 6 * p.budget.topCount * p.budget.steps * p.budget.b
  indexLoss : 0 ≤ r.indexLoss ∧ r.indexLoss ≤ p.budget.topCount * p.budget.steps * p.budget.b
  upperSlope : ∀ u ∈ r.indices,
    r.inputMaxSlope u ≤ r.referenceMaxSlope u + r.gain + r.commonLoss - r.finiteLoss u
  lowerSlope : ∀ u ∈ r.indices,
    r.referenceSlope u + r.gain + r.commonLoss - r.finiteLoss u - r.pointLoss p c u ≤ r.inputSlope u
  frame_delta : 0 ≤ r.δ ∧ r.δ ≤ 1 / 2
  frame_slope : ∀ H : ℝ, 0 < H → r.meanSlope - r.targetMinSlope ≤ H →
    r.meanSlope - (1 - r.δ)⁻¹ * (4 * r.spread * Real.log (1 + H / r.spread) +
        (r.η + 4 * Real.sqrt r.frameError) * H) ≤ r.targetSlope
  dual_min : r.targetMinSlope = -r.primalMaxSlope
  dual_ceiling : r.meanSlope + r.primalMaxSlope ≤ p.x ^ c.heightExponent * p.budget.b
  height_bound : ∀ u ∈ r.indices, r.targetSlope + r.height u - r.commonLoss ≤
    p.baseTerm - p.topMass * r.logPrime u + (p.errors c r.indices.card).e4
  local_error : ∀ u ∈ r.indices, ∀ j : Fin p.budget.steps,
    |r.localError u j - p.topMass * p.localLog| ≤ c.scaleConstant * p.budget.liftCost p.x p.ε
  height_identity : ∀ u ∈ r.indices, ∀ v ∈ r.indices,
    r.height u + p.topMass * r.logPrime u = r.height v + p.topMass * r.logPrime v
  levels : Nonempty (ChainLevelPlacement p c r)
  reference_bounds : ∀ u ∈ r.indices, -(p.errors c r.indices.card).e7 ≤ r.referenceSlope u ∧
    r.referenceMaxSlope u ≤ c.scaleConstant * p.budget.topCount * p.budget.a * p.logSize ∧
    r.inputSlope u ≤ r.inputMaxSlope u

/-- The numerical construction conditions after inserting the word count
and the frame bounds from Lemma 13.19. -/
structure ChainConstructionConditions {U : Type*} (p : ChainInputs) (c : ChainConstants)
    (r : ChainRecord U p.budget.steps) : Prop extends ChainConstructionCoreConditions p c r where
  index_count : (r.indices.card : ℝ) ≤ 2 ^ (p.budget.k - 3)
  frame_eta : 0 ≤ r.η
  frame_error : 0 ≤ r.frameError ∧ r.frameError ≤ 1 / 4
  frame_small : (r.η + 4 * Real.sqrt r.frameError) * p.x ^ c.heightExponent ≤ 6

/-- Proposition 18.11 on the numerical projection of a chain. -/
theorem ChainConstructionConditions.toChainConditions {U : Type*} {p : ChainInputs}
    {c : ChainConstants} {r : ChainRecord U p.budget.steps} (h : ChainConstructionConditions p c r)
    (hc : c.Valid) (hp : ExcessSizeBounds p.budget p.x p.ε) : ChainConditions p c r := by
  obtain ⟨levels⟩ := h.levels
  have hx : (1 : ℝ) ≤ p.x := by linarith [hp.scale_ge_three]
  have hpow : 1 ≤ p.scalePower := by
    rw [ChainInputs.scalePower]
    exact Real.one_le_rpow hx hp.epsilon_pos.le
  have hlog : 0 ≤ p.logSize := by linarith [levels.logSize_ge]
  have hcost : 0 ≤ p.budget.liftCost p.x p.ε := by
    unfold ExcessBudget.liftCost
    positivity [hp.b_pos, show 0 ≤ p.x from zero_le_one.trans hx]
  have he₁ : 6 * (p.budget.topCount : ℝ) * p.budget.steps * p.budget.b ≤
      (p.errors c r.indices.card).e1 := by
    change _ ≤ c.scaleConstant * p.budget.topCount * p.budget.steps * p.budget.b *
      p.x ^ (c.lossExponent * p.ε)
    have hr : 1 ≤ p.x ^ (c.lossExponent * p.ε) :=
      Real.one_le_rpow hx (mul_nonneg hc.loss_nonneg hp.epsilon_pos.le)
    calc
      _ ≤ c.scaleConstant * p.budget.topCount * p.budget.steps * p.budget.b := by
        gcongr <;> first | exact hp.b_pos.le | exact h.scale_ge_six
      _ ≤ _ := le_mul_of_one_le_right (by positivity [hp.b_pos, hc.scale_ge_one]) hr
  have hi₁ : (p.budget.topCount : ℝ) * p.budget.steps * p.budget.b ≤
      6 * p.budget.topCount * p.budget.steps * p.budget.b := by
    conv_lhs => rw [← one_mul (p.budget.topCount : ℝ)]
    gcongr <;> first | exact hp.b_pos.le | norm_num
  refine
    { rank_pos := h.rank_pos
      primalPrime := h.primalPrime
      index_count := h.index_count
      k1 := ⟨h.gain.trans he₁, h.indexLoss.1, h.indexLoss.2.trans (hi₁.trans he₁)⟩
      k2 := ?_
      k3_delta := h.frame_delta
      k3_eta := h.frame_eta
      k3_frame := h.frame_error
      k3_small := h.frame_small
      k3 := ?_
      k4_dual := h.dual_min
      k4_ceiling := h.dual_ceiling
      k4 := h.height_bound
      k5 := h.local_error
      k6 := ?_
      k7 := levels.log_bounds hp.k_pos hpow
      k7_variation := levels.log_variation
      k8 := h.reference_bounds }
  · intro u hu
    have hs : 0 ≤ (p.errors c r.indices.card).e5 := by
      change 0 ≤ c.scaleConstant * p.budget.steps * p.budget.liftCost p.x p.ε
      positivity [hc.scale_ge_one, hcost]
    exact ⟨(h.upperSlope u hu).trans (le_add_of_nonneg_right hs), h.lowerSlope u hu⟩
  · intro H hH hgap
    have hc₁ : (1 : ℝ) ≤ r.indices.card := by exact_mod_cast r.nonempty.card_pos
    have hl := Real.log_nonneg hc₁
    linarith only [hl, h.frame_slope H hH hgap]
  · intro u hu v hv
    rw [h.height_identity u hu v hv, sub_self, abs_zero]
    positivity [hc.scale_ge_one, hp.a_pos, hlog, hcost]

end Riemann
