module

public import Utilities.CenterMass
import Mathlib.Tactic.Linarith

@[expose] public section

open Utilities
open scoped BigOperators

namespace Riemann

/-- The seven errors entering (3.1)–(3.7). -/
structure AccountingErrors where
  e1 : ℝ
  e2 : ℝ
  e3 : ℝ
  e4 : ℝ
  e5 : ℝ
  e6 : ℝ
  e7 : ℝ

noncomputable def AccountingErrors.total (e : AccountingErrors) (A : ℝ) : ℝ :=
  e.e1 + e.e2 + e.e3 + e.e4 + e.e5 + A * e.e6 + e.e7

/-- The scalar data of Proposition 3.1. The terms shared by all indices
are factored out of the sums over the tops and nodes. -/
structure AccountingData (U : Type*) where
  indices : Finset U
  rankWeight : U → ℝ
  inputSlope : U → ℝ
  referenceSlope : U → ℝ
  height : U → ℝ
  finiteLoss : U → ℝ
  logPrime : U → ℝ
  primeSum : ℝ
  gain : ℝ
  commonLoss : ℝ
  targetSlope : ℝ
  baseTerm : ℝ
  topMass : ℝ
  nodeLogSum : ℝ
  localLog : ℝ

noncomputable def AccountingData.mainTerm {U : Type*} (d : AccountingData U) : ℝ :=
  d.baseTerm - d.topMass * d.nodeLogSum

structure AccountingHypotheses {U : Type*} (d : AccountingData U)
    (e : AccountingErrors) : Prop where
  indices_nonempty : d.indices.Nonempty
  rank_pos : ∀ u ∈ d.indices, 0 < d.rankWeight u
  topMass_nonneg : 0 ≤ d.topMass
  primeSum_le : d.primeSum ≤ d.gain + e.e1
  inputSlope_lower : ∀ u ∈ d.indices,
    d.referenceSlope u + d.gain + d.commonLoss - d.finiteLoss u - e.e2 ≤ d.inputSlope u
  mean_le : d.indices.centerMass d.rankWeight (fun u => d.inputSlope u - d.height u) - e.e3 ≤
    d.targetSlope
  height_le : ∀ u ∈ d.indices,
    d.targetSlope + d.height u - d.commonLoss ≤ d.baseTerm - d.topMass * d.logPrime u + e.e4
  finiteLoss_le : ∀ u ∈ d.indices, d.finiteLoss u ≤ d.topMass * d.localLog + e.e5
  logPrime_lower : ∀ u ∈ d.indices, d.nodeLogSum + d.localLog - e.e6 ≤ d.logPrime u
  referenceSlope_lower : ∀ u ∈ d.indices, -e.e7 ≤ d.referenceSlope u

/-- Proposition 3.1 in the factorization used by the excess sum. -/
theorem accounting_primeSum_le {U : Type*} {d : AccountingData U} {e : AccountingErrors}
    (h : AccountingHypotheses d e) :
    d.primeSum ≤ d.mainTerm + e.total d.topMass := by
  let lower := d.gain + d.targetSlope - d.mainTerm -
    (e.e2 + e.e4 + e.e5 + d.topMass * e.e6 + e.e7)
  have hpoint : ∀ u ∈ d.indices, lower ≤ d.inputSlope u - d.height u := by
    intro u hu
    have hlog := mul_le_mul_of_nonneg_left (h.logPrime_lower u hu) h.topMass_nonneg
    have hin := h.inputSlope_lower u hu
    have hheight := h.height_le u hu
    have hfinite := h.finiteLoss_le u hu
    have href := h.referenceSlope_lower u hu
    dsimp [lower, AccountingData.mainTerm]
    linarith
  have hweight : 0 < ∑ u ∈ d.indices, d.rankWeight u :=
    Finset.sum_pos h.rank_pos h.indices_nonempty
  have havg : lower ≤ d.indices.centerMass d.rankWeight
      (fun u => d.inputSlope u - d.height u) :=
    const_le_centerMass_real (fun u hu => (h.rank_pos u hu).le) hweight.ne' hpoint
  have hmean := h.mean_le
  have hprime := h.primeSum_le
  dsimp only [lower] at havg
  unfold AccountingErrors.total
  linarith

/-- Corollary 3.4 given the identity that expresses the prime sum as main term plus excess. -/
theorem accounting_excess_le {U : Type*} {d : AccountingData U} {e : AccountingErrors}
    {excess : ℝ} (h : AccountingHypotheses d e) (hidentity : d.primeSum = d.mainTerm + excess) :
    excess ≤ e.total d.topMass := by
  have hprime := accounting_primeSum_le h
  rw [hidentity] at hprime
  exact le_of_add_le_add_left hprime

end Riemann
