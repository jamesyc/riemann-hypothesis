module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Find

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace Utilities

/-- Round a real number at least one up to a power of two. -/
theorem exists_dyadic_cover {z : ℝ} (hz : 1 ≤ z) :
    ∃ n : ℕ, z ≤ (2 : ℝ) ^ n ∧ (2 : ℝ) ^ n ≤ 2 * z := by
  classical
  have hexists : ∃ n : ℕ, z ≤ (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt z (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn.le⟩
  refine ⟨Nat.find hexists, Nat.find_spec hexists, ?_⟩
  by_cases hzero : Nat.find hexists = 0
  · rw [hzero, pow_zero]
    linarith
  · let k := Nat.find hexists - 1
    have hk : k < Nat.find hexists := by dsimp [k]; omega
    have hprev : (2 : ℝ) ^ k < z := lt_of_not_ge (Nat.find_min hexists hk)
    have hsucc : Nat.find hexists = k + 1 := by dsimp [k]; omega
    rw [hsucc, pow_succ]
    linarith

theorem isLittleO_const_rpow_atTop (C : ℝ) {a : ℝ} (ha : 0 < a) :
    (fun _ : ℝ => C) =o[atTop] (fun x : ℝ => x ^ a) :=
  isLittleO_const_left.mpr (Or.inr ((tendsto_rpow_atTop ha).congr' <|
    (eventually_ge_atTop (0 : ℝ)).mono fun _ hx =>
      (Real.norm_of_nonneg (Real.rpow_nonneg hx a)).symm))

/-- Every fixed exponential in a smaller positive power fits under any fixed
positive fraction of the final exponential budget. -/
theorem eventually_mul_exp_rpow_le {a b c D δ : ℝ}
    (ha : 0 < a) (hab : a < b) (hD : 0 ≤ D) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, D * Real.exp (c * x ^ a) ≤ δ * Real.exp (x ^ b / 2) := by
  have hb : 0 < b := ha.trans hab
  have hsmall : (fun x : ℝ => x ^ a) =o[atTop] (fun x : ℝ => x ^ b) := by
    apply isLittleO_of_tendsto'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx h
      exact ((Real.rpow_pos_of_pos hx b).ne' h).elim
    · refine (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_sub hx, neg_sub]
  have hconst := isLittleO_const_rpow_atTop (Real.log (D / δ)) hb
  by_cases hz : D = 0
  · exact Eventually.of_forall fun x => by simp only [hz, zero_mul]; positivity
  have hnum := ((hsmall.const_mul_left c).add hconst).bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hnum, eventually_ge_atTop (0 : ℝ)] with x hx hx₀
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx₀ _)] at hx
  have hupper := (le_abs_self (c * x ^ a + Real.log (D / δ))).trans hx
  have hlog : Real.exp (Real.log (D / δ)) = D / δ :=
    Real.exp_log (div_pos (lt_of_le_of_ne hD (Ne.symm hz)) hδ)
  have hexp := Real.exp_le_exp.mpr (show c * x ^ a + Real.log (D / δ) ≤ x ^ b / 2 by
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul, mul_comm] using hupper)
  rw [Real.exp_add, hlog] at hexp
  calc
    D * Real.exp (c * x ^ a) = Real.exp (c * x ^ a) * (D / δ) * δ := by
      rw [mul_assoc, div_mul_cancel₀ _ hδ.ne', mul_comm]
    _ ≤ Real.exp (x ^ b / 2) * δ := mul_le_mul_of_nonneg_right hexp hδ.le
    _ = _ := mul_comm _ _

end Utilities
