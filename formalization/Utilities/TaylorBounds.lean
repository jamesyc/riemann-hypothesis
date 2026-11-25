module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter
open scoped Topology

namespace Utilities

/-- The `k`th Taylor coefficient in the coordinate `center - z`. -/
noncomputable def signedTaylorCoefficient (f : ℂ → ℂ) (center : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * iteratedDeriv k f center / (k.factorial : ℂ)

theorem signedTaylorCoefficient_congr_eventuallyEq {f g : ℂ → ℂ} {center : ℂ}
    (heq : f =ᶠ[𝓝 center] g) (k : ℕ) :
    signedTaylorCoefficient f center k = signedTaylorCoefficient g center k := by
  unfold signedTaylorCoefficient
  rw [heq.iteratedDeriv_eq k]

theorem signedTaylorCoefficient_add {f g : ℂ → ℂ} {center : ℂ}
    (hf : AnalyticAt ℂ f center) (hg : AnalyticAt ℂ g center) (k : ℕ) :
    signedTaylorCoefficient (fun z => f z + g z) center k =
      signedTaylorCoefficient f center k + signedTaylorCoefficient g center k := by
  unfold signedTaylorCoefficient
  rw [iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt]
  ring

theorem signedTaylorCoefficient_simplePole (pole residue center : ℂ) (k : ℕ) :
    signedTaylorCoefficient (fun z => residue / (z - pole)) center k =
      residue / (center - pole) ^ (k + 1) := by
  have hfun : (fun z : ℂ => residue / (z - pole)) = fun z => residue * (z - pole)⁻¹ := by
    funext z
    rw [div_eq_mul_inv]
  have hInv : deriv^[k] (fun z : ℂ => (z - pole)⁻¹) center =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) * (center - pole) ^ (-1 - (k : ℤ)) := by
    simpa only [one_mul, one_pow, mul_one] using
      congrFun (iter_deriv_inv_linear_sub k (1 : ℂ) pole) center
  have hpow : (center - pole) ^ (-1 - (k : ℤ)) = ((center - pole) ^ (k + 1 : ℕ))⁻¹ := by
    rw [show (-1 : ℤ) - (k : ℤ) = -((k + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; simp
  have hfact : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  unfold signedTaylorCoefficient
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, hInv, hpow]
  calc
    _ = residue * ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ((k.factorial : ℂ) / k.factorial) *
        ((center - pole) ^ (k + 1 : ℕ))⁻¹ := by ring
    _ = _ := by simp only [hsign, div_self hfact, mul_one, div_eq_mul_inv]

/-- Cauchy's estimate makes the signed Taylor coefficients of an analytic
remainder decay after normalization at any smaller radius. -/
theorem tendsto_scaled_signedTaylorCoefficient_re {f : ℂ → ℂ} {center : ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : r < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall center R)) :
    Tendsto (fun k : ℕ => r ^ (k + 1) * (signedTaylorCoefficient f center k).re) atTop (𝓝 0) := by
  have hR₀ : 0 < R := hr.trans hR
  have hd : DifferentiableOn ℂ f (closure (Metric.ball center R)) :=
    fun z hz => (hf z (Metric.closure_ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere center R).exists_bound_of_continuousOn
    (hf.continuousOn.mono Metric.sphere_subset_closedBall)
  let B := max 0 C
  have hB (z : ℂ) (hz : z ∈ Metric.sphere center R) : ‖f z‖ ≤ B := (hC z hz).trans (le_max_right _ _)
  have hnorm (k : ℕ) : ‖signedTaylorCoefficient f center k‖ ≤ B / R ^ k := by
    have hfact : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR₀ hd.diffContOnCl hB
    calc
      _ = ‖iteratedDeriv k f center‖ / (k.factorial : ℝ) := by
        simp [signedTaylorCoefficient, norm_pow]
      _ ≤ ((k.factorial : ℝ) * B / R ^ k) / (k.factorial : ℝ) :=
        div_le_div_of_nonneg_right hCauchy hfact.le
      _ = _ := by field_simp [hfact.ne', (pow_pos hR₀ k).ne']
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (g := fun k : ℕ => (B * r) * (r / R) ^ k) ?_ ?_
  · intro k
    have hk : 0 ≤ r ^ (k + 1 : ℕ) := pow_nonneg hr.le _
    calc
      _ = r ^ (k + 1) * |(signedTaylorCoefficient f center k).re| := by
        rw [norm_mul, Real.norm_of_nonneg hk, Real.norm_eq_abs]
      _ ≤ r ^ (k + 1) * (B / R ^ k) := mul_le_mul_of_nonneg_left
        ((Complex.abs_re_le_norm _).trans (hnorm k)) hk
      _ = _ := by rw [pow_succ, div_pow]; ring
  · have hr' : r / R < 1 := (div_lt_iff₀ hR₀).mpr (by simpa only [one_mul] using hR)
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr.le hR₀.le) hr').const_mul (B * r)

end Utilities
