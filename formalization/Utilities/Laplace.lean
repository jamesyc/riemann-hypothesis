module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Utilities

/-- The signed moment for derivatives of the Laplace transform on `[0,∞)`. -/
noncomputable def laplaceMoment (g : ℝ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ici 0, (-(u : ℂ)) ^ k * Complex.exp (-s * (u : ℂ)) * g u

theorem hasDerivAt_laplaceMoment {g : ℝ → ℂ} (hg : Measurable g)
    {a B : ℝ} (hB : 0 ≤ B) (hgrowth : ∀ u ≥ 0, ‖g u‖ ≤ B * Real.exp (a * u))
    (k : ℕ) {s : ℂ} (hs : a < s.re) :
    HasDerivAt (laplaceMoment g k) (laplaceMoment g (k + 1) s) s := by
  let δ := (s.re - a) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let D : Set ℂ := {z | a + δ < z.re}
  have hsD : s ∈ D := by change a + δ < s.re; dsimp [δ]; linarith
  have hD : D ∈ 𝓝 s := (Complex.isOpen_re_gt (a + δ)).mem_nhds hsD
  let μ := volume.restrict (Set.Ici (0 : ℝ))
  let kernel (j : ℕ) (z : ℂ) (u : ℝ) := (-(u : ℂ)) ^ j * Complex.exp (-z * (u : ℂ)) * g u
  let majorant (j : ℕ) (u : ℝ) := B * (u ^ j * Real.exp (-(δ * u)))
  have hmeas (j : ℕ) (z : ℂ) : AEStronglyMeasurable (kernel j z) μ := by
    have h := (show Continuous (fun u : ℝ => (-(u : ℂ)) ^ j * Complex.exp (-z * (u : ℂ))) by fun_prop)
    exact h.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have hmajorant (j : ℕ) : Integrable (majorant j) μ := by
    change IntegrableOn (majorant j) (Set.Ici (0 : ℝ))
    rw [integrableOn_Ici_iff_integrableOn_Ioi, IntegrableOn]
    have hj : (-1 : ℝ) < (j : ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg j)
    simpa only [majorant, Real.rpow_natCast, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hj zero_lt_one hδ).const_mul B
  have hbound (j : ℕ) (z : ℂ) (hz : z ∈ D) (u : ℝ) (hu : 0 ≤ u) :
      ‖kernel j z u‖ ≤ majorant j u := by
    have hdiff : (a - z.re) * u ≤ -(δ * u) := by
      change a + δ < z.re at hz
      simpa only [neg_mul] using mul_le_mul_of_nonneg_right (show a - z.re ≤ -δ by linarith) hu
    calc
      _ = (u ^ j * Real.exp (-z.re * u)) * ‖g u‖ := by
        simp only [kernel, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hu, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
      _ ≤ (u ^ j * Real.exp (-z.re * u)) * (B * Real.exp (a * u)) :=
        mul_le_mul_of_nonneg_left (hgrowth u hu) (by positivity)
      _ = B * (u ^ j * (Real.exp (-z.re * u) * Real.exp (a * u))) := by ring
      _ = B * (u ^ j * Real.exp ((a - z.re) * u)) := by
        rw [← Real.exp_add, show -z.re * u + a * u = (a - z.re) * u by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdiff) (pow_nonneg hu _)) hB
  have hae : ∀ᵐ u ∂μ, 0 ≤ u := ae_restrict_mem measurableSet_Ici
  have hint : Integrable (kernel k s) μ :=
    (hmajorant k).mono' (hmeas k s) (hae.mono fun u hu => hbound k s hsD u hu)
  have hderiv (z : ℂ) (u : ℝ) : HasDerivAt (fun t => kernel k t u) (kernel (k + 1) z u) z := by
    have h := (hasDerivAt_neg' z).mul_const (u : ℂ)
    have hexp := (h.cexp.const_mul ((-(u : ℂ)) ^ k)).mul_const (g u)
    refine hexp.congr_deriv ?_
    simp only [kernel, neg_one_mul, pow_succ]
    ring
  change HasDerivAt (fun z => ∫ u, kernel k z u ∂μ) (∫ u, kernel (k + 1) s u ∂μ) s
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := majorant (k + 1)) hD
    (Eventually.of_forall (hmeas k)) hint (hmeas (k + 1) s)
    (hae.mono fun u hu z hz => hbound (k + 1) z hz u hu) (hmajorant (k + 1))
    (Eventually.of_forall fun u z _ => hderiv z u)).2

theorem iteratedDeriv_laplace_eq_moment {g : ℝ → ℂ} (hg : Measurable g)
    {a B : ℝ} (hB : 0 ≤ B) (hgrowth : ∀ u ≥ 0, ‖g u‖ ≤ B * Real.exp (a * u))
    (k : ℕ) {s : ℂ} (hs : a < s.re) :
    iteratedDeriv k (laplaceMoment g 0) s = laplaceMoment g k s := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have heq : iteratedDeriv k (laplaceMoment g 0) =ᶠ[𝓝 s] laplaceMoment g k := by
      filter_upwards [(Complex.isOpen_re_gt a).mem_nhds hs] with z hz
      exact ih hz
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact (hasDerivAt_laplaceMoment hg hB hgrowth k hs).deriv

end Utilities
