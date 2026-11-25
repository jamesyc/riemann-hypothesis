module

public import Riemann.AdmissibleExcess
public import Utilities.SmoothedMangoldtVariation

@[expose] public section

open Utilities

namespace Riemann

private theorem norm_weighted_smoothedTwist_sub_le
    (coefficient : ℕ → ℂ) (hcoeff : ∀ n, ‖coefficient n‖ ≤ 1) (D : ℂ)
    {A w w' : ℝ} (hw : 0 < w) (hww' : w ≤ w') (hwA : w ≤ A) :
    ‖(w : ℂ) * smoothedTwist coefficient D (A / w) -
      (w' : ℂ) * smoothedTwist coefficient D (A / w')‖ ≤ 3 * A * (w' - w) / w := by
  have hcancel (t : ℝ) (ht : 0 < t) :
      (t : ℂ) * smoothedTwist coefficient D (A / t) =
        (t : ℂ) * smoothedMangoldt coefficient (A / t) + D * (A : ℂ) := by
    rw [smoothedTwist, mul_add, Complex.ofReal_div, mul_left_comm _ D, mul_div_cancel₀]
    exact_mod_cast ht.ne'
  rw [hcancel _ hw, hcancel _ (hw.trans_le hww'), add_sub_add_right_eq_sub]
  exact norm_weighted_smoothedMangoldt_sub_le coefficient hcoeff hw hww' hwA

private theorem norm_weighted_smoothedZetaSum_sub_le
    {A w w' : ℝ} (hw : 0 < w) (hww' : w ≤ w') (hwA : w ≤ A) :
    ‖(w : ℂ) * (smoothedZetaSum (A / w) : ℂ) -
      (w' : ℂ) * (smoothedZetaSum (A / w') : ℂ)‖ ≤ 3 * A * (w' - w) / w := by
  have hw' := hw.trans_le hww'
  have hA := hw.trans_le hwA
  let R (t : ℝ) := (smoothedMangoldt (fun _ => 1) (A / t)).re
  let C (t : ℝ) := zetaCorrection (A / t)
  let M := 3 * A * (w' - w) / w
  have hr₀ : 0 ≤ w * R w - w' * R w' :=
    sub_nonneg.mpr (weighted_smoothedMangoldt_one_re_antitone hA.le hw hww')
  have hr : w * R w - w' * R w' ≤ M := by
    have h := norm_weighted_smoothedMangoldt_sub_le (fun _ => 1) (by simp) hw hww' hwA
    rw [← smoothedMangoldt_one_real (A / w), ← smoothedMangoldt_one_real (A / w'),
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hcor (t : ℝ) (ht : 0 < t) :
      t * C t = -A * Real.log (A / t) + (1 + Real.eulerMascheroniConstant) * A := by
    dsimp [C, zetaCorrection]
    field_simp
  have hdiff : w' * C w' - w * C w = A * Real.log (w' / w) := by
    rw [hcor _ hw', hcor _ hw, Real.log_div hA.ne' hw'.ne', Real.log_div hA.ne' hw.ne',
      Real.log_div hw'.ne' hw.ne']
    ring
  have hcorr₀ : 0 ≤ w' * C w' - w * C w := by
    rw [hdiff]
    exact mul_nonneg hA.le (Real.log_nonneg ((one_le_div hw).mpr hww'))
  have hcorr : w' * C w' - w * C w ≤ M := by
    rw [hdiff]
    calc
      _ ≤ A * (w' / w - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hw' hw)) hA.le
      _ = A * (w' - w) / w := by field_simp
      _ ≤ M := by
        dsimp only [M]
        gcongr
        linarith
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  change |w * (R w + C w) - w' * (R w' + C w')| ≤ M
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The uniform weighted-variation hypothesis of Theorem 4.2 follows from
Lemma 4.1(i) and the identification of the prime-power coefficients. -/
theorem HostInducingConditions.weightedVariation
    {H : Type} [AddCommGroup H] [Fintype H]
    {prime : PrimeExcessData H} {inducing : ExcessCharacter H → BundledDirichletCharacter}
    (h : HostInducingConditions prime inducing)
    (ψ : ExcessCharacter H) (A w w' : ℝ)
    (_hA : 0 < A) (hw : 0 < w) (hwA : w ≤ A) (hw' : 0 < w') (hw'A : w' ≤ A) :
    ‖(w : ℂ) * prime.smoothed ψ (A / w) - (w' : ℂ) * prime.smoothed ψ (A / w')‖ ≤
      3 * A * |w - w'| / min w w' := by
  have hordered (v v' : ℝ) (hv : 0 < v) (hvv' : v ≤ v') (hvA : v ≤ A) :
      ‖(v : ℂ) * prime.smoothed ψ (A / v) - (v' : ℂ) * prime.smoothed ψ (A / v')‖ ≤
        3 * A * (v' - v) / v := by
    by_cases hψ : ψ = 0
    · rw [hψ, prime.smoothed_zero, prime.smoothed_zero]
      exact norm_weighted_smoothedZetaSum_sub_le hv hvv' hvA
    have hcoeff (n : ℕ) : ‖prime.coefficient ψ n‖ ≤ 1 := by
      by_cases hn : IsPrimePow n
      · rw [h.inducing_coefficient ψ n hn]
        exact (inducing ψ).character.norm_le_one _
      · simp [PrimeExcessData.coefficient, hn]
    simp only [PrimeExcessData.smoothed, ite_eq_right hψ]
    exact norm_weighted_smoothedTwist_sub_le _ hcoeff _ hv hvv' hvA
  rcases le_total w w' with hww' | hww'
  · rw [min_eq_left hww', abs_of_nonpos (sub_nonpos.mpr hww'), neg_sub]
    exact hordered w w' hw hww' hwA
  · rw [min_eq_right hww', abs_of_nonneg (sub_nonneg.mpr hww'), norm_sub_rev]
    exact hordered w' w hw' hww' hw'A

/-- Near a scale at least three, weighted variation bounds the local
change by the normalized norm at the scale and an absolute constant. -/
theorem HostInducingConditions.localVariation_le
    {H : Type} [AddCommGroup H] [Fintype H]
    {prime : PrimeExcessData H} {inducing : ExcessCharacter H → BundledDirichletCharacter}
    (h : HostInducingConditions prime inducing)
    (ψ : ExcessCharacter H) {x y M : ℝ} (hx : 3 ≤ x) (hclose : |y - x| ≤ 1)
    (hG : ‖prime.smoothed ψ x‖ ≤ M * x) :
    ‖prime.smoothed ψ y - prime.smoothed ψ x‖ ≤ 4 + M := by
  let G := prime.smoothed ψ
  have hx₀ : 0 < x := by linarith
  have hy₁ : 1 ≤ y := by linarith [(abs_le.mp hclose).1]
  have hy₀ : 0 < y := zero_lt_one.trans_le hy₁
  let A := x * y
  have hxA : x ≤ A := by
    dsimp only [A]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy₁ hx₀.le
  have hyA : y ≤ A := by
    dsimp only [A]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by linarith : 1 ≤ x) hy₀.le
  have hweighted := h.weightedVariation ψ A x y (mul_pos hx₀ hy₀) hx₀ hxA hy₀ hyA
  have hAx : A / x = y := by dsimp [A]; field_simp
  have hAy : A / y = x := by dsimp [A]; field_simp
  rw [hAx, hAy] at hweighted
  have hmax : A / min x y = max x y := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy, max_eq_right hxy, hAx]
    · rw [min_eq_right hyx, max_eq_left hyx, hAy]
  have habs : |x - y| ≤ 1 := by rwa [abs_sub_comm]
  have hscale : 3 * A * |x - y| / min x y ≤ 4 * x := by
    have hbound : max x y ≤ x + 1 :=
      max_le (by linarith) (by linarith [(abs_le.mp hclose).2])
    calc
      _ = 3 * (A / min x y) * |x - y| := by ring
      _ ≤ 3 * (x + 1) := by
        rw [hmax]
        exact (mul_le_of_le_one_right (by positivity) habs).trans
          (mul_le_mul_of_nonneg_left hbound (by norm_num))
      _ ≤ _ := by linarith
  have hterm : ‖((y : ℂ) - (x : ℂ)) * G x‖ ≤ M * x := by
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) hclose).trans hG
  have hrearrange : (x : ℂ) * (G y - G x) =
      ((x : ℂ) * G y - (y : ℂ) * G x) + ((y : ℂ) - (x : ℂ)) * G x := by ring
  apply (le_of_mul_le_mul_left ?_ hx₀)
  calc
    x * ‖G y - G x‖ = ‖(x : ℂ) * (G y - G x)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx₀.le]
    _ ≤ 4 * x + M * x := by
      rw [hrearrange]
      exact (norm_add_le _ _).trans (add_le_add (hweighted.trans hscale) hterm)
    _ = x * (4 + M) := by ring

end Riemann
