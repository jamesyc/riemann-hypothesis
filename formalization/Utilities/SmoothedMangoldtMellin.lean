module

public import Mathlib.NumberTheory.LSeries.Basic
public import Utilities.SmoothedMangoldt
public import Utilities.Mellin
import Mathlib.NumberTheory.LSeries.Dirichlet
import Utilities.IntegralSeries

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Utilities

/-- Absolute convergence of the von Mangoldt L-series bounds the smoothed
sum by every real power strictly above the linear scale. -/
theorem norm_smoothedMangoldt_le_rpow (coefficient : ℕ → ℂ)
    (hcoeff : ∀ n, ‖coefficient n‖ ≤ 1) {a : ℝ} (ha : 1 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, ‖smoothedMangoldt coefficient x‖ ≤ B * x ^ a := by
  let t (n : ℕ) := ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (a : ℂ) n‖
  have hsum : Summable t := summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (show 1 < (a : ℂ).re by simpa only [Complex.ofReal_re] using ha))
  let B := ∑' n, t n
  refine ⟨B, tsum_nonneg (fun n => norm_nonneg _), fun x hx => ?_⟩
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  let term (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1) : ℝ) : ℂ) * coefficient n
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 (Nat.floor x)) : ‖term n‖ ≤ x ^ a * t n := by
    obtain ⟨hn₁, hnFloor⟩ := Finset.mem_Icc.mp hn
    have hn₀ : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn₁
    have hnPos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn₀)
    have hnt : (n : ℝ) ≤ x := (Nat.le_floor_iff hx₀).mp hnFloor
    have hratio : 1 ≤ x / (n : ℝ) := (le_div_iff₀ hnPos).mpr (by simpa only [one_mul] using hnt)
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hpos : 0 ≤ ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1) :=
      mul_nonneg hΛ (sub_nonneg.mpr hratio)
    calc
      _ = ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1) * ‖coefficient n‖ := by
        dsimp only [term]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
      _ ≤ ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1) :=
        mul_le_of_le_one_right hpos (hcoeff n)
      _ ≤ ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) hΛ
      _ ≤ ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ a := by
        have hp := Real.rpow_le_rpow_of_exponent_le hratio ha.le
        rw [Real.rpow_one] at hp
        exact mul_le_mul_of_nonneg_left hp hΛ
      _ = _ := by
        dsimp only [t]
        rw [Real.div_rpow hx₀ hnPos.le, LSeries.norm_term_eq, ite_eq_right hn₀,
          Complex.norm_real, Real.norm_of_nonneg hΛ, Complex.ofReal_re]
        ring
  calc
    ‖smoothedMangoldt coefficient x‖ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), ‖term n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), x ^ a * t n := Finset.sum_le_sum hterm
    _ = x ^ a * (∑ n ∈ Finset.Icc 1 (Nat.floor x), t n) := by rw [Finset.mul_sum]
    _ ≤ x ^ a * B := mul_le_mul_of_nonneg_left
      (hsum.sum_le_tsum _ fun _ _ => norm_nonneg _) (Real.rpow_nonneg hx₀ _)
    _ = B * x ^ a := mul_comm _ _

private noncomputable def mangoldtMellinTerm (coefficient : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℝ → ℂ :=
  (Set.Ioi (n : ℝ)).indicator fun x =>
    ((ArithmeticFunction.vonMangoldt n : ℂ) * coefficient n) *
      (((x : ℂ) / (n : ℂ) - 1) * (x : ℂ) ^ (-s - 1))

private theorem mangoldtMellinTerm_integrable (coefficient : ℕ → ℂ) {s : ℂ}
    (hs : 1 < s.re) (n : ℕ) : Integrable (mangoldtMellinTerm coefficient s n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mangoldtMellinTerm]
  · rw [mangoldtMellinTerm, integrable_indicator_iff measurableSet_Ioi, IntegrableOn]
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simpa only [Complex.ofReal_natCast] using
      (integrableOn_smoothedLinearKernel hn' hs).const_mul
        ((ArithmeticFunction.vonMangoldt n : ℂ) * coefficient n)

private theorem integral_mangoldtMellinTerm (coefficient : ℕ → ℂ) {s : ℂ}
    (hs : 1 < s.re) (n : ℕ) :
    (∫ x : ℝ, mangoldtMellinTerm coefficient s n x) =
      LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ) * coefficient k) s n /
        (s * (s - 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mangoldtMellinTerm]
  · have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [mangoldtMellinTerm, integral_indicator measurableSet_Ioi, integral_const_mul,
      ← Complex.ofReal_natCast n, integral_smoothedLinearKernel hn' hs,
      LSeries.term_of_ne_zero hn, Complex.ofReal_natCast, Complex.cpow_neg]
    simp only [div_eq_mul_inv]
    ring

private theorem integral_norm_mangoldtMellinTerm_le (coefficient : ℕ → ℂ)
    (hcoeff : ∀ n, ‖coefficient n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    (∫ x : ℝ, ‖mangoldtMellinTerm coefficient s n x‖) ≤
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) / (s.re - 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mangoldtMellinTerm]
  · have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    let w := (ArithmeticFunction.vonMangoldt n : ℂ) * coefficient n
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hw : ‖w‖ ≤ ArithmeticFunction.vonMangoldt n := by
      dsimp [w]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
      exact mul_le_of_le_one_right hΛ (hcoeff n)
    calc
      _ = ‖w‖ * ∫ x : ℝ in Set.Ioi (n : ℝ),
          ‖((x : ℂ) / (n : ℂ) - 1) * (x : ℂ) ^ (-s - 1)‖ := by
        change (∫ x : ℝ, ‖(Set.Ioi (n : ℝ)).indicator
          (fun x => w * (((x : ℂ) / (n : ℂ) - 1) * (x : ℂ) ^ (-s - 1))) x‖) = _
        simp only [norm_indicator_eq_indicator_norm, norm_mul, integral_indicator measurableSet_Ioi,
          integral_const_mul]
      _ ≤ ‖w‖ * ((n : ℝ) ^ (-s.re) / (s.re - 1)) := mul_le_mul_of_nonneg_left
        (by simpa only [Complex.ofReal_natCast] using integral_norm_smoothedLinearKernel_le hn' hs)
        (norm_nonneg w)
      _ ≤ _ := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hw
          (div_nonneg (Real.rpow_nonneg hn'.le _) (sub_nonneg.mpr hs.le))

/-- At each point the series has finite support. Equality at a cutoff endpoint
holds because the corresponding linear factor is zero. -/
private theorem smoothedMangoldt_kernel_eq_tsum (coefficient : ℕ → ℂ) (s : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    (x : ℂ) ^ (-s - 1) * smoothedMangoldt coefficient x =
      ∑' n : ℕ, mangoldtMellinTerm coefficient s n x := by
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  rw [tsum_eq_sum (s := Finset.Icc 1 (Nat.floor x))]
  · unfold smoothedMangoldt
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn₁ := (Finset.mem_Icc.mp hn).1
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx₀).mp (Finset.mem_Icc.mp hn).2
    rcases hnx.lt_or_eq with hlt | heq
    · rw [mangoldtMellinTerm, Set.indicator_of_mem (show x ∈ Set.Ioi (n : ℝ) from hlt),
        Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_natCast]
      ring
    · subst x
      have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn₁)
      simp [mangoldtMellinTerm, hn₀]
  · intro n hn
    by_cases hn₀ : n = 0
    · simp [mangoldtMellinTerm, hn₀]
    · have hfloor : Nat.floor x < n := lt_of_not_ge fun hle =>
        hn (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn₀, hle⟩)
      have hlt : x < (n : ℝ) := (Nat.floor_lt hx₀).mp hfloor
      have hnot : x ∉ Set.Ioi (n : ℝ) := not_lt.mpr hlt.le
      simp [mangoldtMellinTerm, hnot]

/-- Absolute convergence justifies summing the single-cutoff Mellin formula. -/
theorem smoothedMangoldt_hasMellin (coefficient : ℕ → ℂ)
    (hcoeff : ∀ n, ‖coefficient n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator (smoothedMangoldt coefficient)) (-s)
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * coefficient n) s /
        (s * (s - 1))) := by
  let F := mangoldtMellinTerm coefficient s
  have hInt : ∀ n, Integrable (F n) := mangoldtMellinTerm_integrable coefficient hs
  have hnorm : Summable fun n => ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n‖ :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  have hmajor (n : ℕ) : ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) =
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n‖ := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.norm_term_eq, ite_eq_right hn, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.rpow_neg (Nat.cast_nonneg n),
        div_eq_mul_inv]
  have hsum : Summable fun n => ∫ x : ℝ, ‖F n x‖ := by
    apply Summable.of_nonneg_of_le (f := fun n =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) / (s.re - 1))
    · exact fun _ => integral_nonneg fun _ => norm_nonneg _
    · exact integral_norm_mangoldtMellinTerm_le coefficient hcoeff hs
    · simp_rw [hmajor]
      exact hnorm.div_const _
  have htotal := integrable_tsum_of_summable_integral_norm hInt hsum
  have hkernel : Set.EqOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * smoothedMangoldt coefficient x)
      (fun x => ∑' n, F n x) (Set.Ici 1) := fun _ hx => smoothedMangoldt_kernel_eq_tsum coefficient s hx
  have hsupport : (Set.Ici (1 : ℝ)).indicator (fun x => ∑' n, F n x) = (fun x => ∑' n, F n x) := by
    funext x
    by_cases hx : x ∈ Set.Ici (1 : ℝ)
    · exact Set.indicator_of_mem hx _
    · have hx' : x < 1 := lt_of_not_ge hx
      have hzero (n : ℕ) : F n x = 0 := by
        rcases eq_or_ne n 0 with rfl | hn
        · simp [F, mangoldtMellinTerm]
        · have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          have hnot : x ∉ Set.Ioi (n : ℝ) := not_lt.mpr (hx'.trans_le hn').le
          simp [F, mangoldtMellinTerm, hnot]
      simp [hx, hzero]
  rw [hasMellin_cutoffOne_iff]
  refine ⟨htotal.integrableOn.congr_fun (fun x hx => (hkernel hx).symm) measurableSet_Ici, ?_⟩
  calc
    _ = ∫ x : ℝ in Set.Ici 1, ∑' n, F n x := setIntegral_congr_fun measurableSet_Ici hkernel
    _ = ∫ x : ℝ, ∑' n, F n x := by rw [← integral_indicator measurableSet_Ici, hsupport]
    _ = ∑' n, ∫ x : ℝ, F n x := (integral_tsum_of_summable_integral_norm hInt hsum).symm
    _ = _ := by
      simp_rw [F, integral_mangoldtMellinTerm coefficient hs]
      rw [tsum_div_const, LSeries]

end Utilities
