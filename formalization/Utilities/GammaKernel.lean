module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Sqrt

@[expose] public section

open Filter
open scoped Topology

namespace Utilities

noncomputable def mellinGammaKernel (a : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  u ^ k * Real.exp (-(a * u)) / (k.factorial : ℝ)

/-- Multiplying the kernel by an exponential shifts its rate parameter. -/
theorem exp_mul_mellinGammaKernel (a t : ℝ) (k : ℕ) (u : ℝ) :
    Real.exp (t * u) * mellinGammaKernel a k u = mellinGammaKernel (a - t) k u := by
  unfold mellinGammaKernel
  rw [show -((a - t) * u) = t * u + -(a * u) by ring, Real.exp_add]
  ring

theorem integral_mellinGammaKernel (a : ℝ) (ha : 0 < a) (k : ℕ) :
    (∫ u : ℝ in Set.Ici 0, mellinGammaKernel a k u) = (1 / a) ^ (k + 1) := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  simp only [mellinGammaKernel, MeasureTheory.integral_div]
  have hscaled : (1 / a) ^ ((k : ℝ) + 1) = (1 / a) ^ (k + 1) := by
    rw [← Nat.cast_succ, Real.rpow_natCast]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := a) (by positivity) ha
  simp only [add_sub_cancel_right, Real.rpow_natCast, hscaled, Real.Gamma_nat_eq_factorial] at h
  rw [h, mul_div_cancel_right₀]
  exact_mod_cast Nat.factorial_ne_zero k

theorem mellinGammaKernel_integrable {a : ℝ} (ha : 0 < a) (k : ℕ) :
    MeasureTheory.IntegrableOn (mellinGammaKernel a k) (Set.Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hk : (-1 : ℝ) < (k : ℝ) := lt_of_lt_of_le (by norm_num) k.cast_nonneg
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := a)
    hk zero_lt_one ha
  change MeasureTheory.Integrable
    (fun u : ℝ => u ^ k * Real.exp (-(a * u)) / (k.factorial : ℝ))
    (MeasureTheory.volume.restrict (Set.Ioi 0))
  simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using (h.div_const (k.factorial : ℝ))

theorem mellinGammaKernel_nonneg (a : ℝ) (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ mellinGammaKernel a k u := by
  unfold mellinGammaKernel
  positivity

/-- Exponential comparison on a measurable part of the nonnegative axis. -/
theorem mellinGammaKernel_restrict_le {a b v : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ)
    {D : Set ℝ} (hD : MeasurableSet D) (hD₀ : D ⊆ Set.Ici 0)
    (hcutoff : ∀ u ∈ D, (b - a) * u ≤ v) :
    (∫ u in D, mellinGammaKernel a k u) ≤ Real.exp v * (1 / b) ^ (k + 1) := by
  have hB := mellinGammaKernel_integrable hb k
  have hBnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ici 0)] mellinGammaKernel b k :=
    (MeasureTheory.ae_restrict_mem measurableSet_Ici).mono fun _ hu => mellinGammaKernel_nonneg b k hu
  have hcompare := MeasureTheory.setIntegral_mono_on
    ((mellinGammaKernel_integrable ha k).mono_set hD₀)
    ((hB.mono_set hD₀).const_mul (Real.exp v)) hD
    (fun u hu => show mellinGammaKernel a k u ≤ Real.exp v * mellinGammaKernel b k u from by
      have he : Real.exp (-(a * u)) = Real.exp ((b - a) * u) * Real.exp (-(b * u)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = Real.exp ((b - a) * u) * mellinGammaKernel b k u := by
          unfold mellinGammaKernel
          rw [he]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hcutoff u hu))
          (mellinGammaKernel_nonneg b k (hD₀ hu)))
  calc
    _ ≤ ∫ u in D, Real.exp v * mellinGammaKernel b k u := hcompare
    _ = Real.exp v * (∫ u in D, mellinGammaKernel b k u) :=
      MeasureTheory.integral_const_mul _ _
    _ ≤ Real.exp v * (∫ u : ℝ in Set.Ici 0, mellinGammaKernel b k u) :=
      mul_le_mul_of_nonneg_left
        (MeasureTheory.setIntegral_mono_set hB hBnonneg hD₀.eventuallySubset)
        (Real.exp_pos _).le
    _ = _ := by rw [integral_mellinGammaKernel b hb k]

/-- An exponential bound for the left tail of the normalized Gamma kernel. -/
theorem mellinGammaKernel_left_tail {a b U : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    (∫ u : ℝ in Set.Icc 0 U, mellinGammaKernel a k u) ≤
      Real.exp ((b - a) * U) * (1 / b) ^ (k + 1) :=
  mellinGammaKernel_restrict_le ha (ha.trans_le hab) k measurableSet_Icc
    (fun _ hu => hu.1)
    (fun _ hu => mul_le_mul_of_nonneg_left hu.2 (sub_nonneg.mpr hab))

/-- An exponential bound for the right tail of the normalized Gamma kernel. -/
theorem mellinGammaKernel_right_tail {a b U : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hU : 0 ≤ U) (k : ℕ) :
    (∫ u : ℝ in Set.Ioi U, mellinGammaKernel a k u) ≤
      Real.exp ((b - a) * U) * (1 / b) ^ (k + 1) :=
  mellinGammaKernel_restrict_le (hb.trans_le hba) hb k measurableSet_Ioi
    (fun _ hu => hU.trans (Set.mem_Ioi.mp hu).le)
    (fun _ hu => mul_le_mul_of_nonpos_left (Set.mem_Ioi.mp hu).le (sub_nonpos.mpr hba))

/-- Estimate a weighted Gamma integral using a one-sided bound on `[L,U]`
and an absolute bound on the two tails. -/
theorem integral_weighted_mellinGammaKernel_le_three_ranges {F : ℝ → ℝ} (hF : Measurable F)
    {σ outsideExponent windowExponent B C L U bLeft bRight : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (ha : 0 < σ - outsideExponent) (hb : 0 < σ - windowExponent)
    (hL : 0 ≤ L) (hLU : L ≤ U)
    (hLeft : σ - outsideExponent ≤ bLeft) (hRight₀ : 0 < bRight)
    (hRight : bRight ≤ σ - outsideExponent)
    (houtside : ∀ u ≥ 0, |F u| ≤ B * Real.exp (outsideExponent * u))
    (hwindow : ∀ u ∈ Set.Icc L U, F u ≤ C * Real.exp (windowExponent * u)) (k : ℕ) :
    (∫ u : ℝ in Set.Ici 0, F u * mellinGammaKernel σ k u) ≤
      B * (Real.exp ((bLeft - (σ - outsideExponent)) * L) * (1 / bLeft) ^ (k + 1)) +
      C * (1 / (σ - windowExponent)) ^ (k + 1) +
      B * (Real.exp ((bRight - (σ - outsideExponent)) * U) * (1 / bRight) ^ (k + 1)) := by
  let a := σ - outsideExponent
  let b := σ - windowExponent
  let f (u : ℝ) := F u * mellinGammaKernel σ k u
  have hU : 0 ≤ U := hL.trans hLU
  have hpoint (u : ℝ) (hu : 0 ≤ u) : ‖f u‖ ≤ B * mellinGammaKernel a k u := by
    calc
      _ = |F u| * mellinGammaKernel σ k u := by
        dsimp only [f]
        rw [norm_mul, Real.norm_eq_abs (F u), Real.norm_of_nonneg (mellinGammaKernel_nonneg σ k hu)]
      _ ≤ (B * Real.exp (outsideExponent * u)) * mellinGammaKernel σ k u :=
        mul_le_mul_of_nonneg_right (houtside u hu) (mellinGammaKernel_nonneg σ k hu)
      _ = _ := by rw [mul_assoc, exp_mul_mellinGammaKernel]
  have hf : MeasureTheory.IntegrableOn f (Set.Ici 0) := by
    have hfmeas : Measurable f := by
      dsimp [f, mellinGammaKernel]
      fun_prop
    exact ((mellinGammaKernel_integrable ha k).const_mul B).mono' hfmeas.aestronglyMeasurable
      ((MeasureTheory.ae_restrict_mem measurableSet_Ici).mono fun u hu => hpoint u hu)
  have htail {D : Set ℝ} (hD : MeasurableSet D) (hD₀ : D ⊆ Set.Ici 0) :
      (∫ u in D, f u) ≤ B * (∫ u in D, mellinGammaKernel a k u) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on (hf.mono_set hD₀)
      (((mellinGammaKernel_integrable ha k).mono_set hD₀).const_mul B) hD ?_
    intro u hu
    exact (le_abs_self (f u)).trans (by simpa only [Real.norm_eq_abs] using hpoint u (hD₀ hu))
  have hLeft₀ : Set.Icc 0 L ⊆ Set.Ici (0 : ℝ) := fun _ hu => hu.1
  have hRightSet₀ : Set.Ioi U ⊆ Set.Ici (0 : ℝ) := fun _ hu => hU.trans (Set.mem_Ioi.mp hu).le
  have hMiddle₀ : Set.Ioc L U ⊆ Set.Ici (0 : ℝ) := fun _ hu => hL.trans hu.1.le
  have hleft := (htail measurableSet_Icc hLeft₀).trans
    (mul_le_mul_of_nonneg_left (mellinGammaKernel_left_tail ha hLeft k) hB)
  have hright := (htail measurableSet_Ioi hRightSet₀).trans
    (mul_le_mul_of_nonneg_left (mellinGammaKernel_right_tail hRight₀ hRight hU k) hB)
  have hmiddle : (∫ u : ℝ in Set.Ioc L U, f u) ≤ C * (1 / b) ^ (k + 1) := by
    have hmid : (∫ u : ℝ in Set.Ioc L U, mellinGammaKernel b k u) ≤ (1 / b) ^ (k + 1) := by
      simpa only [Real.exp_zero, one_mul] using
        mellinGammaKernel_restrict_le (v := 0) hb hb k measurableSet_Ioc hMiddle₀
          (fun _ _ => by simp)
    calc
      _ ≤ ∫ u : ℝ in Set.Ioc L U, C * mellinGammaKernel b k u := by
        refine MeasureTheory.setIntegral_mono_on (hf.mono_set hMiddle₀)
          (((mellinGammaKernel_integrable hb k).mono_set hMiddle₀).const_mul C) measurableSet_Ioc ?_
        intro u hu
        calc
          f u ≤ (C * Real.exp (windowExponent * u)) * mellinGammaKernel σ k u :=
            mul_le_mul_of_nonneg_right (hwindow u ⟨hu.1.le, hu.2⟩)
              (mellinGammaKernel_nonneg σ k (hMiddle₀ hu))
          _ = _ := by rw [mul_assoc, exp_mul_mellinGammaKernel]
      _ = C * (∫ u : ℝ in Set.Ioc L U, mellinGammaKernel b k u) := MeasureTheory.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hmid hC
  have hd₁ : Disjoint (Set.Icc 0 L) (Set.Ioc L U) := Set.disjoint_left.mpr fun _ hu hv =>
    (not_lt_of_ge hu.2) hv.1
  have hd₂ : Disjoint (Set.Icc 0 U) (Set.Ioi U) := Set.disjoint_left.mpr fun _ hu hv =>
    (not_lt_of_ge hu.2) hv
  change (∫ u : ℝ in Set.Ici 0, f u) ≤ _
  rw [← Set.Icc_union_Ioi_eq_Ici hU,
    MeasureTheory.setIntegral_union hd₂ measurableSet_Ioi
      (hf.mono_set fun _ hu => hu.1) (hf.mono_set hRightSet₀),
    ← Set.Icc_union_Ioc_eq_Icc hL hLU,
    MeasureTheory.setIntegral_union hd₁ measurableSet_Ioc (hf.mono_set hLeft₀) (hf.mono_set hMiddle₀)]
  exact add_le_add (add_le_add hleft hmiddle) hright

/-- For a fixed window stretch and additive rate gap, large rates admit
cutoffs whose normalized tail exponents are strictly negative. -/
theorem exists_mellinGammaKernel_cutoffs {stretch width : ℝ} (hstretch : 1 < stretch)
    (hwidth : 0 < width) :
    ∃ amin : ℝ, 0 < amin ∧ ∀ a r : ℝ, amin ≤ a → a < r → r < a + width →
      ∃ bLeft bRight ξ₁ ξ₂ : ℝ, r < bLeft ∧ 0 < bRight ∧ bRight < a ∧
        0 < ξ₁ ∧ ξ₁ < ξ₂ ∧
        bLeft - a + ξ₁ * Real.log (r / bLeft) < 0 ∧
        (bRight - a) * stretch + ξ₂ * Real.log (r / bRight) < 0 := by
  have hSqrt : 1 < Real.sqrt stretch := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) hstretch
  obtain ⟨t, ht, htSqrt⟩ := exists_between hSqrt
  have ht₀ : 0 < t := zero_lt_one.trans ht
  have hstretch₀ : 0 ≤ stretch := zero_le_one.trans hstretch.le
  have htStretch : t < stretch / t := by
    apply (lt_div_iff₀ ht₀).mpr
    have hsq := (sq_lt_sq₀ ht₀.le (Real.sqrt_nonneg stretch)).mpr htSqrt
    rwa [Real.sq_sqrt hstretch₀, pow_two] at hsq
  obtain ⟨u, htu, huStretch⟩ := exists_between htStretch
  obtain ⟨v, huv, hvStretch⟩ := exists_between huStretch
  have hu₀ : 0 < u := ht₀.trans htu
  have hv₀ : 0 < v := hu₀.trans huv
  let left (x : ℝ) := t - 1 + u * Real.log (x / t)
  let right (x : ℝ) := (1 / t - 1) * stretch + v * Real.log (x * t)
  have hleft : left 1 < 0 := by
    change t - 1 + u * Real.log (1 / t) < 0
    have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr ht₀)
    calc
      _ ≤ t - 1 + u * (1 / t - 1) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hu₀.le)
      _ = (1 - u / t) * (t - 1) := by
        field_simp [ht₀.ne']
        ring
      _ < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr ((lt_div_iff₀ ht₀).mpr (by simpa using htu)))
        (sub_pos.mpr ht)
  have hright : right 1 < 0 := by
    change (1 / t - 1) * stretch + v * Real.log (1 * t) < 0
    rw [one_mul]
    have hlog := Real.log_le_sub_one_of_pos ht₀
    calc
      _ ≤ (1 / t - 1) * stretch + v * (t - 1) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hv₀.le)
      _ = (v - stretch / t) * (t - 1) := by
        field_simp [ht₀.ne']
        ring
      _ < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hvStretch) (sub_pos.mpr ht)
  have hleftCont : ContinuousAt left (1 : ℝ) := by
    dsimp only [left]
    fun_prop (disch := first | exact ht₀.ne' | exact div_ne_zero one_ne_zero ht₀.ne')
  have hrightCont : ContinuousAt right (1 : ℝ) := by
    dsimp only [right]
    fun_prop (disch := first | exact ht₀.ne' | exact mul_ne_zero one_ne_zero ht₀.ne')
  have hnear : {x : ℝ | left x < 0 ∧ right x < 0 ∧ x < t} ∈ 𝓝 (1 : ℝ) := by
    filter_upwards [hleftCont.eventually_lt continuousAt_const hleft,
      hrightCont.eventually_lt continuousAt_const hright, Iio_mem_nhds ht] with x hxl hxr hxt
    exact ⟨hxl, hxr, hxt⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨width / ε, div_pos hwidth hε, ?_⟩
  intro a r haMin har hr
  have ha : 0 < a := (div_pos hwidth hε).trans_le haMin
  have hrLower : 1 < r / a := (lt_div_iff₀ ha).mpr (by simpa only [one_mul] using har)
  have hrUpper : r / a < 1 + ε := by
    apply (div_lt_iff₀ ha).mpr
    have hwidth' := (div_le_iff₀ hε).mp haMin
    rw [add_mul, one_mul, mul_comm ε a]
    linarith
  have hratio : r / a ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hrLower.le)]
    linarith
  have ⟨hrl, hrr, hrt⟩ := hball hratio
  have hLeftCutoff : r < t * a := (div_lt_iff₀ ha).mp hrt
  have hRightCutoff : a / t < a := div_lt_self ha ht
  refine ⟨t * a, a / t, u * a, v * a, hLeftCutoff, div_pos ha ht₀, hRightCutoff,
    mul_pos hu₀ ha, mul_lt_mul_of_pos_right huv ha, ?_, ?_⟩
  · have hdiv : r / (t * a) = (r / a) / t := by field_simp [ha.ne', ht₀.ne']
    calc
      t * a - a + u * a * Real.log (r / (t * a)) = a * left (r / a) := by
        dsimp only [left]
        rw [hdiv]
        ring
      _ < 0 := mul_neg_of_pos_of_neg ha hrl
  · have hdiv : r / (a / t) = (r / a) * t := by field_simp [ha.ne', ht₀.ne']
    calc
      (a / t - a) * stretch + v * a * Real.log (r / (a / t)) = a * right (r / a) := by
        dsimp only [right]
        rw [hdiv]
        ring
      _ < 0 := mul_neg_of_pos_of_neg ha hrr

end Utilities
