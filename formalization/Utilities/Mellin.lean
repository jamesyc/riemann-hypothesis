module

public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

open Asymptotics Filter MeasureTheory
open scoped Topology

namespace Utilities

private theorem cutoffOne_mellinKernel (f : ℝ → ℂ) (s : ℂ) :
    (fun x : ℝ => (x : ℂ) ^ (s - 1) • (Set.Ici (1 : ℝ)).indicator f x) =
      (Set.Ici (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x) := by
  funext x
  by_cases hx : x ∈ Set.Ici (1 : ℝ) <;> simp [Set.indicator, hx, smul_eq_mul]

theorem mellin_cutoffOne_eq_setIntegral (f : ℝ → ℂ) (s : ℂ) :
    mellin ((Set.Ici (1 : ℝ)).indicator f) s =
      ∫ x : ℝ in Set.Ici 1, (x : ℂ) ^ (s - 1) * f x := by
  have hsubset : Set.Ici (1 : ℝ) ⊆ Set.Ioi 0 := fun _ hx => zero_lt_one.trans_le hx
  rw [mellin, cutoffOne_mellinKernel, setIntegral_indicator measurableSet_Ici,
    Set.inter_eq_right.mpr hsubset]

theorem hasMellin_cutoffOne_iff (f : ℝ → ℂ) (s w : ℂ) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator f) s w ↔
      IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x) (Set.Ici 1) ∧
      (∫ x : ℝ in Set.Ici 1, (x : ℂ) ^ (s - 1) * f x) = w := by
  have hsubset : Set.Ici (1 : ℝ) ⊆ Set.Ioi 0 := fun _ hx => zero_lt_one.trans_le hx
  unfold HasMellin MellinConvergent
  rw [cutoffOne_mellinKernel, integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet,
    Set.inter_eq_left.mpr hsubset, mellin_cutoffOne_eq_setIntegral]

/-- On changing variables by `x = exp u`, the negative Mellin parameter becomes
the parameter of a Laplace integral on the nonnegative axis. -/
theorem mellin_cutoffOne_eq_laplace (f : ℝ → ℂ) (s : ℂ) :
    mellin ((Set.Ici (1 : ℝ)).indicator f) (-s) =
      ∫ u : ℝ in Set.Ici 0, Complex.exp (-s * (u : ℂ)) * f (Real.exp u) := by
  have himage : Real.exp '' Set.Ici (0 : ℝ) = Set.Ici 1 := by
    rw [Real.image_exp_Ici, Real.exp_zero]
  rw [mellin_cutoffOne_eq_setIntegral, ← himage,
    integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ici
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
      (Real.exp_strictMono.monotone.monotoneOn _)]
  apply setIntegral_congr_fun measurableSet_Ici
  intro u _
  dsimp only
  have hexp : 0 < Real.exp u := Real.exp_pos _
  have hnonzero : (Real.exp u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hexp.ne'
  have hpower : (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (-s - 1) = Complex.exp (-s * (u : ℂ)) := by
    calc
      _ = (Real.exp u : ℂ) ^ (1 : ℂ) * (Real.exp u : ℂ) ^ (-s - 1) := by rw [Complex.cpow_one]
      _ = (Real.exp u : ℂ) ^ (-s) := by
        rw [← Complex.cpow_add _ _ hnonzero, show 1 + (-s - 1) = -s by ring]
      _ = _ := by
        rw [Complex.cpow_def_of_ne_zero hnonzero, ← Complex.ofReal_log hexp.le, Real.log_exp, mul_comm]
  rw [Complex.real_smul, ← mul_assoc, hpower]

theorem cutoffLinear_hasMellin {s : ℂ} (hs : 1 < s.re) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator fun x => (x : ℂ)) (-s) (1 / (s - 1)) := by
  rw [hasMellin_cutoffOne_iff]
  have hp : (-s).re < -1 := by
    rw [Complex.neg_re]
    linarith
  have hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Set.Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_cpow_of_lt hp zero_lt_one
  have hkernel : Set.EqOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (x : ℂ))
      (fun x : ℝ => (x : ℂ) ^ (-s)) (Set.Ici 1) := by
    intro x hx
    have hx₀ : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hx).ne'
    change (x : ℂ) ^ (-s - 1) * (x : ℂ) = (x : ℂ) ^ (-s)
    calc
      _ = (x : ℂ) ^ (-s - 1) * (x : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = _ := by rw [← Complex.cpow_add _ _ hx₀, sub_add_cancel]
  refine ⟨hi.congr_fun (fun x hx => (hkernel hx).symm) measurableSet_Ici, ?_⟩
  calc
    _ = ∫ x : ℝ in Set.Ici 1, (x : ℂ) ^ (-s) :=
      setIntegral_congr_fun measurableSet_Ici hkernel
    _ = _ := by
      rw [integral_Ici_eq_integral_Ioi, integral_Ioi_cpow_of_lt hp zero_lt_one]
      rw [show -s + 1 = -(s - 1) by ring]
      simp only [Complex.ofReal_one, Complex.one_cpow, neg_div_neg_eq]

theorem cutoffLinearLog_hasMellin {s : ℂ} (hs : 1 < s.re) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator fun x => (x : ℂ) * (Real.log x : ℂ))
      (-s) (1 / (s - 1) ^ (2 : ℕ)) := by
  let f := (Set.Ici (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ))
  have hp : (-s).re < -1 := by rw [Complex.neg_re]; linarith
  have hlocal : LocallyIntegrableOn f (Set.Ioi 0) := by
    have hbase : LocallyIntegrable (fun x : ℝ => (x : ℂ)) := Complex.continuous_ofReal.locallyIntegrable
    exact (hbase.indicator (show MeasurableSet (Set.Ici (1 : ℝ)) from measurableSet_Ici)).locallyIntegrableOn _
  have htop : f =O[atTop] (fun x : ℝ => x ^ (-(-1 : ℝ))) := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp [f, Set.indicator_of_mem (show x ∈ Set.Ici (1 : ℝ) from hx), Complex.norm_real]
  have hbot : f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-((-s).re - 1))) := by
    apply IsBigO.of_bound 0
    have hsmall : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hsmall] with x hx
    have hx' : x ∉ Set.Ici (1 : ℝ) := not_le.mpr hx
    simp [f, hx']
  obtain ⟨hconv, hderiv⟩ := mellin_hasDerivAt_of_isBigO_rpow (s := -s) hlocal htop hp hbot
    (show (-s).re - 1 < (-s).re by linarith)
  have hformula : mellin f =ᶠ[𝓝 (-s)] (fun z : ℂ => -(z + 1)⁻¹) := by
    filter_upwards [(Complex.isOpen_re_lt (-1)).mem_nhds hp] with z hz
    have hz' : 1 < (-z).re := by
      change z.re < -1 at hz
      rw [Complex.neg_re]
      linarith
    have h := (cutoffLinear_hasMellin hz').2
    simpa only [f, neg_neg, one_div, show -z - 1 = -(z + 1) by ring, inv_neg] using h
  have hnonzero : -s + 1 ≠ (0 : ℂ) := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hrational : HasDerivAt (fun z : ℂ => -(z + 1)⁻¹) (1 / (s - 1) ^ (2 : ℕ)) (-s) := by
    have hd := (((hasDerivAt_id (-s)).add_const 1).inv hnonzero).neg
    refine hd.congr_deriv ?_
    change -(-1 / (-s + 1) ^ (2 : ℕ)) = 1 / (s - 1) ^ (2 : ℕ)
    rw [show -s + 1 = -(s - 1) by ring, neg_sq, ← neg_div, neg_neg]
  have hvalue := hderiv.unique (hrational.congr_of_eventuallyEq hformula)
  have hlog : (fun x : ℝ => Real.log x • f x) =
      (Set.Ici (1 : ℝ)).indicator (fun x => (x : ℂ) * (Real.log x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Ici (1 : ℝ) <;> simp [f, hx, Complex.real_smul, mul_comm]
  rw [← hlog]
  exact ⟨hconv, hvalue⟩

private theorem smoothedLinearKernel_eq {x c : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x : ℂ) / (c : ℂ) - 1) * (x : ℂ) ^ (-s - 1) =
      (x : ℂ) ^ (-s) / (c : ℂ) - (x : ℂ) ^ (-s - 1) := by
  have hx₀ : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow : (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
    calc
      _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-s - 1) := by rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_add _ _ hx₀]
        congr 1
        ring
  rw [sub_mul, one_mul, div_mul_eq_mul_div, hpow]

theorem integrableOn_smoothedLinearKernel {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => ((x : ℂ) / (c : ℂ) - 1) * (x : ℂ) ^ (-s - 1)) (Set.Ioi c) := by
  have h₁ : (-s).re < -1 := by rw [Complex.neg_re]; linarith
  have h₂ : (-s - 1).re < -1 := by simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith
  have h : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s) / (c : ℂ) - (x : ℂ) ^ (-s - 1))
      (Set.Ioi c) := ((integrableOn_Ioi_cpow_of_lt h₁ hc).div_const (c : ℂ)).sub
    (integrableOn_Ioi_cpow_of_lt h₂ hc)
  exact h.congr_fun (fun x hx => (smoothedLinearKernel_eq (hc.trans hx) s).symm) measurableSet_Ioi

/-- The Mellin integral of a linear cutoff at a positive threshold. -/
theorem integral_smoothedLinearKernel {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
    (∫ x : ℝ in Set.Ioi c, ((x : ℂ) / (c : ℂ) - 1) * (x : ℂ) ^ (-s - 1)) =
      (c : ℂ) ^ (-s) / (s * (s - 1)) := by
  have h₁ : (-s).re < -1 := by
    rw [Complex.neg_re]
    linarith
  have h₂ : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hs₀ : s ≠ 0 := by
    intro h
    simp [h] at hs
    linarith
  have hs₁ : s - 1 ≠ 0 := by
    intro h
    have heq : s = 1 := sub_eq_zero.mp h
    simp [heq] at hs
  calc
    _ = ∫ x : ℝ in Set.Ioi c, (x : ℂ) ^ (-s) / (c : ℂ) - (x : ℂ) ^ (-s - 1) := by
      exact setIntegral_congr_fun measurableSet_Ioi fun x hx => smoothedLinearKernel_eq (hc.trans hx) s
    _ = _ := by
      rw [integral_sub ((integrableOn_Ioi_cpow_of_lt h₁ hc).div_const (c : ℂ))
        (integrableOn_Ioi_cpow_of_lt h₂ hc), integral_div,
        integral_Ioi_cpow_of_lt h₁ hc, integral_Ioi_cpow_of_lt h₂ hc]
      rw [show -s - 1 + 1 = -s by ring, Complex.cpow_add (-s) 1 hc₀, Complex.cpow_one]
      have hs₁' : -s + 1 ≠ 0 := by
        rw [show -s + 1 = -(s - 1) by ring]
        exact neg_ne_zero.mpr hs₁
      field_simp
      ring

/-- An absolute majorant of one term with the same decay in the cutoff scale. -/
theorem integral_norm_smoothedLinearKernel_le {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
    (∫ x : ℝ in Set.Ioi c, ‖((x : ℂ) / (c : ℂ) - 1) * (x : ℂ) ^ (-s - 1)‖) ≤
      c ^ (-s.re) / (s.re - 1) := by
  have hr : -s.re < -1 := by linarith
  have hmajor := (integrableOn_Ioi_rpow_of_lt hr hc).const_mul (1 / c)
  calc
    _ ≤ ∫ x : ℝ in Set.Ioi c, (1 / c) * x ^ (-s.re) := by
      apply setIntegral_mono_on (integrableOn_smoothedLinearKernel hc hs).norm hmajor measurableSet_Ioi
      intro x hx
      have hx₀ : 0 < x := hc.trans hx
      have hcutoff : 0 ≤ x / c - 1 := sub_nonneg.mpr ((le_div_iff₀ hc).mpr (by simpa using hx.le))
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx₀,
        Complex.sub_re, Complex.neg_re, Complex.one_re,
        ← Complex.ofReal_div, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcutoff]
      calc
        _ ≤ (x / c) * x ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) (Real.rpow_nonneg hx₀.le _)
        _ = (1 / c) * (x ^ (1 : ℝ) * x ^ (-s.re - 1)) := by rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add hx₀, show 1 + (-s.re - 1) = -s.re by ring]
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hr hc, Real.rpow_add hc, Real.rpow_one,
        show -s.re + 1 = -(s.re - 1) by ring, neg_div_neg_eq]
      field_simp [hc.ne', (sub_pos.mpr hs).ne']

end Utilities
