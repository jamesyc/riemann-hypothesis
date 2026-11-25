module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Meromorphic.Order
public import Utilities.GammaKernel
public import Utilities.Laplace
public import Utilities.PrincipalPart
public import Utilities.TaylorBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Utilities.Mellin
import Utilities.MeromorphicReflection
import Utilities.NearestComplexPair
import Utilities.RotationBounds

@[expose] public section

open Filter MeasureTheory Utilities
open scoped ComplexConjugate Topology

namespace Riemann

/-- A one-sided bound with a fixed constant on windows starting arbitrarily far out. -/
def HasWindowUpperBound (H : ℝ → ℝ) (stretch exponent : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ lower : ℝ, ∃ Y : ℝ, max 1 lower ≤ Y ∧
    ∀ x ∈ Set.Icc Y (Y ^ stretch), H x ≤ C * x ^ exponent

theorem HasWindowUpperBound.mono_exponent {H : ℝ → ℝ} {stretch a b : ℝ}
    (hbound : HasWindowUpperBound H stretch a) (hab : a ≤ b) :
    HasWindowUpperBound H stretch b := by
  obtain ⟨C, hC, hwindows⟩ := hbound
  refine ⟨C, hC, fun lower => ?_⟩
  obtain ⟨Y, hY, hboundY⟩ := hwindows lower
  refine ⟨Y, hY, fun x hx => ?_⟩
  have hx₁ : 1 ≤ x := (le_max_left 1 lower).trans (hY.trans hx.1)
  exact (hboundY x hx).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx₁ hab) hC.le)

/-- Cofinal windows become cofinal intervals with linearly scaled endpoints under `log`. -/
theorem HasWindowUpperBound.logarithmic {H : ℝ → ℝ} {stretch exponent : ℝ}
    (hbound : HasWindowUpperBound H stretch exponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ lower : ℝ, ∃ L : ℝ, max 0 lower ≤ L ∧
      ∀ u ∈ Set.Icc L (stretch * L), H (Real.exp u) ≤ C * Real.exp (exponent * u) := by
  obtain ⟨C, hC, hwindows⟩ := hbound
  refine ⟨C, hC, fun lower => ?_⟩
  obtain ⟨Y, hY, hwindow⟩ := hwindows (Real.exp lower)
  have hY₁ : 1 ≤ Y := (le_max_left _ _).trans hY
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY₁
  let L := Real.log Y
  have hL₀ : 0 ≤ L := Real.log_nonneg hY₁
  have hL : lower ≤ L := by
    have hlog := Real.log_le_log (Real.exp_pos lower) ((le_max_right _ _).trans hY)
    simpa only [Real.log_exp] using hlog
  refine ⟨L, max_le hL₀ hL, ?_⟩
  intro u hu
  have hleft : Y ≤ Real.exp u := by
    rw [← Real.exp_log hY₀]
    exact Real.exp_le_exp.mpr hu.1
  have hright : Real.exp u ≤ Y ^ stretch := by
    rw [Real.rpow_def_of_pos hY₀, mul_comm (Real.log Y) stretch]
    exact Real.exp_le_exp.mpr hu.2
  have hval := hwindow (Real.exp u) ⟨hleft, hright⟩
  simpa only [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_comm u exponent] using hval

/-- Mellin data for the window theorem, using Mathlib's Mellin transform at `-s`.
An arbitrarily small loss in the linear growth exponent suffices. -/
structure WindowMellinData (H : ℝ → ℝ) (A : ℂ → ℂ) : Prop where
  measurable : Measurable H
  powerGrowth : ∀ a : ℝ, 1 < a → ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, |H x| ≤ B * x ^ a
  meromorphic : Meromorphic A
  hasMellin : ∀ s : ℂ, 1 < s.re →
    HasMellin ((Set.Ici (1 : ℝ)).indicator fun x => (H x : ℂ)) (-s) (A s)

theorem WindowMellinData.of_linearGrowth {H : ℝ → ℝ} {A : ℂ → ℂ}
    (hMeasurable : Measurable H) (hGrowth : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, |H x| ≤ B * x)
    (hMeromorphic : Meromorphic A)
    (hMellin : ∀ s : ℂ, 1 < s.re →
      HasMellin ((Set.Ici (1 : ℝ)).indicator fun x => (H x : ℂ)) (-s) (A s)) :
    WindowMellinData H A := by
  obtain ⟨B, hB, hGrowth⟩ := hGrowth
  refine ⟨hMeasurable, fun a ha => ⟨B, hB, fun x hx => ?_⟩, hMeromorphic, hMellin⟩
  have hxPower : x ≤ x ^ a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx ha.le
  exact (hGrowth x hx).trans (mul_le_mul_of_nonneg_left hxPower hB)

theorem WindowMellinData.eq_laplace {H : ℝ → ℝ} {A : ℂ → ℂ}
    (h : WindowMellinData H A) {z : ℂ} (hz : 1 < z.re) :
    A z = laplaceMoment (fun u => (H (Real.exp u) : ℂ)) 0 z := by
  simpa only [mellin_cutoffOne_eq_laplace, laplaceMoment, pow_zero, one_mul] using (h.hasMellin z hz).2.symm

private theorem WindowMellinData.laplace_growth {H : ℝ → ℝ} {A : ℂ → ℂ}
    (h : WindowMellinData H A) {a : ℝ} (ha : 1 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u ≥ 0, ‖(H (Real.exp u) : ℂ)‖ ≤ B * Real.exp (a * u) := by
  obtain ⟨B, hB, hGrowth⟩ := h.powerGrowth a ha
  refine ⟨B, hB, fun u hu => ?_⟩
  have hu' : 1 ≤ Real.exp u := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hu
  simpa only [Complex.norm_real, Real.norm_eq_abs, Real.rpow_def_of_pos (Real.exp_pos u),
    Real.log_exp, mul_comm u a] using hGrowth (Real.exp u) hu'

theorem WindowMellinData.analyticAt_of_one_lt_re {H : ℝ → ℝ} {A : ℂ → ℂ}
    (h : WindowMellinData H A) {z : ℂ} (hz : 1 < z.re) : AnalyticAt ℂ A z := by
  let g (u : ℝ) : ℂ := (H (Real.exp u) : ℂ)
  have hg : Measurable g := Complex.continuous_ofReal.measurable.comp
    (h.measurable.comp Real.continuous_exp.measurable)
  obtain ⟨a, ha, haz⟩ := exists_between hz
  obtain ⟨B, hB, hGrowth⟩ := h.laplace_growth ha
  have heq : A =ᶠ[𝓝 z] laplaceMoment g 0 := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hz] with w hw using h.eq_laplace hw
  have hanalytic : AnalyticAt ℂ (laplaceMoment g 0) z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [(Complex.isOpen_re_gt a).mem_nhds haz] with w hw
    exact (hasDerivAt_laplaceMoment hg hB hGrowth 0 hw).differentiableAt
  exact hanalytic.congr heq.symm

/-- The Mellin transform of a real input has conjugate-symmetric punctured germs
throughout its meromorphic continuation. -/
theorem WindowMellinData.conj_symmetry_nhdsNE {H : ℝ → ℝ} {A : ℂ → ℂ}
    (h : WindowMellinData H A) (ρ : ℂ) : A =ᶠ[𝓝[≠] ρ] (conj ∘ A ∘ conj) := by
  apply meromorphic_eventuallyEq_nhdsNE_of_eq_nhds h.meromorphic (meromorphic_conj_conj h.meromorphic) (x := (2 : ℂ))
  filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : 1 < (2 : ℂ).re)] with z hz
  have hzc : 1 < (conj z).re := by simpa only [Complex.conj_re] using hz
  change A z = conj (A (conj z))
  rw [h.eq_laplace hz, h.eq_laplace hzc]
  simp only [laplaceMoment, pow_zero, one_mul]
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ici
  intro u _
  dsimp only
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal]

theorem WindowMellinData.orderAt_conj {H : ℝ → ℝ} {A : ℂ → ℂ}
    (h : WindowMellinData H A) (ρ : ℂ) : meromorphicOrderAt A (conj ρ) = meromorphicOrderAt A ρ :=
  (meromorphicOrderAt_congr (h.conj_symmetry_nhdsNE (conj ρ))).trans
    (meromorphicAt_conj_conj_and_order (h.meromorphic ρ)).2

theorem WindowMellinData.hasPrincipalPart_conj {H : ℝ → ℝ} {A : ℂ → ℂ}
    (h : WindowMellinData H A) {ρ residue : ℂ} (hpart : HasPrincipalPart A ρ residue) :
    HasPrincipalPart A (conj ρ) (conj residue) :=
  (hasPrincipalPart_conj_conj hpart).congr_eventuallyEq (h.conj_symmetry_nhdsNE (conj ρ))

private theorem WindowMellinData.exists_nearest_pole_pair {H : ℝ → ℝ} {A : ℂ → ℂ}
    (h : WindowMellinData H A) {exponent : ℝ}
    (hupper : ∀ z : ℂ, exponent < z.re → meromorphicOrderAt A z < 0 → z.re < 1)
    {p : ℂ} (hp : exponent < p.re) (hpole : meromorphicOrderAt A p < 0)
    (σmin : ℝ) (hσmin : 1 < σmin) :
    ∃ (σ r R : ℝ) (q : ℂ), σmin ≤ σ ∧ σ - 1 < r ∧ r < R ∧ R < σ - exponent ∧
      meromorphicOrderAt A q < 0 ∧ 0 ≤ q.im ∧ dist (σ : ℂ) q = r ∧
        ∀ z : ℂ, meromorphicOrderAt A z < 0 → dist (σ : ℂ) z ≤ R → z = q ∨ z = conj q := by
  exact exists_isolated_nearest_conj_pair {z | meromorphicOrderAt A z < 0}
    (fun R => finite_poles_inter_isCompact h.meromorphic (isCompact_closedBall (0 : ℂ) R))
    (fun z hz => by simpa only [Set.mem_ofPred_eq, h.orderAt_conj z] using hz)
    (fun z hz hRe => hupper z hRe hz) hpole hp σmin hσmin

/-- The real Taylor moment on the logarithmic scale, normalized by the nearest-pole radius. -/
noncomputable def normalizedMellinMoment (H : ℝ → ℝ) (σ r : ℝ) (k : ℕ) : ℝ :=
  r ^ (k + 1) * ∫ u : ℝ in Set.Ici 0,
    H (Real.exp u) * mellinGammaKernel σ k u

noncomputable def normalizedMellinTaylor (A : ℂ → ℂ) (σ r : ℝ) (k : ℕ) : ℝ :=
  r ^ (k + 1) * (signedTaylorCoefficient A (σ : ℂ) k).re

/-- The two descriptions of the Taylor coefficient in step 3 of Theorem 2.4. -/
theorem normalizedMellinMoment_eq_taylor {H : ℝ → ℝ} {A : ℂ → ℂ}
    (hMellin : WindowMellinData H A) {σ : ℝ} (hσ : 1 < σ) (r : ℝ) (k : ℕ) :
    normalizedMellinMoment H σ r k = normalizedMellinTaylor A σ r k := by
  let g (u : ℝ) : ℂ := (H (Real.exp u) : ℂ)
  have hg : Measurable g := Complex.continuous_ofReal.measurable.comp
    (hMellin.measurable.comp Real.continuous_exp.measurable)
  obtain ⟨a, ha, haσ⟩ := exists_between hσ
  obtain ⟨B, hB, hExpGrowth⟩ := hMellin.laplace_growth ha
  have hσ' : 1 < (σ : ℂ).re := by simpa only [Complex.ofReal_re] using hσ
  have haσ' : a < (σ : ℂ).re := by simpa only [Complex.ofReal_re] using haσ
  have heq : A =ᶠ[𝓝 (σ : ℂ)] laplaceMoment g 0 := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hσ'] with z hz using hMellin.eq_laplace hz
  have hderiv : iteratedDeriv k A (σ : ℂ) = laplaceMoment g k (σ : ℂ) :=
    (heq.iteratedDeriv_eq k).trans (iteratedDeriv_laplace_eq_moment hg hB hExpGrowth k haσ')
  have hmoment : (-1 : ℂ) ^ k * laplaceMoment g k (σ : ℂ) / (k.factorial : ℂ) =
      ((∫ u : ℝ in Set.Ici 0, H (Real.exp u) * mellinGammaKernel σ k u : ℝ) : ℂ) := by
    unfold laplaceMoment
    rw [← integral_const_mul, ← integral_div, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ici
    intro u _
    have hsign : (-1 : ℂ) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by
      rw [← mul_pow, neg_one_mul, neg_neg]
    have hexp : Complex.exp (-(σ : ℂ) * (u : ℂ)) = (Real.exp (-(σ * u)) : ℂ) := by
      rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, neg_mul]
    calc
      _ = (((-1 : ℂ) ^ k * (-(u : ℂ)) ^ k) * Complex.exp (-(σ : ℂ) * (u : ℂ))) *
          g u / (k.factorial : ℂ) := by ring
      _ = _ := by
        rw [hsign, hexp]
        simp only [g, mellinGammaKernel, Complex.ofReal_mul, Complex.ofReal_div,
          Complex.ofReal_pow, Complex.ofReal_natCast]
        ring
  unfold normalizedMellinMoment normalizedMellinTaylor signedTaylorCoefficient
  rw [hderiv, hmoment, Complex.ofReal_re]

/-- Steps 2–3 of Theorem 2.4. Poles give large Taylor coefficients with bounded gaps. -/
theorem normalizedMellinTaylor_frequently_ge_of_pole {H : ℝ → ℝ} {A : ℂ → ℂ}
    (hMellin : WindowMellinData H A) {exponent : ℝ}
    (hpoles : ∀ ρ : ℂ, exponent < ρ.re → meromorphicOrderAt A ρ < 0 →
      ρ.re < 1 ∧ ∃ residue : ℂ, HasSimplePoleWithResidue A ρ residue ∧
        (ρ.im = 0 → 0 < residue.re))
    {p : ℂ} (hp : exponent < p.re) (horder : meromorphicOrderAt A p < 0)
    (σmin : ℝ) (hσmin : 1 < σmin) :
    ∃ (σ r c : ℝ) (gap : ℕ), σmin ≤ σ ∧ σ - 1 < r ∧ r < σ - exponent ∧ 0 < c ∧
      ∀ start : ℕ, ∃ k ∈ Set.Icc start (start + gap), c ≤ normalizedMellinTaylor A σ r k := by
  classical
  obtain ⟨σ, r, R, q, hσ, hrLower, hrR, hR, hqPole, hqIm, hqDist, hcover⟩ :=
    hMellin.exists_nearest_pole_pair (fun z hRe hPole => (hpoles z hRe hPole).1) hp horder σmin hσmin
  have hσ₁ : 1 < σ := hσmin.trans_le hσ
  have hr : 0 < r := (sub_pos.mpr hσ₁).trans hrLower
  have hrUpper : r < σ - exponent := hrR.trans hR
  have hrealBound : σ - q.re ≤ r := by
    rw [← hqDist, dist_eq_norm]
    simpa only [Complex.sub_re, Complex.ofReal_re] using Complex.re_le_norm ((σ : ℂ) - q)
  have hqRe : exponent < q.re := by linarith
  obtain ⟨hqUpper, residue, hqResidue, hqReal⟩ := hpoles q hqRe hqPole
  let poles : Finset ℂ := {q, conj q}
  let coeff (p : ℂ) := if p = q then residue else conj residue
  have hparts (p : ℂ) (hp : p ∈ poles) : HasPrincipalPart A p (coeff p) := by
    have hp' : p = q ∨ p = conj q := by simpa only [poles, Finset.mem_insert, Finset.mem_singleton] using hp
    rcases hp' with rfl | rfl
    · simpa only [coeff, ite_eq_left rfl] using hqResidue.2
    · by_cases heq : conj q = q
      · simpa only [coeff, heq, ite_eq_left rfl] using hqResidue.2
      · simpa only [coeff, ite_eq_right heq] using hMellin.hasPrincipalPart_conj hqResidue.2
  let U := Metric.closedBall (σ : ℂ) R
  have hcover' (p : ℂ) (hp : p ∈ U) (hpPole : meromorphicOrderAt A p < 0) : p ∈ poles := by
    have hd : dist (σ : ℂ) p ≤ R := by simpa only [U, Metric.mem_closedBall, dist_comm] using hp
    simpa only [poles, Finset.mem_insert, Finset.mem_singleton] using hcover p hpPole hd
  obtain ⟨Q, hQ, _, hlocal⟩ := exists_analytic_remainder_after_subtracting_principalParts
    (fun p _ => hMellin.meromorphic p) poles coeff hparts hcover'
  have hcenter : (σ : ℂ) ∈ U := Metric.mem_closedBall_self (hr.trans hrR).le
  have hqConjDist : dist (σ : ℂ) (conj q) = r := by
    rw [← Complex.dist_conj_comm, Complex.conj_ofReal, hqDist]
  have hcenter₀ : (σ : ℂ) ∉ poles := by
    intro hcenterPole
    have hor : (σ : ℂ) = q ∨ (σ : ℂ) = conj q := by
      simpa only [poles, Finset.mem_insert, Finset.mem_singleton] using hcenterPole
    rcases hor with heq | heq
    · rw [← heq, dist_self] at hqDist
      exact hr.ne' hqDist.symm
    · rw [← heq, dist_self] at hqConjDist
      exact hr.ne' hqConjDist.symm
  have hAσ : AnalyticAt ℂ A (σ : ℂ) := hMellin.analyticAt_of_one_lt_re (by simpa using hσ₁)
  have hremainder := hlocal (σ : ℂ) hcenter hAσ hcenter₀
  let singular (z : ℂ) := ∑ p ∈ poles, coeff p / (z - p)
  have hsingular : AnalyticAt ℂ singular (σ : ℂ) := by
    refine Finset.analyticAt_fun_sum poles fun p hp => ?_
    have hne : (σ : ℂ) ≠ p := fun heq => hcenter₀ (heq.symm ▸ hp)
    fun_prop (disch := exact sub_ne_zero.mpr hne)
  have hsum : A =ᶠ[𝓝 (σ : ℂ)] fun z => singular z + Q z := by
    filter_upwards [hremainder] with z hz
    change Q z = A z - singular z at hz
    rw [hz]
    ring
  have hcoeff (k : ℕ) : signedTaylorCoefficient A (σ : ℂ) k =
      signedTaylorCoefficient singular (σ : ℂ) k + signedTaylorCoefficient Q (σ : ℂ) k :=
    (signedTaylorCoefficient_congr_eventuallyEq hsum k).trans
      (signedTaylorCoefficient_add hsingular (hQ (σ : ℂ) hcenter) k)
  let main (k : ℕ) := r ^ (k + 1) * (signedTaylorCoefficient singular (σ : ℂ) k).re
  let error (k : ℕ) := r ^ (k + 1) * (signedTaylorCoefficient Q (σ : ℂ) k).re
  have hdecay : Tendsto error atTop (𝓝 0) := tendsto_scaled_signedTaylorCoefficient_re hr hrR hQ
  have hdecomp (k : ℕ) : normalizedMellinTaylor A σ r k = main k + error k := by
    simp only [normalizedMellinTaylor, hcoeff, Complex.add_re, mul_add, main, error]
  have hreScale (z : ℂ) (k : ℕ) : ((r : ℂ) ^ (k + 1) * z).re = r ^ (k + 1) * z.re := by
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hscale (z d : ℂ) (k : ℕ) : (r : ℂ) ^ (k + 1) * (z / d ^ (k + 1)) =
      z * ((r : ℂ) / d) ^ (k + 1) := by
    rw [div_pow]
    ring
  have hmain : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ gap : ℕ,
      ∀ start : ℕ, ∃ k ∈ Set.Icc start (start + gap), c₀ ≤ main k := by
    by_cases him : q.im = 0
    · have hconj : conj q = q := Complex.conj_eq_iff_im.mpr him
      have hsing : singular = fun z => residue / (z - q) := by
        funext z
        simp [singular, poles, hconj, coeff]
      have hpos : 0 < σ - q.re := sub_pos.mpr (hqUpper.trans hσ₁)
      have hd : (σ : ℂ) - q = ((σ - q.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp only [Complex.sub_re, Complex.ofReal_re]
        · simp only [Complex.sub_im, Complex.ofReal_im, him, sub_zero]
      have hrEq : r = σ - q.re := by
        rw [← hqDist, dist_eq_norm, hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      have hden : (σ : ℂ) - q = (r : ℂ) := by rw [hd, hrEq]
      refine ⟨residue.re, hqReal him, 0, fun start => ⟨start, by simp, ?_⟩⟩
      change residue.re ≤ r ^ (start + 1) * (signedTaylorCoefficient singular (σ : ℂ) start).re
      rw [← hreScale, hsing, signedTaylorCoefficient_simplePole, hscale, hden,
        div_self (Complex.ofReal_ne_zero.mpr hr.ne'), one_pow, mul_one]
    · have hqImPos : 0 < q.im := lt_of_le_of_ne hqIm (Ne.symm him)
      have hconj : conj q ≠ q := fun heq => him (Complex.conj_eq_iff_im.mp heq)
      have hsing : singular = fun z => residue / (z - q) + conj residue / (z - conj q) := by
        funext z
        simp [singular, poles, coeff, hconj, Ne.symm hconj]
      have hq₀ : (σ : ℂ) ≠ q := by
        intro heq
        exact hcenter₀ (heq.symm ▸ (show q ∈ poles by simp [poles]))
      have hq₁ : (σ : ℂ) ≠ conj q := by
        intro heq
        exact hcenter₀ (heq.symm ▸ (show conj q ∈ poles by simp [poles]))
      have hF : AnalyticAt ℂ (fun z : ℂ => residue / (z - q)) (σ : ℂ) := by
        fun_prop (disch := exact sub_ne_zero.mpr hq₀)
      have hG : AnalyticAt ℂ (fun z : ℂ => conj residue / (z - conj q)) (σ : ℂ) := by
        fun_prop (disch := exact sub_ne_zero.mpr hq₁)
      let d := (σ : ℂ) - q
      let ω := (r : ℂ) / d
      have hdNorm : ‖d‖ = r := by simpa only [d, ← dist_eq_norm] using hqDist
      have hωNorm : ‖ω‖ = 1 := by
        dsimp only [ω]
        rw [norm_div, hdNorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
      have hsq : 0 < Complex.normSq d := Complex.normSq_pos.mpr (sub_ne_zero.mpr hq₀)
      have hωRe : 0 < ω.re := by
        dsimp only [ω, d]
        simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
          zero_mul, zero_div, add_zero]
        exact div_pos (mul_pos hr (sub_pos.mpr (hqUpper.trans hσ₁))) hsq
      have hωIm : 0 < ω.im := by
        dsimp only [ω, d]
        simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
          zero_mul, zero_div, zero_sub, mul_neg, neg_div, neg_neg]
        exact div_pos (mul_pos hr hqImPos) hsq
      have hconjω : (r : ℂ) / ((σ : ℂ) - conj q) = conj ω := by
        simp only [ω, d, map_div₀, map_sub, Complex.conj_ofReal]
      have hscaleSingular (k : ℕ) : (r : ℂ) ^ (k + 1) * signedTaylorCoefficient singular (σ : ℂ) k =
          residue * ω ^ (k + 1) + conj (residue * ω ^ (k + 1)) := by
        rw [hsing, signedTaylorCoefficient_add hF hG, signedTaylorCoefficient_simplePole q residue,
          signedTaylorCoefficient_simplePole (conj q) (conj residue), mul_add,
          hscale residue ((σ : ℂ) - q) k, hscale (conj residue) ((σ : ℂ) - conj q) k, hconjω]
        simp only [map_mul, map_pow, ω, d]
      obtain ⟨gap, hgood⟩ := exists_re_mul_pow_ge_half_norm_on_nat_block ω hωNorm hωRe hωIm
      refine ⟨‖residue‖, norm_pos_iff.mpr hqResidue.1, gap, fun start => ?_⟩
      obtain ⟨k, hk, hval⟩ := hgood residue start
      refine ⟨k, hk, ?_⟩
      change ‖residue‖ ≤ r ^ (k + 1) * (signedTaylorCoefficient singular (σ : ℂ) k).re
      rw [← hreScale, hscaleSingular, Complex.add_re, Complex.conj_re]
      linarith
  obtain ⟨c₀, hc₀, gap, hgood⟩ := hmain
  obtain ⟨wideGap, hwide⟩ := exists_lower_bound_on_nat_blocks_add_of_tendsto_zero hc₀ gap hgood hdecay
  refine ⟨σ, r, c₀ / 2, wideGap, hσ, hrLower, hrUpper, half_pos hc₀, fun start => ?_⟩
  obtain ⟨k, hk, hval⟩ := hwide start
  exact ⟨k, hk, (hdecomp k).symm ▸ hval⟩

theorem normalizedMellinMoment_frequently_ge_of_pole {H : ℝ → ℝ} {A : ℂ → ℂ}
    (hMellin : WindowMellinData H A) {exponent : ℝ}
    (hpoles : ∀ ρ : ℂ, exponent < ρ.re → meromorphicOrderAt A ρ < 0 →
      ρ.re < 1 ∧ ∃ residue : ℂ, HasSimplePoleWithResidue A ρ residue ∧
        (ρ.im = 0 → 0 < residue.re))
    {p : ℂ} (hp : exponent < p.re) (horder : meromorphicOrderAt A p < 0)
    (σmin : ℝ) (hσmin : 1 < σmin) :
    ∃ (σ r c : ℝ) (gap : ℕ), σmin ≤ σ ∧ σ - 1 < r ∧ r < σ - exponent ∧ 0 < c ∧
      ∀ start : ℕ, ∃ k ∈ Set.Icc start (start + gap), c ≤ normalizedMellinMoment H σ r k := by
  obtain ⟨σ, r, c, gap, hσ, hr₀, hr₁, hc, hlarge⟩ :=
    normalizedMellinTaylor_frequently_ge_of_pole hMellin hpoles hp horder σmin hσmin
  refine ⟨σ, r, c, gap, hσ, hr₀, hr₁, hc, fun start => ?_⟩
  obtain ⟨k, hk, hmoment⟩ := hlarge start
  exact ⟨k, hk, normalizedMellinMoment_eq_taylor hMellin (hσmin.trans_le hσ) r k ▸ hmoment⟩

/-- Steps 1 and 4 of Theorem 2.4. Long windows yield intervals of small normalized moments. -/
theorem normalizedMellinMoment_small_on_interval {H : ℝ → ℝ} {stretch exponent outsideExponent : ℝ}
    (hMeasurable : Measurable H) (houtside : 1 ≤ outsideExponent)
    (hGrowth : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, |H x| ≤ B * x ^ outsideExponent)
    (hstretch : 1 < stretch) (hexponent : exponent < 1)
    (hbound : HasWindowUpperBound H stretch exponent) :
    ∃ σmin : ℝ, 1 < σmin ∧ ∀ σ r : ℝ, σmin ≤ σ → σ - 1 < r → r < σ - exponent →
      ∀ c : ℝ, 0 < c → ∀ gap : ℕ,
        ∃ start : ℕ, ∀ k ∈ Set.Icc start (start + gap), normalizedMellinMoment H σ r k < c := by
  obtain ⟨amin, hamin, hcutoffs⟩ := exists_mellinGammaKernel_cutoffs hstretch
    (sub_pos.mpr (hexponent.trans_le houtside))
  obtain ⟨B, hB, hGrowth⟩ := hGrowth
  obtain ⟨C, hC, hWindows⟩ := hbound.logarithmic
  refine ⟨outsideExponent + amin, by linarith, ?_⟩
  intro σ r hσ hrLower hrUpper c hc gap
  let a := σ - outsideExponent
  let b := σ - exponent
  have haMin : amin ≤ a := by dsimp only [a]; linarith
  have ha : 0 < a := hamin.trans_le haMin
  have hrLower' : a < r := (sub_le_sub_left houtside σ).trans_lt hrLower
  have hr : 0 < r := ha.trans hrLower'
  have hb : 0 < b := hr.trans hrUpper
  have hgap : r < a + (outsideExponent - exponent) := by dsimp only [a]; linarith
  obtain ⟨bLeft, bRight, ξ₁, ξ₂, hLeft, hRight₀, hRight, hξ₁, hξ, hLeftRate, hRightRate⟩ :=
    hcutoffs a r haMin hrLower' hgap
  have hLeft₀ : 0 < bLeft := hr.trans hLeft
  have hLeftLog : Real.log (r / bLeft) < 0 :=
    (Real.log_lt_log (div_pos hr hLeft₀) ((div_lt_iff₀ hLeft₀).mpr (by simpa only [one_mul] using hLeft))).trans_eq
      Real.log_one
  have hRightLog : 0 ≤ Real.log (r / bRight) := (Real.log_pos
    ((lt_div_iff₀ hRight₀).mpr (by simpa only [one_mul] using hRight.trans hrLower'))).le
  have hMiddleLog : Real.log (r / b) < 0 :=
    (Real.log_lt_log (div_pos hr hb) ((div_lt_iff₀ hb).mpr (by simpa only [one_mul] using hrUpper))).trans_eq
      Real.log_one
  let leftRate := bLeft - a + ξ₁ * Real.log (r / bLeft)
  let rightRate := (bRight - a) * stretch + ξ₂ * Real.log (r / bRight)
  let middleRate := ξ₁ * Real.log (r / b)
  let δ := min (-leftRate) (min (-rightRate) (-middleRate))
  have hδ : 0 < δ := lt_min (neg_pos.mpr hLeftRate)
    (lt_min (neg_pos.mpr hRightRate) (neg_pos.mpr (mul_neg_of_pos_of_neg hξ₁ hMiddleLog)))
  let total := B + C + B
  have htotal : 0 < total := by dsimp only [total]; linarith
  let lengthThreshold := ((gap : ℝ) + 2) / (ξ₂ - ξ₁)
  let decayThreshold := -Real.log (c / total) / δ + 1
  obtain ⟨L, hL, hwindow⟩ := hWindows (max lengthThreshold decayThreshold)
  have hL₀ : 0 ≤ L := (le_max_left _ _).trans hL
  have hthreshold := (le_max_right _ _).trans hL
  have hlength : lengthThreshold ≤ L := (le_max_left _ _).trans hthreshold
  have hdecay : decayThreshold ≤ L := (le_max_right _ _).trans hthreshold
  have hspan : (gap : ℝ) + 2 ≤ L * (ξ₂ - ξ₁) := (div_le_iff₀ (sub_pos.mpr hξ)).mp hlength
  have hsmall : total * Real.exp (-(δ * L)) < c := by
    have hL' : -Real.log (c / total) / δ < L := by
      dsimp only [decayThreshold] at hdecay
      linarith
    have hlog := (div_lt_iff₀ hδ).mp hL'
    rw [mul_comm L δ] at hlog
    have hExp : Real.exp (-(δ * L)) < c / total :=
      (Real.exp_lt_exp.mpr (by linarith : -(δ * L) < Real.log (c / total))).trans_eq
        (Real.exp_log (div_pos hc htotal))
    rw [mul_comm total]
    exact (lt_div_iff₀ htotal).mp hExp
  have hrate (q : ℝ) (hq : δ ≤ -q) : q * L ≤ -(δ * L) := by
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right (show q ≤ -δ by linarith) hL₀
  let start := Nat.ceil (ξ₁ * L)
  refine ⟨start, ?_⟩
  intro k hk
  let n : ℝ := (k : ℝ) + 1
  have hk₁ : ξ₁ * L ≤ n := by
    have hceil : ξ₁ * L ≤ (start : ℝ) := Nat.le_ceil _
    have hstart : (start : ℝ) ≤ k := by exact_mod_cast hk.1
    exact (hceil.trans hstart).trans (by dsimp only [n]; linarith)
  have hk₂ : n ≤ ξ₂ * L := by
    have hceil : (start : ℝ) < ξ₁ * L + 1 := Nat.ceil_lt_add_one (mul_nonneg hξ₁.le hL₀)
    have hend : (k : ℝ) ≤ (start : ℝ) + (gap : ℝ) := by exact_mod_cast hk.2
    dsimp only [n]
    rw [show L * (ξ₂ - ξ₁) = ξ₂ * L - ξ₁ * L by ring] at hspan
    linarith
  let leftShift := (bLeft - a) * L
  let rightShift := (bRight - a) * (stretch * L)
  have hboundLeft : leftShift + n * Real.log (r / bLeft) ≤ -(δ * L) := by
    calc
      _ ≤ leftShift + (ξ₁ * L) * Real.log (r / bLeft) :=
        add_le_add le_rfl (mul_le_mul_of_nonpos_right hk₁ hLeftLog.le)
      _ = leftRate * L := by dsimp only [leftShift, leftRate]; ring
      _ ≤ _ := hrate leftRate (min_le_left _ _)
  have hboundRight : rightShift + n * Real.log (r / bRight) ≤ -(δ * L) := by
    calc
      _ ≤ rightShift + (ξ₂ * L) * Real.log (r / bRight) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hk₂ hRightLog)
      _ = rightRate * L := by dsimp only [rightShift, rightRate]; ring
      _ ≤ _ := hrate rightRate ((min_le_right _ _).trans (min_le_left _ _))
  have hboundMiddle : n * Real.log (r / b) ≤ -(δ * L) := by
    calc
      _ ≤ (ξ₁ * L) * Real.log (r / b) := mul_le_mul_of_nonpos_right hk₁ hMiddleLog.le
      _ = middleRate * L := by dsimp only [middleRate]; ring
      _ ≤ _ := hrate middleRate ((min_le_right _ _).trans (min_le_right _ _))
  have hscale {d : ℝ} (hd : 0 < d) (p : ℝ) :
      r ^ (k + 1) * (Real.exp p * (1 / d) ^ (k + 1)) =
        Real.exp (p + n * Real.log (r / d)) := by
    calc
      _ = Real.exp p * (r ^ (k + 1) * (1 / d) ^ (k + 1)) := by ring
      _ = Real.exp p * (r / d) ^ (k + 1) := by rw [← mul_pow, mul_one_div]
      _ = _ := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (div_pos hr hd), ← Real.exp_add,
          Nat.cast_add, Nat.cast_one, mul_comm (Real.log (r / d))]
  have hscaleMiddle : r ^ (k + 1) * (1 / b) ^ (k + 1) = Real.exp (n * Real.log (r / b)) := by
    simpa only [Real.exp_zero, one_mul, zero_add] using hscale hb 0
  have hMeasExp : Measurable (fun u => H (Real.exp u)) := hMeasurable.comp Real.continuous_exp.measurable
  have hGrowthExp (u : ℝ) (hu : 0 ≤ u) : |H (Real.exp u)| ≤ B * Real.exp (outsideExponent * u) := by
    have hExp : 1 ≤ Real.exp u := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hu
    simpa only [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_comm u outsideExponent] using
      hGrowth (Real.exp u) hExp
  have hUpper := integral_weighted_mellinGammaKernel_le_three_ranges
    (σ := σ) (outsideExponent := outsideExponent) (windowExponent := exponent) hMeasExp hB hC.le ha hb hL₀
    (le_mul_of_one_le_left hL₀ hstretch.le) (hrLower'.le.trans hLeft.le) hRight₀ hRight.le
    hGrowthExp hwindow k
  calc
    normalizedMellinMoment H σ r k ≤ r ^ (k + 1) *
        (B * (Real.exp leftShift * (1 / bLeft) ^ (k + 1)) + C * (1 / b) ^ (k + 1) +
          B * (Real.exp rightShift * (1 / bRight) ^ (k + 1))) :=
      mul_le_mul_of_nonneg_left hUpper (pow_nonneg hr.le _)
    _ = B * (r ^ (k + 1) * (Real.exp leftShift * (1 / bLeft) ^ (k + 1))) +
        C * (r ^ (k + 1) * (1 / b) ^ (k + 1)) +
        B * (r ^ (k + 1) * (Real.exp rightShift * (1 / bRight) ^ (k + 1))) := by ring
    _ = B * Real.exp (leftShift + n * Real.log (r / bLeft)) + C * Real.exp (n * Real.log (r / b)) +
        B * Real.exp (rightShift + n * Real.log (r / bRight)) := by
      rw [hscale hLeft₀ leftShift, hscaleMiddle, hscale hRight₀ rightShift]
    _ ≤ B * Real.exp (-(δ * L)) + C * Real.exp (-(δ * L)) + B * Real.exp (-(δ * L)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hboundLeft) hB)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hboundMiddle) hC.le))
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hboundRight) hB)
    _ = total * Real.exp (-(δ * L)) := by dsimp only [total]; ring
    _ < c := hsmall

/-- Theorem 2.4, the general window criterion for a Mellin transform. -/
theorem meromorphicOrder_nonneg_of_window_upper_bound {H : ℝ → ℝ} {A : ℂ → ℂ}
    (hMellin : WindowMellinData H A) {stretch exponent : ℝ}
    (hstretch : 1 < stretch) (_hexponent₀ : 0 ≤ exponent) (hexponent₁ : exponent < 1)
    (hpoles : ∀ ρ : ℂ, exponent < ρ.re → meromorphicOrderAt A ρ < 0 →
      ρ.re < 1 ∧ ∃ residue : ℂ, HasSimplePoleWithResidue A ρ residue ∧
        (ρ.im = 0 → 0 < residue.re))
    (hbound : HasWindowUpperBound H stretch exponent) {s : ℂ} (hs : exponent < s.re) :
    0 ≤ meromorphicOrderAt A s := by
  by_contra! horder
  obtain ⟨σmin, hσmin, hsmall⟩ := normalizedMellinMoment_small_on_interval
    hMellin.measurable (by norm_num : 1 ≤ (2 : ℝ)) (hMellin.powerGrowth 2 (by norm_num))
    hstretch hexponent₁ hbound
  obtain ⟨σ, r, c, gap, hσ, hr₀, hr₁, hc, hlarge⟩ :=
    normalizedMellinMoment_frequently_ge_of_pole hMellin hpoles hs horder σmin hσmin
  obtain ⟨start, hstart⟩ := hsmall σ r hσ hr₀ hr₁ c hc gap
  obtain ⟨k, hk, hmoment⟩ := hlarge start
  exact (not_lt_of_ge hmoment) (hstart k hk)

end Riemann
