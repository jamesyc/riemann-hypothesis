module

public import Riemann.AuxiliaryPrimeWindows
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

open MeasureTheory
open scoped BigOperators Classical

namespace Riemann

/-- The truncated minimum-weight sum (S_Z) in (5.11). -/
noncomputable def truncatedAuxiliarySmoothedSum (c : ℕ → ℂ) (Z : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 Z, c n * ((min 1 (y / (n : ℝ)) : ℝ) : ℂ)

/-- The partial-sum function for the coefficients in the auxiliary-prime test. -/
noncomputable def auxiliaryPartialSum (c : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 (Nat.floor y), c n

private theorem sum_Icc_split {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {N Z : ℕ} (hNZ : N ≤ Z) :
    (∑ n ∈ Finset.Icc 0 Z, f n) =
      (∑ n ∈ Finset.Icc 0 N, f n) + (∑ n ∈ Finset.Ioc N Z, f n) := by
  have hdis : Disjoint (Finset.Icc 0 N) (Finset.Ioc N Z) := by
    rw [Finset.disjoint_left]
    intro n hn hno
    exact (not_le_of_gt (Finset.mem_Ioc.mp hno).1) (Finset.mem_Icc.mp hn).2
  have hUnion : Finset.Icc 0 N ∪ Finset.Ioc N Z = Finset.Icc 0 Z := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← hUnion, Finset.sum_union hdis]

private theorem inverse_truncatedAuxiliarySmoothedSum_eq (c : ℕ → ℂ) (hzero : c 0 = 0)
    {Z : ℕ} {y : ℝ} (hy : 0 < y) (hyZ : y ≤ Z) :
    ((y⁻¹ : ℝ) : ℂ) * truncatedAuxiliarySmoothedSum c Z y =
      ((y⁻¹ : ℝ) : ℂ) * auxiliaryPartialSum c y +
        ∑ n ∈ Finset.Ioc (Nat.floor y) Z, (n : ℂ)⁻¹ * c n := by
  have hfloor : Nat.floor y ≤ Z := by simpa only [Nat.floor_natCast] using Nat.floor_mono hyZ
  unfold truncatedAuxiliarySmoothedSum auxiliaryPartialSum
  rw [sum_Icc_split _ hfloor, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hnzero : n = 0
    · simp [hnzero, hzero]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hnzero
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' hnzero).mp (Finset.mem_Icc.mp hn).2
    simp only [min_eq_left ((one_le_div hnpos).mpr hny), Complex.ofReal_one, mul_one]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnzero : n ≠ 0 := by have := (Finset.mem_Ioc.mp hn).1; omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hnzero
    have hny : y < (n : ℝ) := (Nat.floor_lt' hnzero).mp (Finset.mem_Ioc.mp hn).1
    rw [min_eq_right (div_le_one_of_le₀ hny.le hnpos.le), Complex.ofReal_inv, Complex.ofReal_div,
      Complex.ofReal_natCast]
    have hcy : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    field_simp

private theorem inverse_deriv (u : ℝ) (hu : u ≠ 0) :
    deriv (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) u = -((((u ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ) := by
  simpa only [Complex.ofReal_neg] using ((hasDerivAt_inv hu).ofReal_comp).deriv

/-- The truncated sum has the exact block identity (5.12). -/
theorem inverse_truncatedAuxiliarySmoothedSum_sub_eq_integral
    (c : ℕ → ℂ) (hzero : c 0 = 0) {Z : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbZ : b ≤ Z) :
    ((b⁻¹ : ℝ) : ℂ) * truncatedAuxiliarySmoothedSum c Z b -
      ((a⁻¹ : ℝ) : ℂ) * truncatedAuxiliarySmoothedSum c Z a =
        -(∫ u in Set.Ioc a b, ((((u ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ) * auxiliaryPartialSum c u) := by
  let f (t : ℝ) : ℂ := ((t⁻¹ : ℝ) : ℂ)
  let g (t : ℝ) : ℂ := -((((t ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ)
  have hf₁ : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t :=
    fun t ht => ((hasDerivAt_inv (ha.trans_le ht.1).ne').ofReal_comp).differentiableAt
  have hg : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.neg
    apply Complex.continuous_ofReal.comp_continuousOn
    exact (continuousOn_id.pow _).inv₀ (fun t ht => pow_ne_zero _ (ha.trans_le ht.1).ne')
  have hf₂ : IntegrableOn (deriv f) (Set.Icc a b) :=
    (hg.congr (fun t ht => inverse_deriv t (ha.trans_le ht.1).ne')).integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha.le hab hf₁ hf₂
  have hfloor := Nat.floor_mono hab
  have hbN : Nat.floor b ≤ Z := by simpa only [Nat.floor_natCast] using Nat.floor_mono hbZ
  have hsplit :
      (∑ n ∈ Finset.Ioc (Nat.floor a) Z, f n * c n) =
      (∑ n ∈ Finset.Ioc (Nat.floor a) (Nat.floor b), f n * c n) +
        ∑ n ∈ Finset.Ioc (Nat.floor b) Z, f n * c n := by
    rw [← Finset.Ioc_union_Ioc_eq_Ioc hfloor hbN,
      Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  have hInt :
      (∫ t in Set.Ioc a b, deriv f t * auxiliaryPartialSum c t) =
        -(∫ t in Set.Ioc a b, ((((t ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ) * auxiliaryPartialSum c t) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [inverse_deriv t (ha.trans ht.1).ne', neg_mul]
  rw [inverse_truncatedAuxiliarySmoothedSum_eq c hzero (ha.trans_le hab) hbZ,
    inverse_truncatedAuxiliarySmoothedSum_eq c hzero ha (hab.trans hbZ)]
  have hfCast (n : ℕ) : f n = (n : ℂ)⁻¹ := by simp [f]
  simp_rw [← hfCast]
  change f b * auxiliaryPartialSum c b + (∑ n ∈ Finset.Ioc (Nat.floor b) Z, f n * c n) -
    (f a * auxiliaryPartialSum c a + ∑ n ∈ Finset.Ioc (Nat.floor a) Z, f n * c n) = _
  rw [hsplit, hAbel]
  change _ - (_ + (_ - _ - (∫ t in Set.Ioc a b, deriv f t * auxiliaryPartialSum c t) + _)) = _
  rw [← hInt]
  simp only [auxiliaryPartialSum]
  ring

/-- The nonnegative energy (J_q(y)) used to control a complete block. -/
noncomputable def auxiliaryBlockEnergy (c : ℕ → ℂ) (y : ℝ) : ℝ :=
  ∫ u in Set.Ioc y (2 * y), (‖auxiliaryPartialSum c u‖ / u) ^ (2 : ℕ)

theorem auxiliaryBlockEnergy_nonneg (c : ℕ → ℂ) (y : ℝ) : 0 ≤ auxiliaryBlockEnergy c y :=
  integral_nonneg fun u => sq_nonneg (‖auxiliaryPartialSum c u‖ / u)

private theorem auxiliaryPartialSum_div_memLp (c : ℕ → ℂ) {a : ℝ} (ha : 0 < a) :
    MemLp (fun u => ‖auxiliaryPartialSum c u‖ / u) 2 (volume.restrict (Set.Ioc a (2 * a))) := by
  let μ := volume.restrict (Set.Ioc a (2 * a))
  let _ : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  let A := ∑ n ∈ Finset.Icc 0 (Nat.floor (2 * a)), ‖c n‖
  have hsum : Measurable (auxiliaryPartialSum c) :=
    (measurable_of_countable (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, c k)).comp Nat.measurable_floor
  refine MemLp.of_bound (hsum.norm.div measurable_id).aestronglyMeasurable (A * a⁻¹) ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
  have hu₀ := ha.trans hu.1
  have huA : ‖auxiliaryPartialSum c u‖ ≤ A := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.floor_mono hu.2)) (fun i _ _ => norm_nonneg (c i))
  rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hu₀.le), div_eq_mul_inv]
  exact mul_le_mul huA ((inv_le_inv₀ hu₀ ha).mpr hu.1.le) (by positivity)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- The partial-sum moment controls the integrated moment on the same block. -/
theorem auxiliaryBlockEnergy_sum_le_of_partial_moment {P : Type*} (pool : Finset P)
    (c : P → ℕ → ℂ) {y C : ℝ} (hy : 1 ≤ y) (hC : 0 ≤ C)
    (hpartial : ∀ u ∈ Set.Icc y (2 * y),
      (∑ p ∈ pool, ‖auxiliaryPartialSum (c p) u‖ ^ (2 : ℕ)) ≤
        C * pool.card * u * Real.log (2 * u)) :
    (∑ p ∈ pool, auxiliaryBlockEnergy (c p) y) ≤
      C * pool.card * Real.log (4 * y) := by
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  let μ := volume.restrict (Set.Ioc y (2 * y))
  let _ : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  let f (p : P) (u : ℝ) := (‖auxiliaryPartialSum (c p) u‖ / u) ^ (2 : ℕ)
  let A := C * (pool.card : ℝ) * Real.log (4 * y)
  have hi (p : P) : Integrable (f p) μ := by
    have hh := (auxiliaryPartialSum_div_memLp (c p) hy₀).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  change (∑ p ∈ pool, ∫ u, f p u ∂μ) ≤ A
  rw [← integral_finsetSum pool (fun p _ => hi p)]
  calc
    _ ≤ ∫ _ : ℝ, A / y ∂μ := by
      apply integral_mono_ae (integrable_finsetSum pool (fun p _ => hi p)) (integrable_const _)
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
      have hu₀ := hy₀.trans hu.1
      have hlog : Real.log (2 * u) ≤ Real.log (4 * y) :=
        Real.log_le_log (by positivity) (by linarith [hu.2])
      have hA : 0 ≤ A := by
        unfold A
        exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
      have hsum := (hpartial u ⟨hu.1.le, hu.2⟩).trans
        (mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ C * pool.card * u))
      calc
        (∑ p ∈ pool, f p u) = (∑ p ∈ pool, ‖auxiliaryPartialSum (c p) u‖ ^ (2 : ℕ)) / u ^ (2 : ℕ) := by
          simp only [f, div_pow, Finset.sum_div]
        _ ≤ (C * pool.card * u * Real.log (4 * y)) / u ^ (2 : ℕ) :=
          div_le_div_of_nonneg_right hsum (by positivity)
        _ = A / u := by unfold A; field_simp
        _ ≤ A / y := div_le_div_of_nonneg_left hA hy₀ hu.1.le
    _ = A := by
      rw [integral_const, smul_eq_mul]
      simp [μ, hy₀.le, show 2 * y - y = y by ring, mul_div_cancel₀ _ hy₀.ne']

private theorem norm_integral_auxiliaryPartialSum_le
    (c : ℕ → ℂ) {a b : ℝ} (ha : 0 < a) (h2 : b ≤ 2 * a) :
    ‖∫ u in Set.Ioc a b, ((((u ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ) * auxiliaryPartialSum c u‖ ≤
      Real.sqrt (auxiliaryBlockEnergy c a) * Real.sqrt ((2 * a)⁻¹) := by
  classical
  let B := Set.Ioc a (2 * a)
  let μ := volume.restrict B
  let _ : IsFiniteMeasure μ := ⟨by simp [μ, B, Real.volume_Ioc]⟩
  let f (u : ℝ) := ‖auxiliaryPartialSum c u‖ / u
  let g (u : ℝ) := u⁻¹
  have ht : ∀ᵐ u ∂μ, u ∈ B := ae_restrict_mem measurableSet_Ioc
  have hmeas : Measurable (auxiliaryPartialSum c) :=
    (measurable_of_countable (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, c k)).comp Nat.measurable_floor
  have hfm : Measurable f := hmeas.norm.div measurable_id
  have hgm : Measurable g := measurable_id.inv
  have hf₀ : 0 ≤ᵐ[μ] f := ht.mono fun u hu => div_nonneg (norm_nonneg _) (ha.trans hu.1).le
  have hg₀ : 0 ≤ᵐ[μ] g := ht.mono fun u hu => inv_nonneg.mpr (ha.trans hu.1).le
  have hgBound : ∀ᵐ u ∂μ, ‖g u‖ ≤ a⁻¹ := by
    filter_upwards [ht] with u hu
    have hu₀ := ha.trans hu.1
    dsimp only [g]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hu₀.le)]
    exact (inv_le_inv₀ hu₀ ha).mpr hu.1.le
  have hf : MemLp f 2 μ := auxiliaryPartialSum_div_memLp c ha
  have hg : MemLp g 2 μ := MemLp.of_bound hgm.aestronglyMeasurable _ hgBound
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hf₀ hg₀
    (by simpa only [ENNReal.ofReal_ofNat] using hf)
    (by simpa only [ENNReal.ofReal_ofNat] using hg)
  have hgeq : (∫ u, g u ^ (2 : ℕ) ∂μ) = (2 * a)⁻¹ := by
    have heq : (∫ u, g u ^ (2 : ℕ) ∂μ) = ∫ u, u ^ (-2 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ht] with u hu
      dsimp only [g]
      rw [inv_pow, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg (ha.trans hu.1).le, Real.rpow_natCast]
    rw [heq]
    change (∫ u in Set.Ioc a (2 * a), u ^ (-2 : ℝ)) = _
    have hab' : a ≤ 2 * a := by linarith
    rw [← intervalIntegral.integral_of_le hab',
      integral_rpow (Or.inr ⟨by norm_num, by
        rw [Set.uIcc_of_le hab']
        exact fun h => (not_le_of_gt ha) h.1⟩)]
    norm_num [Real.rpow_neg_one]
    field_simp
    norm_num
  have hh : (∫ u, f u * g u ∂μ) ≤ Real.sqrt (auxiliaryBlockEnergy c a) *
      Real.sqrt ((2 * a)⁻¹) := by
    have hpow (t : ℝ) : t ^ (2 : ℝ) = t ^ (2 : ℕ) := Real.rpow_natCast t 2
    simp_rw [hpow] at hH
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hgeq] at hH
    exact hH
  have hchange (u : ℝ) :
      ‖((((u ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ) * auxiliaryPartialSum c u‖ = f u * g u := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    dsimp only [f, g]
    rw [div_eq_mul_inv, ← inv_pow, pow_two]
    ring
  calc
    _ ≤ ∫ u in Set.Ioc a b, ‖((((u ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ) * auxiliaryPartialSum c u‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ u in Set.Ioc a b, f u * g u := integral_congr_ae (Filter.Eventually.of_forall hchange)
    _ ≤ ∫ u, f u * g u ∂μ :=
      setIntegral_mono_set (hf.integrable_mul hg)
        (by filter_upwards [hf₀, hg₀] with u hu hv; exact mul_nonneg hu hv)
        (Filter.Eventually.of_forall (Set.Ioc_subset_Ioc_right h2))
    _ ≤ _ := hh

/-- The exact continuation bound for the smoothed sum on a dyadic block. -/
theorem truncatedAuxiliarySmoothedSum_block_le
    (c : ℕ → ℂ) (hzero : c 0 = 0) {Z : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (h2 : b ≤ 2 * a) (hZ : 2 * a ≤ Z) :
    ‖truncatedAuxiliarySmoothedSum c Z b‖ ≤
      2 * ‖truncatedAuxiliarySmoothedSum c Z a‖ + Real.sqrt (2 * a * auxiliaryBlockEnergy c a) := by
  have hb := ha.trans_le hab
  let Ia := ∫ u in Set.Ioc a b, ((((u ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ) * auxiliaryPartialSum c u
  let S := truncatedAuxiliarySmoothedSum c Z
  have h := inverse_truncatedAuxiliarySmoothedSum_sub_eq_integral c hzero ha hab (h2.trans hZ)
  change ((b⁻¹ : ℝ) : ℂ) * S b - ((a⁻¹ : ℝ) : ℂ) * S a = -Ia at h
  have hs : S b = (b : ℂ) * ((a⁻¹ : ℝ) : ℂ) * S a - (b : ℂ) * Ia := by
    have hc : (b : ℂ) * ((b⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hb.ne', Complex.ofReal_one]
    have h' := congrArg (fun z : ℂ => (b : ℂ) * z) h
    simp only [mul_sub, mul_neg, ← mul_assoc, hc, one_mul] at h'
    exact eq_sub_of_add_eq (by linear_combination h')
  have hscale : b * a⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ ha).mpr h2
  have hnorm : ‖Ia‖ ≤ Real.sqrt (auxiliaryBlockEnergy c a) * Real.sqrt ((2 * a)⁻¹) :=
    norm_integral_auxiliaryPartialSum_le c ha h2
  have hsqrt :
      (2 * a) * (Real.sqrt (auxiliaryBlockEnergy c a) * Real.sqrt ((2 * a)⁻¹)) =
        Real.sqrt (2 * a * auxiliaryBlockEnergy c a) := by
    calc
      _ = (Real.sqrt (2 * a) * Real.sqrt (2 * a)) *
          (Real.sqrt (auxiliaryBlockEnergy c a) * Real.sqrt ((2 * a)⁻¹)) := by
        rw [Real.mul_self_sqrt (by positivity)]
      _ = Real.sqrt (2 * a * auxiliaryBlockEnergy c a) *
          (Real.sqrt (2 * a) * Real.sqrt ((2 * a)⁻¹)) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * a)]
        ring
      _ = _ := by rw [← Real.sqrt_mul (by positivity), mul_inv_cancel₀ (by positivity),
        Real.sqrt_one, mul_one]
  change ‖S b‖ ≤ 2 * ‖S a‖ + Real.sqrt (2 * a * auxiliaryBlockEnergy c a)
  rw [hs]
  calc
    _ ≤ ‖(b : ℂ) * ((a⁻¹ : ℝ) : ℂ) * S a‖ + ‖(b : ℂ) * Ia‖ := norm_sub_le _ _
    _ = b * a⁻¹ * ‖S a‖ + b * ‖Ia‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hb.le, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
    _ ≤ 2 * ‖S a‖ + (2 * a) *
        (Real.sqrt (auxiliaryBlockEnergy c a) * Real.sqrt ((2 * a)⁻¹)) :=
      add_le_add (mul_le_mul_of_nonneg_right hscale (norm_nonneg _))
        (mul_le_mul h2 hnorm (norm_nonneg _) (by positivity))
    _ = _ := by rw [hsqrt]

/-- The smoothed sums satisfy the dyadic exceptional count once their
two uniform moment bounds have been established. -/
theorem auxiliaryExceptional_truncated_window_bound {P : Type*}
    (pool : Finset P) (c : P → ℕ → ℂ) (Z : ℕ) {Y X τ C : ℝ}
    (hY : 1 ≤ Y) (hτ : 0 < τ) (hC : 0 ≤ C) (hZ : 2 * X ≤ Z)
    (hzero : ∀ q ∈ pool, c q 0 = 0)
    (hS : ∀ y ∈ Set.Icc Y X,
      (∑ q ∈ pool, ‖truncatedAuxiliarySmoothedSum (c q) Z y‖ ^ (2 : ℕ)) ≤
        C * pool.card * y * Real.log (2 * y))
    (hJ : ∀ y ∈ Set.Icc Y X, (∑ q ∈ pool, auxiliaryBlockEnergy (c q) y) ≤
      C * pool.card * Real.log (2 * y)) :
    ((pool.filter fun q => ∃ u ∈ Set.Icc Y X,
      (1 / 2 : ℝ) * u ^ (1 / 2 + τ) < ‖truncatedAuxiliarySmoothedSum (c q) Z u‖).card : ℝ) ≤
      96 * C * pool.card * (Y ^ (-2 * τ) * Real.log (2 * Y) /
        (1 - (4 : ℝ) ^ (-τ)) ^ (2 : ℕ)) := by
  apply auxiliaryExceptional_window_bound pool (fun q => truncatedAuxiliarySmoothedSum (c q) Z)
    (fun q => auxiliaryBlockEnergy (c q)) hY hτ hC (fun y _ q _ => auxiliaryBlockEnergy_nonneg _ y) hS hJ
  intro y hy y' hy' q hq
  have hy₀ : 0 < y := zero_lt_one.trans_le (hY.trans hy.1)
  exact truncatedAuxiliarySmoothedSum_block_le (c q) (hzero q hq) hy₀ hy'.1 hy'.2
    ((mul_le_mul_of_nonneg_left hy.2 (by norm_num : (0 : ℝ) ≤ 2)).trans hZ)

end Riemann
