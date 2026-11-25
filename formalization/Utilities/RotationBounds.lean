module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

open Filter
open scoped Topology

namespace Utilities

/-- A rotation with step strictly between `0` and `π / 2` reaches the arc
where the cosine is at least one half in every sufficiently long block. -/
theorem exists_cos_ge_half_on_nat_block {φ : ℝ} (hφ : 0 < φ) (hφ' : φ < Real.pi / 2) :
    ∃ gap : ℕ, ∀ α : ℝ, ∀ start : ℕ, ∃ k ∈ Set.Icc start (start + gap),
      (1 / 2 : ℝ) ≤ Real.cos (α + (k : ℝ) * φ) := by
  let period := 2 * Real.pi
  have hperiod : 0 < period := mul_pos (by norm_num) Real.pi_pos
  let gap := Nat.ceil (period / φ)
  refine ⟨gap, fun α start => ?_⟩
  let center := α + (start : ℝ) * φ + φ / 2
  let m := Int.ceil (center / period)
  let distance := (m : ℝ) * period - center
  have hcenter : center / period ≤ m := Int.le_ceil _
  have hdistance : 0 ≤ distance := sub_nonneg.mpr ((div_le_iff₀ hperiod).mp hcenter)
  have hdistance' : distance < period := by
    have hm : (m : ℝ) < center / period + 1 := Int.ceil_lt_add_one _
    have hmul := mul_lt_mul_of_pos_right hm hperiod
    rw [add_mul, div_mul_cancel₀ _ hperiod.ne', one_mul] at hmul
    dsimp only [distance]
    linarith
  let j := Nat.ceil (distance / φ)
  have hj : j ≤ gap := Nat.ceil_mono (div_le_div_of_nonneg_right hdistance'.le hφ.le)
  have hjLower : distance ≤ (j : ℝ) * φ := (div_le_iff₀ hφ).mp (Nat.le_ceil _)
  have hjUpper : (j : ℝ) * φ < distance + φ := by
    have hceil : (j : ℝ) < distance / φ + 1 := Nat.ceil_lt_add_one (div_nonneg hdistance hφ.le)
    have hmul := mul_lt_mul_of_pos_right hceil hφ
    rwa [add_mul, div_mul_cancel₀ _ hφ.ne', one_mul] at hmul
  let residual := (j : ℝ) * φ - distance - φ / 2
  have hresidual : |residual| ≤ Real.pi / 3 := by
    apply abs_le.mpr
    dsimp only [residual]
    constructor <;> linarith [Real.pi_pos]
  have hangle : α + ((start + j : ℕ) : ℝ) * φ = residual + (m : ℝ) * period := by
    simp only [Nat.cast_add, residual, distance, center]
    ring
  have hcos : (1 / 2 : ℝ) ≤ Real.cos |residual| := by
    rw [← Real.cos_pi_div_three]
    exact Real.antitoneOn_cos ⟨abs_nonneg _, by linarith [Real.pi_pos]⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩ hresidual
  refine ⟨start + j, ⟨Nat.le_add_right _ _, Nat.add_le_add_left hj _⟩, ?_⟩
  rw [hangle]
  change (1 / 2 : ℝ) ≤ Real.cos (residual + (m : ℝ) * (2 * Real.pi))
  rw [Real.cos_add_int_mul_two_pi]
  simpa only [Real.cos_abs] using hcos

/-- Polar coordinates for the real part of a unit rotation applied to `z`. -/
theorem re_mul_pow_eq_norm_mul_cos_of_norm_one (z q : ℂ) (hq : ‖q‖ = 1) (n : ℕ) :
    (z * q ^ n).re = ‖z‖ * Real.cos (z.arg + (n : ℝ) * q.arg) := by
  have hqExp : q = Complex.exp ((q.arg : ℂ) * Complex.I) := by
    simpa only [hq, Complex.ofReal_one, one_mul] using (Complex.norm_mul_exp_arg_mul_I q).symm
  have hpow : Complex.exp ((q.arg : ℂ) * Complex.I) ^ n =
      Complex.exp ((((n : ℝ) * q.arg : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc]
  calc
    _ = (z * Complex.exp ((q.arg : ℂ) * Complex.I) ^ n).re :=
      congrArg (fun w : ℂ => (z * w ^ n).re) hqExp
    _ = (((‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I)) *
        Complex.exp ((((n : ℝ) * q.arg : ℝ) : ℂ) * Complex.I)).re := by
      rw [Complex.norm_mul_exp_arg_mul_I, ← hpow]
    _ = ((‖z‖ : ℂ) * Complex.exp (((z.arg + (n : ℝ) * q.arg : ℝ) : ℂ) * Complex.I)).re := by
      rw [Complex.ofReal_add, add_mul, Complex.exp_add, mul_assoc]
    _ = _ := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.exp_ofReal_mul_I_re]

/-- Positive lower bounds for the real part recur with bounded gaps for a
unit rotation in the open first quadrant. -/
theorem exists_re_mul_pow_ge_half_norm_on_nat_block (q : ℂ) (hq : ‖q‖ = 1)
    (hre : 0 < q.re) (him : 0 < q.im) :
    ∃ gap : ℕ, ∀ z : ℂ, ∀ start : ℕ, ∃ k ∈ Set.Icc start (start + gap),
      ‖z‖ / 2 ≤ (z * q ^ (k + 1)).re := by
  have harg₀ : q.arg ≠ 0 := by
    intro heq
    have hsin := Complex.sin_arg q
    rw [heq, Real.sin_zero, hq, div_one] at hsin
    exact him.ne' hsin.symm
  have harg : 0 < q.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le) harg₀.symm
  have harg' : q.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  obtain ⟨gap, hgood⟩ := exists_cos_ge_half_on_nat_block harg harg'
  refine ⟨gap, fun z start => ?_⟩
  obtain ⟨k, hk, hcos⟩ := hgood (z.arg + q.arg) start
  have hphase : z.arg + q.arg + (k : ℝ) * q.arg = z.arg + ((k + 1 : ℕ) : ℝ) * q.arg := by
    push_cast
    ring
  refine ⟨k, hk, ?_⟩
  rw [hphase] at hcos
  rw [re_mul_pow_eq_norm_mul_cos_of_norm_one z q hq]
  calc
    ‖z‖ / 2 = ‖z‖ * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcos (norm_nonneg z)

/-- A perturbation tending to zero preserves a positive lower bound on some
index in every sufficiently long block. -/
theorem exists_lower_bound_on_nat_blocks_add_of_tendsto_zero {u v : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (gap : ℕ) (hgood : ∀ start, ∃ k ∈ Set.Icc start (start + gap), c ≤ u k)
    (herror : Tendsto v atTop (𝓝 0)) :
    ∃ wideGap : ℕ, ∀ start, ∃ k ∈ Set.Icc start (start + wideGap), c / 2 ≤ u k + v k := by
  have hsmall : ∀ᶠ k in atTop, -(c / 2) < v k := herror.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp hsmall
  refine ⟨cutoff + gap, fun start => ?_⟩
  obtain ⟨k, hk, hg⟩ := hgood (start + cutoff)
  have hk₀ : cutoff ≤ k := (Nat.le_add_left _ _).trans hk.1
  refine ⟨k, ⟨(Nat.le_add_right _ _).trans hk.1, by simpa only [add_assoc] using hk.2⟩, ?_⟩
  have hv := hcutoff k hk₀
  linarith

end Utilities
