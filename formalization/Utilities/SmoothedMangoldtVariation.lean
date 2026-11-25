module

public import Utilities.SmoothedMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open scoped BigOperators

namespace Utilities

private theorem chebyshev_psi_le_three {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x ≤ 3 * x := by
  let t := Real.sqrt x
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have ht : 0 < t := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have ht₂ : t ^ 2 = x := Real.sq_sqrt hx₀
  have hlogx : Real.log x = 2 * Real.log t := by
    rw [← ht₂, Real.log_pow]
    norm_num
  have hlogt : Real.log t ≤ t / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos ht (Real.exp_pos 1))
    rw [Real.log_div ht.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    linarith
  have hlogt' : Real.log t ≤ (2 / 5 : ℝ) * t := by
    apply hlogt.trans
    rw [div_le_iff₀ (Real.exp_pos 1)]
    have he : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr he)]
  have hlog4 : Real.log 4 ≤ (7 / 5 : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  have hmain := mul_le_mul_of_nonneg_right hlog4 hx₀
  have htail : 2 * t * Real.log x ≤ (8 / 5 : ℝ) * x := by
    rw [hlogx, ← ht₂]
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hlogt')]
  exact (Chebyshev.psi_le hx).trans (by linarith)

private theorem weighted_smoothedMangoldt_eq_cutoff (coefficient : ℕ → ℂ)
    {A w : ℝ} (hw : 0 < w) {N : ℕ} (hN : Nat.floor (A / w) ≤ N) :
    (w : ℂ) * smoothedMangoldt coefficient (A / w) = ∑ n ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.vonMangoldt n * max (A / (n : ℝ) - w) 0 : ℝ) : ℂ) *
        coefficient n := by
  unfold smoothedMangoldt
  rw [Finset.mul_sum]
  let term (n : ℕ) := ((ArithmeticFunction.vonMangoldt n * max (A / (n : ℝ) - w) 0 : ℝ) : ℂ) *
    coefficient n
  calc
    _ = ∑ n ∈ Finset.Icc 1 (Nat.floor (A / w)), term n := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hn₁, hnle⟩ := Finset.mem_Icc.mp hn
      have hn₀ : n ≠ 0 := by omega
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn₀
      have hle := (Nat.le_floor_iff' hn₀).mp hnle
      have hnonneg : 0 ≤ A / (n : ℝ) - w := sub_nonneg.mpr ((le_div_iff₀ hnpos).mpr
        (by rw [mul_comm]; exact (le_div_iff₀ hw).mp hle))
      dsimp only [term]
      rw [max_eq_left hnonneg, ← mul_assoc, ← Complex.ofReal_mul]
      congr 2
      field_simp
    _ = _ := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right hN)
      intro n hn hx
      have hn₀ : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn₀
      have hnlt : Nat.floor (A / w) < n := lt_of_not_ge fun h =>
        hx (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, h⟩)
      have hlt := (Nat.floor_lt' hn₀).mp hnlt
      have hneg : A / (n : ℝ) - w ≤ 0 := sub_nonpos.mpr ((div_le_iff₀ hnpos).mpr
        (by rw [mul_comm]; exact (div_le_iff₀ hw).mp hlt.le))
      simp [term, max_eq_right hneg]

private theorem cutoff_diff_bounds {t w w' : ℝ} (hww' : w ≤ w') :
    0 ≤ max (t - w) 0 - max (t - w') 0 ∧
      max (t - w) 0 - max (t - w') 0 ≤ w' - w := by
  refine ⟨sub_nonneg.mpr (max_le_max (sub_le_sub_left hww' _) le_rfl), ?_⟩
  apply sub_le_iff_le_add.mpr
  rw [add_comm]
  apply max_le
  · linarith [le_max_left (t - w') (0 : ℝ)]
  · exact add_nonneg (le_max_right _ _) (sub_nonneg.mpr hww')

/-- Weighted smoothed sums change at most by the Chebyshev bound when the
positive weight is increased. This is the raw-sum estimate in Lemma 4.1(i). -/
theorem norm_weighted_smoothedMangoldt_sub_le
    (coefficient : ℕ → ℂ) (hcoeff : ∀ n, ‖coefficient n‖ ≤ 1)
    {A w w' : ℝ} (hw : 0 < w) (hww' : w ≤ w') (hwA : w ≤ A) :
    ‖(w : ℂ) * smoothedMangoldt coefficient (A / w) -
      (w' : ℂ) * smoothedMangoldt coefficient (A / w')‖ ≤ 3 * A * (w' - w) / w := by
  have hw' := hw.trans_le hww'
  have hA := hw.trans_le hwA
  have hscale : 1 ≤ A / w := (one_le_div hw).mpr hwA
  let N := Nat.floor (A / w)
  have hN : Nat.floor (A / w') ≤ N :=
    Nat.floor_mono (div_le_div_of_nonneg_left hA.le hw hww')
  rw [weighted_smoothedMangoldt_eq_cutoff coefficient hw (le_refl N),
    weighted_smoothedMangoldt_eq_cutoff coefficient hw' hN, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * (w' - w) := by
      apply Finset.sum_le_sum
      intro n _
      have hc := cutoff_diff_bounds (t := A / (n : ℝ)) hww'
      have hv := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      rw [← sub_mul, ← Complex.ofReal_sub, ← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv hc.1)]
      exact (mul_le_of_le_one_right (mul_nonneg hv hc.1) (hcoeff n)).trans
        (mul_le_mul_of_nonneg_left hc.2 hv)
    _ = Chebyshev.psi (A / w) * (w' - w) := by
      rw [← Finset.sum_mul, Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc]
      rfl
    _ ≤ _ := by
      calc
        _ ≤ (3 * (A / w)) * (w' - w) :=
          mul_le_mul_of_nonneg_right (chebyshev_psi_le_three hscale) (sub_nonneg.mpr hww')
        _ = _ := by ring

/-- The raw smoothed sum with the zeta coefficients decreases as its weight increases. -/
theorem weighted_smoothedMangoldt_one_re_antitone {A w w' : ℝ}
    (hA : 0 ≤ A) (hw : 0 < w) (hww' : w ≤ w') :
    w' * (smoothedMangoldt (fun _ => 1) (A / w')).re ≤
      w * (smoothedMangoldt (fun _ => 1) (A / w)).re := by
  have hN := Nat.floor_mono (div_le_div_of_nonneg_left hA hw hww')
  have hmul (t : ℝ) (c : ℂ) : t * c.re = ((t : ℂ) * c).re := by
    simp [Complex.mul_re]
  rw [hmul, hmul]
  rw [weighted_smoothedMangoldt_eq_cutoff _ (hw.trans_le hww') hN,
    weighted_smoothedMangoldt_eq_cutoff _ hw le_rfl]
  simp only [mul_one, ← Complex.ofReal_sum, Complex.ofReal_re]
  apply Finset.sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_left (sub_nonneg.mp (cutoff_diff_bounds hww').1)
    ArithmeticFunction.vonMangoldt_nonneg

end Utilities
