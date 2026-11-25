module

public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace Utilities

/-- The smoothed von Mangoldt sum shared by zeta and the character twists. -/
noncomputable def smoothedMangoldt (coefficient : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x),
    ((ArithmeticFunction.vonMangoldt n * (x / (n : ℝ) - 1) : ℝ) : ℂ) * coefficient n

/-- The summand entering at each integer is zero there, so the variable
truncation is locally a fixed sum of continuous positive-part cutoffs. -/
theorem continuous_smoothedMangoldt (coefficient : ℕ → ℂ) : Continuous (smoothedMangoldt coefficient) := by
  rw [continuous_iff_continuousAt]
  intro x
  let N := Nat.ceil (x + 1)
  let term (n : ℕ) (t : ℝ) : ℂ :=
    ((ArithmeticFunction.vonMangoldt n * max (t / (n : ℝ) - 1) 0 : ℝ) : ℂ) * coefficient n
  let cutoff (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 N, term n t
  have hterm (n : ℕ) : Continuous (term n) := by
    dsimp only [term]
    fun_prop
  have hcutoff : Continuous cutoff := continuous_finsetSum _ fun n _ => hterm n
  apply hcutoff.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (show x < x + 1 by linarith)] with t ht
  change t < x + 1 at ht
  have hfloor : Nat.floor t ≤ N := by
    have hN : t ≤ (N : ℝ) := ht.le.trans (Nat.le_ceil (x + 1))
    simpa only [Nat.floor_natCast] using Nat.floor_mono hN
  have hsubset : Finset.Icc 1 (Nat.floor t) ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hfloor
  calc
    smoothedMangoldt coefficient t = ∑ n ∈ Finset.Icc 1 (Nat.floor t), term n t := by
      unfold smoothedMangoldt
      refine Finset.sum_congr rfl fun n hn => ?_
      obtain ⟨hn₁, hnFloor⟩ := Finset.mem_Icc.mp hn
      have hn₀ : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn₁
      have hnPos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn₀)
      have hnt : (n : ℝ) ≤ t := (Nat.le_floor_iff' hn₀).mp hnFloor
      have hpos : 0 ≤ t / (n : ℝ) - 1 := sub_nonneg.mpr
        ((le_div_iff₀ hnPos).mpr (by simpa only [one_mul] using hnt))
      simp only [term, max_eq_left hpos]
    _ = cutoff t := by
      refine Finset.sum_subset hsubset fun n hn hnot => ?_
      have hn₁ := (Finset.mem_Icc.mp hn).1
      have hn₀ : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn₁
      have hnPos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn₀)
      have hnFloor : Nat.floor t < n := lt_of_not_ge fun h => hnot (Finset.mem_Icc.mpr ⟨hn₁, h⟩)
      have htn : t < (n : ℝ) := (Nat.floor_lt' hn₀).mp hnFloor
      have hneg : t / (n : ℝ) - 1 ≤ 0 := sub_nonpos.mpr
        ((div_le_iff₀ hnPos).mpr (by simpa only [one_mul] using htn.le))
      simp only [term, max_eq_right hneg, mul_zero, Complex.ofReal_zero, zero_mul]

theorem smoothedMangoldt_congr_on_primePowers {f g : ℕ → ℂ}
    (h : ∀ n, IsPrimePow n → f n = g n) (x : ℝ) :
    smoothedMangoldt f x = smoothedMangoldt g x := by
  unfold smoothedMangoldt
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : IsPrimePow n
  · rw [h n hn]
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    simp

theorem smoothedMangoldt_one_real (x : ℝ) :
    ((smoothedMangoldt (fun _ => 1) x).re : ℂ) = smoothedMangoldt (fun _ => 1) x := by
  simp only [smoothedMangoldt, mul_one, ← Complex.ofReal_sum, Complex.ofReal_re]

end Utilities
