module

public import Utilities.FiniteMeanSquare
public import Utilities.ExponentialGrowth
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

open Filter Utilities
open scoped BigOperators Classical

namespace Riemann

private theorem exists_dyadic_left {Y y : ℝ} (hY : 0 < Y) (hy : Y ≤ y) :
    ∃ j : ℕ, Y * 2 ^ j ≤ y ∧ y ≤ 2 * (Y * 2 ^ j) := by
  obtain ⟨n, h₁, h₂⟩ := exists_dyadic_cover ((one_le_div hY).mpr hy)
  cases n with
  | zero =>
    rw [pow_zero] at h₁
    have h := (div_le_iff₀ hY).mp h₁
    exact ⟨0, by simpa only [pow_zero, mul_one] using hy, by
      simp only [pow_zero, mul_one] at *
      linarith⟩
  | succ j =>
    rw [pow_succ] at h₁ h₂
    refine ⟨j, ?_, ?_⟩
    · have ha : (2 : ℝ) ^ j ≤ y / Y := by linarith
      have hb := (le_div_iff₀ hY).mp ha
      simpa only [mul_comm] using hb
    · have h := (div_le_iff₀ hY).mp h₁
      convert h using 1
      ring

private theorem sum_dyadic_tail_le {Y τ : ℝ} (hY : 1 ≤ Y) (hτ : 0 < τ) (N : ℕ) :
    (∑ j ∈ Finset.range N, (Y * (2 : ℝ) ^ j) ^ (-2 * τ) *
      Real.log (2 * (Y * (2 : ℝ) ^ j))) ≤
      Y ^ (-2 * τ) * Real.log (2 * Y) / (1 - (4 : ℝ) ^ (-τ)) ^ (2 : ℕ) := by
  let r := (4 : ℝ) ^ (-τ)
  have hr₀ : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hrn : ‖r‖ < 1 := by simpa only [Real.norm_of_nonneg hr₀.le] using hr₁
  have hsum : HasSum (fun j : ℕ => ((j : ℝ) + 1) * r ^ j) ((1 - r) ^ (2 : ℕ))⁻¹ := by
    have h := (hasSum_coe_mul_geometric_of_norm_lt_one hrn).add
      (hasSum_geometric_of_norm_lt_one hrn)
    have heq : r / (1 - r) ^ (2 : ℕ) + (1 - r)⁻¹ = ((1 - r) ^ (2 : ℕ))⁻¹ := by
      field_simp [show 1 - r ≠ 0 by linarith]
      ring
    simpa only [heq, add_mul, one_mul] using h
  have hy₀ := zero_lt_one.trans_le hY
  have hlog₂ : Real.log 2 ≤ Real.log (2 * Y) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog₀ : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have hbase : (2 : ℝ) ^ (-2 * τ) = r := by
    dsimp only [r]
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hpoint (j : ℕ) :
      (Y * (2 : ℝ) ^ j) ^ (-2 * τ) * Real.log (2 * (Y * (2 : ℝ) ^ j)) ≤
        (Y ^ (-2 * τ) * Real.log (2 * Y)) * (((j : ℝ) + 1) * r ^ j) := by
    have hp : ((2 : ℝ) ^ j) ^ (-2 * τ) = r ^ j := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), hbase, Real.rpow_natCast]
    have hlogj : Real.log (2 * (Y * (2 : ℝ) ^ j)) =
        Real.log (2 * Y) + (j : ℝ) * Real.log 2 := by
      rw [← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [Real.mul_rpow hy₀.le (by positivity), hp, hlogj]
    calc
      Y ^ (-2 * τ) * r ^ j * (Real.log (2 * Y) + (j : ℝ) * Real.log 2) ≤
          Y ^ (-2 * τ) * r ^ j * (Real.log (2 * Y) + (j : ℝ) * Real.log (2 * Y)) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ Finset.range N, (Y ^ (-2 * τ) * Real.log (2 * Y)) * (((j : ℝ) + 1) * r ^ j) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ ≤ (Y ^ (-2 * τ) * Real.log (2 * Y)) * ((1 - r) ^ (2 : ℕ))⁻¹ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← hsum.tsum_eq]
      exact hsum.summable.sum_le_tsum _ (fun j _ => by positivity)
    _ = _ := by rw [div_eq_mul_inv]

private theorem card_bad_dyadic_block_le {P : Type*} (pool : Finset P)
    (S : P → ℂ) (J : P → ℝ) {C y τ : ℝ} (hy : 1 ≤ y)
    (hJ₀ : ∀ q ∈ pool, 0 ≤ J q)
    (hS : (∑ q ∈ pool, ‖S q‖ ^ (2 : ℕ)) ≤ C * pool.card * y * Real.log (2 * y))
    (hJ : (∑ q ∈ pool, J q) ≤ C * pool.card * Real.log (2 * y)) :
    ((pool.filter fun q => (1 / 8 : ℝ) * y ^ (1 / 2 + τ) < ‖S q‖ ∨
      (1 / 32 : ℝ) * y ^ (2 * τ) < J q).card : ℝ) ≤
      96 * C * pool.card * y ^ (-2 * τ) * Real.log (2 * y) := by
  have hy₀ := zero_lt_one.trans_le hy
  let w (q : P) := 64 / y ^ (1 + 2 * τ) * ‖S q‖ ^ (2 : ℕ) + 32 / y ^ (2 * τ) * J q
  have hw₀ (q : P) (hq : q ∈ pool) : 0 ≤ w q := by
    dsimp only [w]
    have hj := hJ₀ q hq
    positivity
  refine (card_marked_le_sum_weights _ _ w hw₀ ?_).trans ?_
  · intro q hq h
    dsimp only [w]
    rcases h with hs | hj
    · have hs' := pow_le_pow_left₀ (by positivity) hs.le (2 : ℕ)
      have hpow : ((1 / 8 : ℝ) * y ^ (1 / 2 + τ)) ^ (2 : ℕ) = y ^ (1 + 2 * τ) / 64 := by
        rw [mul_pow, pow_two (y ^ (1 / 2 + τ)), ← Real.rpow_add hy₀,
          show 1 / 2 + τ + (1 / 2 + τ) = 1 + 2 * τ by ring]
        ring
      rw [hpow] at hs'
      have hone : 1 ≤ 64 / y ^ (1 + 2 * τ) * ‖S q‖ ^ (2 : ℕ) := by
        rw [div_mul_eq_mul_div]
        apply (one_le_div (Real.rpow_pos_of_pos hy₀ _)).mpr
        linarith
      have hj := hJ₀ q hq
      exact hone.trans (le_add_of_nonneg_right (by positivity))
    · have hone : 1 ≤ 32 / y ^ (2 * τ) * J q := by
        rw [div_mul_eq_mul_div]
        apply (one_le_div (Real.rpow_pos_of_pos hy₀ _)).mpr
        linarith only [hj]
      exact hone.trans (le_add_of_nonneg_left (by positivity))
  simp only [w, Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    _ ≤ 64 / y ^ (1 + 2 * τ) * (C * pool.card * y * Real.log (2 * y)) +
        32 / y ^ (2 * τ) * (C * pool.card * Real.log (2 * y)) :=
      add_le_add (mul_le_mul_of_nonneg_left hS (by positivity))
        (mul_le_mul_of_nonneg_left hJ (by positivity))
    _ = _ := by
      rw [Real.rpow_add hy₀, Real.rpow_one, show -2 * τ = -(2 * τ) by ring,
        Real.rpow_neg hy₀.le]
      field_simp
      ring

/-- The dyadic count in Proposition 5.6, starting from the block estimates
and the two pointwise second moments. -/
theorem auxiliaryExceptional_window_bound {P : Type*} (pool : Finset P)
    (S : P → ℝ → ℂ) (J : P → ℝ → ℝ) {Y X τ C : ℝ}
    (hY : 1 ≤ Y) (hτ : 0 < τ) (hC : 0 ≤ C)
    (hJ₀ : ∀ y ∈ Set.Icc Y X, ∀ q ∈ pool, 0 ≤ J q y)
    (hS : ∀ y ∈ Set.Icc Y X,
      (∑ q ∈ pool, ‖S q y‖ ^ (2 : ℕ)) ≤ C * pool.card * y * Real.log (2 * y))
    (hJ : ∀ y ∈ Set.Icc Y X, (∑ q ∈ pool, J q y) ≤ C * pool.card * Real.log (2 * y))
    (hblock : ∀ y ∈ Set.Icc Y X, ∀ y' ∈ Set.Icc y (2 * y), ∀ q ∈ pool,
      ‖S q y'‖ ≤ 2 * ‖S q y‖ + Real.sqrt (2 * y * J q y)) :
    ((pool.filter fun q => ∃ u ∈ Set.Icc Y X, (1 / 2 : ℝ) * u ^ (1 / 2 + τ) < ‖S q u‖).card : ℝ) ≤
      96 * C * pool.card * (Y ^ (-2 * τ) * Real.log (2 * Y) /
        (1 - (4 : ℝ) ^ (-τ)) ^ (2 : ℕ)) := by
  classical
  have hY₀ := zero_lt_one.trans_le hY
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (X / Y) (by norm_num : (1 : ℝ) < 2)
  let y (j : ℕ) := Y * (2 : ℝ) ^ j
  let I := (Finset.range (N + 1)).filter (fun j => y j ≤ X)
  let bad (j : ℕ) := pool.filter fun q =>
    (1 / 8 : ℝ) * (y j) ^ (1 / 2 + τ) < ‖S q (y j)‖ ∨
      (1 / 32 : ℝ) * (y j) ^ (2 * τ) < J q (y j)
  have hYy (j : ℕ) : Y ≤ y j := le_mul_of_one_le_right hY₀.le (one_le_pow₀ (by norm_num))
  have hyI (j : ℕ) (hj : j ∈ I) : y j ∈ Set.Icc Y X := ⟨hYy j, (Finset.mem_filter.mp hj).2⟩
  have hcover (u : ℝ) (hu : u ∈ Set.Icc Y X) :
      ∃ j ∈ I, u ∈ Set.Icc (y j) (2 * y j) := by
    obtain ⟨j, hlo, hhi⟩ := exists_dyadic_left hY₀ hu.1
    have hjX : y j ≤ X := hlo.trans hu.2
    have hXn : X ≤ y N := by
      dsimp only [y]
      rw [mul_comm]
      exact (div_le_iff₀ hY₀).mp hN.le
    have hjN : j ≤ N := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      (le_of_mul_le_mul_left (hjX.trans hXn) hY₀)
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjX⟩, hlo, hhi⟩
  have hsubset : (pool.filter fun q => ∃ u ∈ Set.Icc Y X,
      (1 / 2 : ℝ) * u ^ (1 / 2 + τ) < ‖S q u‖) ⊆ I.biUnion bad := by
    intro q hq
    obtain ⟨hqP, u, hu, hlarge⟩ := Finset.mem_filter.mp hq
    obtain ⟨j, hj, hblockj⟩ := hcover u hu
    apply Finset.mem_biUnion.mpr
    refine ⟨j, hj, Finset.mem_filter.mpr ⟨hqP, ?_⟩⟩
    by_contra! hgood
    have hy₀ : 0 < y j := hY₀.trans_le (hYy j)
    have hsmallJ : Real.sqrt (2 * y j * J q (y j)) ≤ (1 / 4 : ℝ) * (y j) ^ (1 / 2 + τ) := by
      apply (Real.sqrt_le_iff).mpr ⟨by positivity, ?_⟩
      rw [mul_pow, pow_two ((y j) ^ (1 / 2 + τ)), ← Real.rpow_add hy₀,
        show 1 / 2 + τ + (1 / 2 + τ) = 1 + 2 * τ by ring, Real.rpow_add hy₀, Real.rpow_one]
      nlinarith only [mul_le_mul_of_nonneg_left hgood.2 (show 0 ≤ 2 * y j by positivity)]
    have hloc := hblock (y j) (hyI j hj) u hblockj q hqP
    have hmain : ‖S q u‖ ≤ (1 / 2 : ℝ) * (y j) ^ (1 / 2 + τ) := by
      linarith only [hloc, hgood.1, hsmallJ]
    exact (not_lt_of_ge (hmain.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hy₀.le hblockj.1 (by positivity)) (by norm_num)))) hlarge
  have hnorm (j : ℕ) (hj : j ∈ I) :
      ((bad j).card : ℝ) ≤ 96 * C * pool.card * (y j) ^ (-2 * τ) * Real.log (2 * y j) :=
    card_bad_dyadic_block_le pool (fun q => S q (y j)) (fun q => J q (y j))
      (hY.trans (hYy j)) (hJ₀ _ (hyI j hj)) (hS _ (hyI j hj)) (hJ _ (hyI j hj))
  have hcard : ((I.biUnion bad).card : ℝ) ≤ ∑ j ∈ I, ((bad j).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  calc
    _ ≤ ((I.biUnion bad).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ j ∈ I, ((bad j).card : ℝ) := hcard
    _ ≤ ∑ j ∈ I, 96 * C * pool.card * (y j) ^ (-2 * τ) * Real.log (2 * y j) :=
      Finset.sum_le_sum hnorm
    _ ≤ ∑ j ∈ Finset.range (N + 1), 96 * C * pool.card * (y j) ^ (-2 * τ) * Real.log (2 * y j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro j _ _
      have hylog : 0 ≤ Real.log (2 * y j) := Real.log_nonneg (by linarith [hYy j])
      have hypos := hY₀.trans_le (hYy j)
      positivity
    _ = (96 * C * pool.card) *
        (∑ j ∈ Finset.range (N + 1), (y j) ^ (-2 * τ) * Real.log (2 * y j)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_dyadic_tail_le hY hτ _) (by positivity)

end Riemann
