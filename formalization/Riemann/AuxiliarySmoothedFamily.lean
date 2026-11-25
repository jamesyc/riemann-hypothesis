module

public import Riemann.AuxiliarySmoothedWindow
public import Riemann.SmoothedCharacters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter Utilities
open scoped BigOperators Classical

namespace Riemann

/-- The coefficients in the partial and truncated sums of §5.3. -/
noncomputable def auxiliarySmoothedCoefficients (χ : BundledDirichletCharacter) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * χ.character (n : ZMod (χ.modulus : ℕ))

/-- Pointwise moments for the same finite family of characters and the same search pool. -/
def AuxiliarySmoothedMomentBounds {P ι : Type*} (pool : Finset P)
    (χ : P → ι → BundledDirichletCharacter) (Z : ℕ) (Y X C : ℝ) : Prop :=
  ∀ i : ι,
    (∀ y ∈ Set.Icc Y X,
      (∑ p ∈ pool, ‖truncatedAuxiliarySmoothedSum (auxiliarySmoothedCoefficients (χ p i)) Z y‖ ^
        (2 : ℕ)) ≤ C * pool.card * y * Real.log (2 * y)) ∧
    (∀ u ∈ Set.Icc Y (2 * X),
      (∑ p ∈ pool, ‖auxiliaryPartialSum (auxiliarySmoothedCoefficients (χ p i)) u‖ ^
        (2 : ℕ)) ≤ C * pool.card * u * Real.log (2 * u))

/-- At sufficiently large left endpoints the sum of the truncated exceptional
counts over a fixed finite family fits into half of the exceptional budget. -/
theorem eventually_auxiliarySmoothedFamily_budget {τ C : ℝ} (hτ : 0 < τ) (hC : 0 ≤ C) (n : ℕ) :
    ∀ᶠ Y : ℝ in atTop,
      (n : ℝ) * (96 * (2 * C)) *
        (Y ^ (-2 * τ) * Real.log (2 * Y) / (1 - (4 : ℝ) ^ (-τ)) ^ (2 : ℕ)) ≤
        (1 / 2 : ℝ) * Y ^ (-τ) := by
  let D := (1 - (4 : ℝ) ^ (-τ)) ^ (2 : ℕ)
  have h4 : (4 : ℝ) ^ (-τ) < 1 := by
    rw [← Real.rpow_zero 4]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hD : 0 < D := pow_pos (sub_pos.mpr h4) _
  let K := (n : ℝ) * (96 * (2 * C)) / D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let k := (1 / 4 : ℝ) / (K + 1)
  have hk : 0 < k := by dsimp [k]; positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ), (isLittleO_log_rpow_atTop hτ).bound hk]
    with Y hY hlog
  have hY₀ : 0 < Y := by linarith
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hpow : 0 ≤ Y ^ τ := Real.rpow_nonneg hY₀.le _
  rw [Real.norm_of_nonneg hlogY, Real.norm_of_nonneg hpow] at hlog
  have hlog₂ : Real.log (2 * Y) ≤ 2 * Real.log Y := by
    rw [Real.log_mul (by norm_num) hY₀.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hY]
  have hKb : K * (2 * k) ≤ (1 / 2 : ℝ) := by
    have hpos : 0 < K + 1 := by positivity
    dsimp [k]
    rw [show K * (2 * (1 / 4 / (K + 1))) = (K / 2) / (K + 1) by ring]
    exact (div_le_iff₀ hpos).mpr (by linarith)
  have hh : K * Real.log (2 * Y) ≤ (1 / 2 : ℝ) * Y ^ τ := by
    calc
      _ ≤ K * (2 * Real.log Y) := mul_le_mul_of_nonneg_left hlog₂ hK
      _ ≤ K * (2 * (k * Y ^ τ)) := by gcongr
      _ = (K * (2 * k)) * Y ^ τ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKb hpow
  calc
    _ = Y ^ (-2 * τ) * (K * Real.log (2 * Y)) := by dsimp [K, D]; ring
    _ ≤ Y ^ (-2 * τ) * ((1 / 2 : ℝ) * Y ^ τ) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hY₀.le _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hY₀]
      ring_nf

/-- Combine the truncated exceptional sets for all characters with a common
exceptional set for the tails and any additional tests. -/
theorem auxiliarySmoothedFamily_exceptional_count {P ι : Type*} [Fintype ι]
    (pool badTail : Finset P) (χ : P → ι → BundledDirichletCharacter) (good : P → Prop)
    {Z : ℕ} {Y X τ C : ℝ} (hY : 1 ≤ Y) (hτ : 0 < τ) (hC : 0 ≤ C) (hZ : 2 * X ≤ Z)
    (hm : AuxiliarySmoothedMomentBounds pool χ Z Y X C)
    (hbudget : (Fintype.card ι : ℝ) * (96 * (2 * C)) *
        (Y ^ (-2 * τ) * Real.log (2 * Y) / (1 - (4 : ℝ) ^ (-τ)) ^ (2 : ℕ)) ≤
      (1 / 2 : ℝ) * Y ^ (-τ))
    (htailCard : (badTail.card : ℝ) ≤ (1 / 2 : ℝ) * Y ^ (-τ) * pool.card)
    (htail : ∀ p ∈ pool, p ∉ badTail → ∀ i : ι, ∀ y ∈ Set.Icc Y X,
      ‖complexSmoothedCharacterSum (χ p i) y -
        truncatedAuxiliarySmoothedSum (auxiliarySmoothedCoefficients (χ p i)) Z y‖ ≤
          (1 / 2 : ℝ) * y ^ (1 / 2 + τ))
    (hgood : ∀ p ∈ pool, p ∉ badTail → good p) :
    ((pool.filter fun p => ¬ ((∀ y ∈ Set.Icc Y X, ∀ i : ι,
      ‖complexSmoothedCharacterSum (χ p i) y‖ ≤ y ^ (1 / 2 + τ)) ∧ good p)).card : ℝ) ≤
      Y ^ (-τ) * pool.card := by
  let S (i : ι) (p : P) := truncatedAuxiliarySmoothedSum (auxiliarySmoothedCoefficients (χ p i)) Z
  let bad (i : ι) := pool.filter fun p => ∃ y ∈ Set.Icc Y X,
    (1 / 2 : ℝ) * y ^ (1 / 2 + τ) < ‖S i p y‖
  let E := Y ^ (-2 * τ) * Real.log (2 * Y) / (1 - (4 : ℝ) ^ (-τ)) ^ (2 : ℕ)
  have hsmall (i : ι) : (bad i).card ≤ 96 * (2 * C) * pool.card * E := by
    apply auxiliaryExceptional_truncated_window_bound pool
      (fun p => auxiliarySmoothedCoefficients (χ p i)) Z hY hτ (by positivity) hZ
    · intro p _
      simp [auxiliarySmoothedCoefficients]
    · intro y hy
      have hlog : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith [hY.trans hy.1])
      exact ((hm i).1 y hy).trans (by gcongr <;> linarith [hY.trans hy.1])
    · intro y hy
      have hy₁ := hY.trans hy.1
      have hy₀ : 0 < y := by linarith
      have hlog : Real.log (4 * y) ≤ 2 * Real.log (2 * y) := by
        rw [show 4 * y = 2 * (2 * y) by ring, Real.log_mul (by norm_num) (by positivity)]
        linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * y)]
      refine (auxiliaryBlockEnergy_sum_le_of_partial_moment pool
        (fun p => auxiliarySmoothedCoefficients (χ p i)) hy₁ hC
        (fun u hu => (hm i).2 u ⟨hy.1.trans hu.1, hu.2.trans (by linarith [hy.2])⟩)).trans ?_
      calc
        _ ≤ (C * pool.card) * (2 * Real.log (2 * y)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = _ := by ring
  let BT := Finset.univ.biUnion bad
  have hBT : (BT.card : ℝ) ≤ (1 / 2 : ℝ) * Y ^ (-τ) * pool.card := by
    calc
      _ ≤ ∑ i : ι, ((bad i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _ : ι, (96 * (2 * C) * pool.card * E) := Finset.sum_le_sum (fun i _ => hsmall i)
      _ = ((Fintype.card ι : ℝ) * (96 * (2 * C)) * E) * pool.card := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)
  have hsub : (pool.filter fun p => ¬ ((∀ y ∈ Set.Icc Y X, ∀ i : ι,
      ‖complexSmoothedCharacterSum (χ p i) y‖ ≤ y ^ (1 / 2 + τ)) ∧ good p)) ⊆ BT ∪ badTail := by
    intro p hp
    obtain ⟨hpp, hpbad⟩ := Finset.mem_filter.mp hp
    by_contra h
    have hmem := Finset.notMem_union.mp h
    apply hpbad
    refine ⟨?_, hgood p hpp hmem.2⟩
    intro y hy i
    have hs : ‖S i p y‖ ≤ (1 / 2 : ℝ) * y ^ (1 / 2 + τ) := by
      by_contra! hlarge
      exact hmem.1 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨hpp, y, hy, hlarge⟩⟩)
    calc
      _ ≤ ‖complexSmoothedCharacterSum (χ p i) y - S i p y‖ + ‖S i p y‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ _ := by linarith only [htail p hpp hmem.2 i y hy, hs]
  calc
    _ ≤ ((BT ∪ badTail).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (BT.card : ℝ) + badTail.card := by exact_mod_cast Finset.card_union_le _ _
    _ ≤ _ := by linarith only [hBT, htailCard]

end Riemann
