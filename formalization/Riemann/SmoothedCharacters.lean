module

public import Riemann.SmoothedSums
public import Utilities.DirichletCharacter
import Utilities.SmoothedMangoldtMellin

@[expose] public section

open Utilities
open scoped BigOperators ComplexConjugate

namespace Riemann

/-- The complex smoothed sum whose real part is Gχ in (2.2) for a nontrivial χ. -/
noncomputable def complexSmoothedCharacterSum (χ : BundledDirichletCharacter) (x : ℝ) : ℂ :=
  let L := DirichletCharacter.LFunction χ.character
  smoothedTwist (fun n => χ.character (n : ZMod (χ.modulus : ℕ))) (logDeriv L 1) x

theorem complexSmoothedCharacterSum_inv_eq_conj (χ : BundledDirichletCharacter)
    (hχ : χ.character ≠ 1) (x : ℝ) :
    complexSmoothedCharacterSum ⟨χ.modulus, χ.character⁻¹⟩ x = conj (complexSmoothedCharacterSum χ x) := by
  unfold complexSmoothedCharacterSum smoothedTwist
  dsimp only
  rw [logDeriv_dirichletLFunction_inv_at_one χ.character hχ, map_add, map_mul, Complex.conj_ofReal]
  congr 1
  unfold smoothedMangoldt
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul, Complex.conj_ofReal, ← Complex.star_def, MulChar.star_apply']

noncomputable def smoothedCombination {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ) (x : ℝ) : ℝ :=
  smoothedZetaSum x + ∑ i, weight i * (complexSmoothedCharacterSum (family i) x).re

theorem continuous_complexSmoothedCharacterSum (χ : BundledDirichletCharacter) :
    Continuous (complexSmoothedCharacterSum χ) := continuous_smoothedTwist _ _

theorem continuous_smoothedCombination {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ) :
    Continuous (smoothedCombination family weight) :=
  continuous_smoothedZetaSum.add (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Complex.continuous_re.comp (continuous_complexSmoothedCharacterSum (family i))))

private theorem abs_zetaCorrection_le_rpow {a x : ℝ} (ha : 1 < a) (hx : 1 ≤ x) :
    |zetaCorrection x| ≤ (1 / (a - 1) + |1 + Real.eulerMascheroniConstant|) * x ^ a := by
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hxPower : x ≤ x ^ a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx ha.le
  have hlog : x * Real.log x ≤ (1 / (a - 1)) * x ^ a := by
    calc
      _ ≤ x * (x ^ (a - 1) / (a - 1)) := mul_le_mul_of_nonneg_left
        (Real.log_le_rpow_div hx₀ (sub_pos.mpr ha)) hx₀
      _ = (x ^ (1 : ℝ) * x ^ (a - 1)) / (a - 1) := by rw [Real.rpow_one, mul_div_assoc]
      _ = _ := by rw [← Real.rpow_add hxPos, show 1 + (a - 1) = a by ring]; ring
  calc
    |zetaCorrection x| ≤ |-(x * Real.log x)| + |(1 + Real.eulerMascheroniConstant) * x| := by
      simpa only [zetaCorrection, neg_mul] using
        abs_add_le (-(x * Real.log x)) ((1 + Real.eulerMascheroniConstant) * x)
    _ = x * Real.log x + |1 + Real.eulerMascheroniConstant| * x := by
      rw [abs_neg, abs_of_nonneg (mul_nonneg hx₀ (Real.log_nonneg hx)), abs_mul, abs_of_nonneg hx₀]
    _ ≤ (1 / (a - 1)) * x ^ a + |1 + Real.eulerMascheroniConstant| * x ^ a :=
      add_le_add hlog (mul_le_mul_of_nonneg_left hxPower (abs_nonneg _))
    _ = _ := by rw [add_mul]

theorem abs_smoothedZetaSum_le_rpow {a : ℝ} (ha : 1 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, |smoothedZetaSum x| ≤ B * x ^ a := by
  obtain ⟨B, hB, hsum⟩ := norm_smoothedMangoldt_le_rpow (fun _ => 1) (by simp) ha
  let correction := 1 / (a - 1) + |1 + Real.eulerMascheroniConstant|
  have hcorrection : 0 ≤ correction := add_nonneg (div_nonneg zero_le_one (sub_nonneg.mpr ha.le)) (abs_nonneg _)
  refine ⟨B + correction, add_nonneg hB hcorrection, fun x hx => ?_⟩
  calc
    _ ≤ |(smoothedMangoldt (fun _ => 1) x).re| + |zetaCorrection x| := abs_add_le _ _
    _ ≤ B * x ^ a + correction * x ^ a := add_le_add
      ((Complex.abs_re_le_norm _).trans (hsum x hx)) (abs_zetaCorrection_le_rpow ha hx)
    _ = _ := by dsimp only [correction]; ring

theorem norm_complexSmoothedCharacterSum_le_rpow (χ : BundledDirichletCharacter) {a : ℝ}
    (ha : 1 < a) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, ‖complexSmoothedCharacterSum χ x‖ ≤ B * x ^ a := by
  let coefficient (n : ℕ) := χ.character (n : ZMod (χ.modulus : ℕ))
  let D := logDeriv (DirichletCharacter.LFunction χ.character) 1
  obtain ⟨B, hB, hsum⟩ := norm_smoothedMangoldt_le_rpow coefficient (fun n => χ.character.norm_le_one _) ha
  refine ⟨B + ‖D‖, add_nonneg hB (norm_nonneg _), fun x hx => ?_⟩
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hxPower : x ≤ x ^ a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx ha.le
  calc
    _ ≤ ‖smoothedMangoldt coefficient x‖ + ‖D * (x : ℂ)‖ := norm_add_le _ _
    _ = ‖smoothedMangoldt coefficient x‖ + ‖D‖ * x := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx₀]
    _ ≤ B * x ^ a + ‖D‖ * x ^ a := add_le_add (hsum x hx)
      (mul_le_mul_of_nonneg_left hxPower (norm_nonneg _))
    _ = _ := by rw [add_mul]

end Riemann
