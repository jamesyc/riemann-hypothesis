module

public import Utilities.CyclotomicLayer
public import Utilities.RootDiscriminant
import Mathlib.Algebra.Algebra.Hom.Rat

@[expose] public section

namespace Utilities

/-- The absolute degree is bounded at a fixed relative depth. When the
base embeds at modulus `N * P`, the logarithmic discriminant bound grows
only as `1 + log P`, with constant independent of `P`. -/
theorem exists_primePowerCyclotomicLayer_discriminant_bound
    (p j nBase N : ℕ) (hp : p.Prime) (hN : 0 < N) :
    ∃ (n : ℕ) (D : ℝ), 0 ≤ D ∧
      ∀ (P : ℕ), 0 < P →
        ∀ (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L],
          Module.finrank ℚ F ≤ nBase → (F →ₐ[ℚ] CyclotomicField (N * P) ℚ) →
          IsPrimePowerCyclotomicLayer p j F L →
          Module.finrank ℚ L ≤ n ∧
          Real.log (2 * ((NumberField.discr L).natAbs : ℝ)) ≤ D * (1 + Real.log (P : ℝ)) := by
  let n := (nBase + 1) * p ^ j
  have hn : 0 < n := mul_pos (by omega) (pow_pos hp.pos j)
  let C := (2 : ℝ) * n * N
  have hC₁ : 1 ≤ C := by
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [C]
    nlinarith only [mul_le_mul hn₁ hN₁ (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
  have hlogC := Real.log_nonneg hC₁
  have hlog₂ := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  let D := Real.log 2 + (n : ℝ) * (Real.log C + 1)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨n, D, hD, ?_⟩
  intro P hP F L _ _ _ _ _ hF f hLayer
  let _ : IsScalarTower ℚ F L :=
    IsScalarTower.of_algebraMap_eq' (algebraMap F L).toRatAlgHom.comp_algebraMap.symm
  have hd : Module.finrank ℚ L ≤ n := by
    rw [← Module.finrank_mul_finrank ℚ F L, hLayer.1]
    exact Nat.mul_le_mul_right _ (hF.trans (Nat.le_succ _))
  refine ⟨hd, ?_⟩
  obtain ⟨M, hM, hMle, ⟨g⟩⟩ := hLayer.exists_cyclotomic_embedding hp (mul_pos hN hP) f
  have hMle' : (M : ℝ) ≤ C * P := by
    have h := hMle.trans (Nat.mul_le_mul_right (N * P) (Nat.mul_le_mul_left 2 hd))
    dsimp only [C]
    rw [mul_assoc (2 * (n : ℝ)) (N : ℝ) (P : ℝ)]
    exact_mod_cast h
  have hP₀ : (0 : ℝ) < P := by exact_mod_cast hP
  have hP₁ : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hM₀ : (0 : ℝ) < M := by exact_mod_cast hM
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogP := Real.log_nonneg hP₁
  have hlogM := Real.log_nonneg hM₁
  have hlog : Real.log (M : ℝ) ≤ Real.log C + Real.log (P : ℝ) := by
    rw [← Real.log_mul (zero_lt_one.trans_le hC₁).ne' hP₀.ne']
    exact Real.log_le_log hM₀ hMle'
  have hdiscr : 0 < ((NumberField.discr L).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)
  have hdiscr_le : ((NumberField.discr L).natAbs : ℝ) ≤ (M : ℝ) ^ Module.finrank ℚ L := by
    exact_mod_cast natAbs_discr_le_pow_of_cyclotomic_embedding L M hM g
  have hdiscr_log := Real.log_le_log hdiscr hdiscr_le
  rw [Real.log_pow] at hdiscr_log
  rw [Real.log_mul (by norm_num) hdiscr.ne']
  have hd' : (Module.finrank ℚ L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hd
  have hprod := (mul_le_mul_of_nonneg_right hd' hlogM).trans
    (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n))
  have hconstant : 0 ≤ Real.log 2 + (n : ℝ) * Real.log C := by positivity
  dsimp only [D]
  nlinarith only [hdiscr_log, hprod, mul_nonneg hconstant hlogP, Nat.cast_nonneg (α := ℝ) n]

end Utilities
