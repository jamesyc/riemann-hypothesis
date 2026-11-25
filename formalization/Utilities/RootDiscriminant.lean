module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

@[expose] public section

open scoped NumberField

namespace Utilities

theorem one_le_rootDiscr (K : Type*) [Field K] [NumberField K] :
    1 ≤ NumberField.rootDiscr K := by
  rw [NumberField.rootDiscr_def]
  apply Real.one_le_rpow _ (by positivity)
  exact_mod_cast (Int.one_le_abs (NumberField.discr_ne_zero K))

/-- The absolute discriminant of a cyclotomic subfield is at most the
modulus raised to the subfield degree. -/
theorem natAbs_discr_le_pow_of_cyclotomicSubfield (n : ℕ) [NeZero n]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]
    (K : IntermediateField ℚ L) :
    (NumberField.discr K).natAbs ≤ n ^ Module.finrank ℚ K := by
  have hL : (NumberField.discr L).natAbs ≤ n ^ Module.finrank ℚ L := by
    rw [IsCyclotomicExtension.Rat.finrank n L, IsCyclotomicExtension.Rat.natAbs_discr n L]
    exact Nat.div_le_self _ _
  have hdiv := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    K (𝓞 K) L (𝓞 L)
  have hpos : 0 < (NumberField.discr L).natAbs :=
    Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)
  have hp : 0 < Module.finrank K L := Module.finrank_pos
  have hpow : (NumberField.discr K).natAbs ^ Module.finrank K L ≤
      (n ^ Module.finrank ℚ K) ^ Module.finrank K L := by
    rw [← pow_mul, Module.finrank_mul_finrank ℚ K L]
    exact (Nat.le_of_dvd hpos ⟨_, hdiv.trans (mul_comm _ _)⟩).trans hL
  exact le_of_not_gt fun hgt => (Nat.pow_lt_pow_left hgt hp.ne').not_ge hpow

/-- The root discriminant is at most the cyclotomic modulus for every
number field contained in the cyclotomic field. -/
theorem rootDiscr_le_cyclotomicModulus (n : ℕ) [NeZero n]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]
    (K : IntermediateField ℚ L) : NumberField.rootDiscr K ≤ n := by
  have hK := natAbs_discr_le_pow_of_cyclotomicSubfield n L K
  have hdeg : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hK' : ((NumberField.discr K).natAbs : ℝ) ≤ (n : ℝ) ^ Module.finrank ℚ K := by
    exact_mod_cast hK
  rw [NumberField.rootDiscr_def, Int.abs_eq_natAbs, Int.cast_natCast]
  calc
    _ ≤ ((n : ℝ) ^ Module.finrank ℚ K) ^ (Module.finrank ℚ K : ℝ)⁻¹ :=
      Real.rpow_le_rpow (by positivity) hK' (inv_nonneg.mpr hdeg.le)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
        mul_inv_cancel₀ hdeg.ne', Real.rpow_one]

/-- A cyclotomic embedding bounds the absolute discriminant by the modulus
to the field degree. -/
theorem natAbs_discr_le_pow_of_cyclotomic_embedding (E : Type*) [Field E] [NumberField E]
    (N : ℕ) (hN : 0 < N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) :
    (NumberField.discr E).natAbs ≤ N ^ Module.finrank ℚ E := by
  let K := CyclotomicField N ℚ
  let _ : NeZero N := ⟨hN.ne'⟩
  let _ : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  let _ : IsCyclotomicExtension {N} ℚ K := CyclotomicField.isCyclotomicExtension N ℚ
  let _ : NumberField K := IsCyclotomicExtension.numberField {N} ℚ K
  let F := j.fieldRange
  let e : E ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField j
  rw [NumberField.discr_eq_discr_of_algEquiv E e, e.toLinearEquiv.finrank_eq]
  exact natAbs_discr_le_pow_of_cyclotomicSubfield N K F

end Utilities
