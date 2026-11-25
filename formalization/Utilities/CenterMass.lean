module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.Real.Basic

@[expose] public section

open scoped BigOperators

namespace Utilities

theorem centerMass_mono_real {U : Type*} {indices : Finset U} {weight f g : U → ℝ}
    (hweight : ∀ u ∈ indices, 0 ≤ weight u) (hle : ∀ u ∈ indices, f u ≤ g u) :
    indices.centerMass weight f ≤ indices.centerMass weight g := by
  simp only [Finset.centerMass, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hle u hu) (hweight u hu))
    (inv_nonneg.mpr (Finset.sum_nonneg hweight))

theorem const_le_centerMass_real {U : Type*} {indices : Finset U} {weight f : U → ℝ}
    {a : ℝ} (hweight : ∀ u ∈ indices, 0 ≤ weight u)
    (hsum : (∑ u ∈ indices, weight u) ≠ 0) (hle : ∀ u ∈ indices, a ≤ f u) :
    a ≤ indices.centerMass weight f := by
  rw [← indices.centerMass_const hsum a]
  exact centerMass_mono_real hweight hle

theorem centerMass_le_const_real {U : Type*} {indices : Finset U} {weight f : U → ℝ}
    {a : ℝ} (hweight : ∀ u ∈ indices, 0 ≤ weight u)
    (hsum : (∑ u ∈ indices, weight u) ≠ 0) (hle : ∀ u ∈ indices, f u ≤ a) :
    indices.centerMass weight f ≤ a := by
  rw [← indices.centerMass_const hsum a]
  exact centerMass_mono_real hweight hle

end Utilities
