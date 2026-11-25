module

public import Utilities.GeneralizedBernoulli
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

@[expose] public section

open PowerSeries

namespace Utilities

private noncomputable def bernoulliSeries (N a : ℕ) : ℚ⟦X⟧ :=
  mk fun k => generalizedBernoulliCoefficient N k a / (k.factorial : ℚ)

private theorem bernoulliSeries_mul_exp_sub_one {N : ℕ} (hN : 0 < N) (a : ℕ) :
    bernoulliSeries N a * (rescale (N : ℚ) (exp ℚ) - 1) = X * rescale (a : ℚ) (exp ℚ) := by
  let t : ℚ := a / (N : ℚ)
  let P : ℚ⟦X⟧ := mk fun k => Polynomial.aeval t ((1 / k.factorial : ℚ) • Polynomial.bernoulli k)
  have hNr : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have ht : t * N = a := div_mul_cancel₀ _ hNr
  have hcoeff : bernoulliSeries N a = C ((N : ℚ)⁻¹) * rescale (N : ℚ) P := by
    ext k
    simp only [bernoulliSeries, P, t, coeff_mk, coeff_C_mul, coeff_rescale, map_smul,
      Polynomial.coe_aeval_eq_eval, smul_eq_mul, generalizedBernoulliCoefficient,
      zpow_sub_one₀ hNr, zpow_natCast]
    ring
  have h := congrArg (rescale (N : ℚ)) (Polynomial.bernoulli_generating_function t)
  change rescale (N : ℚ) (P * (exp ℚ - 1)) = rescale (N : ℚ) (X * rescale t (exp ℚ)) at h
  rw [map_mul, map_sub, map_one, map_mul, rescale_X, rescale_rescale, ht] at h
  rw [hcoeff, mul_assoc, h, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hNr, map_one, one_mul]

/-- Bernoulli distribution across the residue classes above `a` at a multiple of the level. -/
theorem generalizedBernoulliCoefficient_distribution {N m : ℕ}
    (hN : 0 < N) (hm : 0 < m) (k a : ℕ) :
    generalizedBernoulliCoefficient N k a =
      ∑ j ∈ Finset.range m, generalizedBernoulliCoefficient (N * m) k (a + j * N) := by
  let E : ℚ⟦X⟧ := rescale (N : ℚ) (exp ℚ)
  let Em : ℚ⟦X⟧ := rescale ((N * m : ℕ) : ℚ) (exp ℚ)
  have hpow (j : ℕ) : E ^ j = rescale ((j * N : ℕ) : ℚ) (exp ℚ) := by
    dsimp only [E]
    rw [← map_pow, exp_pow_eq_rescale_exp, rescale_rescale, Nat.cast_mul]
  have hEm : Em = E ^ m := by
    dsimp only [Em]
    rw [hpow, Nat.mul_comm m N]
  have hEnz : Em - 1 ≠ 0 := by
    intro h
    have hcoeff := congrArg (coeff (R := ℚ) 1) h
    simp [Em, coeff_rescale, coeff_exp, coeff_one] at hcoeff
    exact hcoeff.elim hN.ne' hm.ne'
  have hleft : bernoulliSeries N a * (Em - 1) =
      X * rescale (a : ℚ) (exp ℚ) * (∑ j ∈ Finset.range m, E ^ j) := by
    rw [hEm, ← geom_sum_mul, mul_comm _ (E - 1), ← mul_assoc]
    rw [bernoulliSeries_mul_exp_sub_one hN a]
  have hright : (∑ j ∈ Finset.range m, bernoulliSeries (N * m) (a + j * N)) *
      (Em - 1) = X * rescale (a : ℚ) (exp ℚ) * (∑ j ∈ Finset.range m, E ^ j) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [bernoulliSeries_mul_exp_sub_one (Nat.mul_pos hN hm), mul_assoc, hpow,
      exp_mul_exp_eq_exp_add, Nat.cast_add]
  have hseries := mul_right_cancel₀ hEnz (hleft.trans hright.symm)
  have h := congrArg (coeff (R := ℚ) k) hseries
  simp only [bernoulliSeries, coeff_mk, map_sum, ← Finset.sum_div] at h
  exact (div_left_inj₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))).mp h

end Utilities
