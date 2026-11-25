module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open scoped BigOperators

namespace Utilities

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*}
  [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]

/-- A ball of this radius can contain only one integer in `[1, Z]`.
A second integer would give a nonzero difference divisible by a
power of `p` larger than the interval. -/
theorem nat_eq_of_near_padic_root {s : K} {Z a b : ℕ}
    (ha : a ∈ Finset.Icc 1 Z) (hb : b ∈ Finset.Icc 1 Z)
    (hsa : ‖s - (a : K)‖ < (p : ℝ) ^ (-(Nat.log p Z : ℤ)))
    (hsb : ‖s - (b : K)‖ < (p : ℝ) ^ (-(Nat.log p Z : ℤ))) : a = b := by
  by_contra hab
  let d : ℤ := (a : ℤ) - b
  let k := Nat.log p Z
  have hd : d ≠ 0 := by dsimp [d]; omega
  have hnorm : ‖(d : ℚ_[p])‖ < (p : ℝ) ^ (-(k : ℤ)) := by
    have heq : algebraMap ℚ_[p] K (d : ℚ_[p]) = (s - b) + -(s - a) := by
      rw [map_intCast]
      push_cast [d]
      ring
    rw [← norm_algebraMap' K, heq]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (by rw [norm_neg]; exact max_lt hsb hsa)
  have hd' : (d : ℚ_[p]) ≠ 0 := by exact_mod_cast hd
  have hp' : 1 < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hd'] at hnorm
  have hvaluation := (zpow_lt_zpow_iff_right₀ hp').mp hnorm
  have hpow : ‖(d : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hd']
    apply zpow_le_zpow_right₀ hp'.le
    push_cast
    omega
  have hdvd := (Padic.norm_int_le_pow_iff_dvd d (k + 1)).mp hpow
  have habs : d.natAbs ≤ Z := by
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    dsimp [d]
    omega
  apply hd
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_
  simpa only [Int.natAbs_pow, Int.natAbs_natCast] using
    habs.trans_lt (Nat.lt_pow_succ_log_self hp.out.one_lt Z)

/-- At most one twist per root has integer distance below the radius.
Outside their union all the root distances meet the common lower bound. -/
theorem exists_padic_twist_exceptions {ι : Type*} [Fintype ι] (roots : ι → K) (Z : ℕ) :
    ∃ exc : Finset ℕ, exc.card ≤ Fintype.card ι ∧
      ∀ i ∈ Finset.Icc 1 Z, i ∉ exc → ∀ a,
        (p : ℝ) ^ (-(Nat.log p Z : ℤ)) ≤ ‖roots a - (i : K)‖ := by
  classical
  let near (a : ι) : Finset ℕ := (Finset.Icc 1 Z).filter fun i =>
    ‖roots a - (i : K)‖ < (p : ℝ) ^ (-(Nat.log p Z : ℤ))
  have hnear (a : ι) : (near a).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    exact nat_eq_of_near_padic_root (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  refine ⟨Finset.univ.biUnion near, ?_, ?_⟩
  · calc
      _ ≤ ∑ a : ι, (near a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a : ι, 1 := Finset.sum_le_sum fun a _ => hnear a
      _ = Fintype.card ι := by simp
  · intro i hi hnot a
    refine le_of_not_gt fun hlt => hnot ?_
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, Finset.mem_filter.mpr ⟨hi, hlt⟩⟩

end Utilities
