module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

open scoped BigOperators ComplexConjugate

namespace Utilities

/-- Bounding each covariance of a finite family gives a bound on the
sum of squared norms of any common linear combination of that family. -/
theorem sum_norm_sum_mul_sq_le_covariance
    {I P : Type*} (primes : Finset P) (indices : Finset I)
    (coefficient : I → ℂ) (symbol : P → I → ℂ) (covBound : I → I → ℝ)
    (hcov : ∀ n ∈ indices, ∀ m ∈ indices,
      ‖∑ q ∈ primes, symbol q n * conj (symbol q m)‖ ≤ covBound n m) :
    (∑ q ∈ primes, ‖∑ n ∈ indices, coefficient n * symbol q n‖ ^ (2 : ℕ)) ≤
      ∑ n ∈ indices, ∑ m ∈ indices, ‖coefficient n‖ * ‖coefficient m‖ * covBound n m := by
  let S (q : P) := ∑ n ∈ indices, coefficient n * symbol q n
  let F (q : P) (n m : I) :=
    (coefficient n * conj (coefficient m)) * (symbol q n * conj (symbol q m))
  let V := ∑ q ∈ primes, ‖S q‖ ^ (2 : ℕ)
  have hV : 0 ≤ V := Finset.sum_nonneg fun q _ => sq_nonneg ‖S q‖
  have hsq (q : P) : ((‖S q‖ ^ (2 : ℕ) : ℝ) : ℂ) = ∑ n ∈ indices, ∑ m ∈ indices, F q n m := by
    rw [Complex.sq_norm, ← Complex.mul_conj]
    simp only [S, map_sum, map_mul]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by dsimp [F]; ring
  have hexpand : (V : ℂ) = ∑ n ∈ indices, ∑ m ∈ indices,
      (coefficient n * conj (coefficient m)) * (∑ q ∈ primes, symbol q n * conj (symbol q m)) := by
    calc
      _ = ∑ q ∈ primes, ∑ n ∈ indices, ∑ m ∈ indices, F q n m := by
        unfold V
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun q _ => hsq q
      _ = ∑ n ∈ indices, ∑ m ∈ indices, ∑ q ∈ primes, F q n m := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := by simp only [F, Finset.mul_sum]
  change V ≤ _
  calc
    V = ‖(V : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hV]
    _ ≤ ∑ n ∈ indices, ∑ m ∈ indices,
        ‖(coefficient n * conj (coefficient m)) * (∑ q ∈ primes, symbol q n * conj (symbol q m))‖ := by
      rw [hexpand]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hcov n hn m hm) (by positivity)

/-- Finite Markov's inequality for a weight which is at least one on
each marked member of the pool. -/
theorem card_marked_le_sum_weights {P : Type*} (pool : Finset P)
    (marked : P → Prop) [DecidablePred marked] (w : P → ℝ)
    (h₀ : ∀ q ∈ pool, 0 ≤ w q) (h₁ : ∀ q ∈ pool, marked q → 1 ≤ w q) :
    ((pool.filter marked).card : ℝ) ≤ ∑ q ∈ pool, w q := by
  calc
    _ = ∑ _q ∈ pool.filter marked, (1 : ℝ) := by simp
    _ ≤ ∑ q ∈ pool.filter marked, w q := by
      apply Finset.sum_le_sum
      intro q hq
      exact h₁ q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      exact fun q hq _ => h₀ q hq

end Utilities
