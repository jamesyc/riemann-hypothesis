module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.VecNotation

@[expose] public section

open scoped BigOperators

namespace Utilities

/-- A function that preserves every vanishing relation of another function
is proportional to it if it is nonzero somewhere. -/
theorem exists_scalar_of_linearRelationTransfer {X : Type*} {K : Type*} [Field K]
    (period μ : X → K)
    (ht : ∀ n (x : Fin n → X) (a : Fin n → K),
      (∑ i, a i * period (x i)) = 0 → (∑ i, a i * μ (x i)) = 0)
    {x₀ : X} (hμ : μ x₀ ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ x, μ x = c * period x := by
  have hperiodValue : period x₀ ≠ 0 := by
    intro h
    exact hμ (by simpa using ht 1 ![x₀] ![1] (by simp [h]))
  refine ⟨μ x₀ / period x₀, div_ne_zero hμ hperiodValue, fun x => ?_⟩
  have hzero := ht 2 ![x₀, x] ![period x, -period x₀] (by simp [Fin.sum_univ_two, mul_comm])
  have heq : period x * μ x₀ = period x₀ * μ x := by
    simpa [Fin.sum_univ_two, ← sub_eq_add_neg, sub_eq_zero] using hzero
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hperiodValue).mpr
  exact (mul_comm (μ x) (period x₀)).trans (heq.symm.trans (mul_comm _ _))

end Utilities
