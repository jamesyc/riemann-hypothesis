module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.Integral

@[expose] public section

open scoped BigOperators

namespace Utilities

/-- Algebraic integers lie in the unit ball of a nonarchimedean normed field. -/
theorem norm_le_one_of_isIntegral_int {K : Type*} [NormedField K] [IsUltrametricDist K]
    {x : K} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  let v := NormedField.valuation (K := K)
  have h := (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp
    (hx.tower_top (A := v.integer))
  exact (NNReal.coe_le_coe.mpr h : (↑‖x‖₊ : ℝ) ≤ ↑(1 : NNReal))

/-- Convert the norm of an integer in the p-adic algebraic closure into its
weighted integer p-adic valuation. -/
theorem neg_log_norm_intCast_padicAlgCl (ℓ : ℕ) [Fact ℓ.Prime]
    (m : ℤ) (hm : m ≠ 0) :
    -Real.log ‖(m : PadicAlgCl ℓ)‖ = (padicValInt ℓ m : ℝ) * Real.log ℓ := by
  have hcast : (m : PadicAlgCl ℓ) = ((m : ℚ_[ℓ]) : PadicAlgCl ℓ) :=
    (map_intCast (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)) m).symm
  rw [hcast, PadicAlgCl.norm_extends, Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hm),
    Padic.valuation_intCast, Real.log_zpow]
  push_cast
  ring

/-- The valuation contribution of a selected part of an integer product is
bounded by the integer's prime multiplicity if the discarded factors have
norm at most one. The values are the normalized p-adic valuations. -/
theorem sum_neg_logb_norm_le_factorization_of_prod
    {p : ℕ} [Fact p.Prime] {I : Type*} [Fintype I]
    (f : I → PadicAlgCl p) (n : ℤ) (hn : n ≠ 0)
    (hf : ∏ i, f i = (n : PadicAlgCl p))
    (s : Finset I) (hsmall : ∀ i ∉ s, ‖f i‖ ≤ 1) :
    ∑ i ∈ s, -Real.logb (p : ℝ) ‖f i‖ ≤ (n.natAbs.factorization p : ℝ) := by
  classical
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hn' : (n : PadicAlgCl p) ≠ 0 := by exact_mod_cast hn
  have hne : ∀ i, f i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mp (hf ▸ hn') i (Finset.mem_univ _)
  have hnorm : Real.logb (p : ℝ) ‖(n : PadicAlgCl p)‖ = -(padicValInt p n : ℝ) := by
    rw [Real.logb]
    apply (div_eq_iff (Real.log_pos hp).ne').2
    linarith only [neg_log_norm_intCast_padicAlgCl p n hn]
  have hprod : ‖(n : PadicAlgCl p)‖ ≤ ∏ i ∈ s, ‖f i‖ := by
    rw [← hf, norm_prod, ← Finset.prod_sdiff s.subset_univ]
    have hsdiff : ∏ i ∈ Finset.univ \ s, ‖f i‖ ≤ 1 := by
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i hi =>
        hsmall i (Finset.mem_sdiff.mp hi).2
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => norm_nonneg _) hsdiff
  have hl := Real.logb_le_logb_of_le hp (norm_pos_iff.mpr hn') hprod
  rw [hnorm, Real.logb_prod _ _ (fun i _ => norm_ne_zero_iff.mpr (hne i))] at hl
  rw [Finset.sum_neg_distrib, Nat.factorization_def _ (Fact.out : p.Prime)]
  change _ ≤ (padicValInt p n : ℝ)
  linarith

end Utilities
