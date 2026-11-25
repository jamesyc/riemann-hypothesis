module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

open scoped BigOperators
open Finset

namespace Utilities

private theorem sum_inv_distance_le_harmonic {n : ℕ} (i : Fin n) :
    (∑ j ∈ Ioi i, ((j.val - i.val : ℕ) : ℝ)⁻¹) ≤ (harmonic n : ℝ) := by
  classical
  let shift (j : Fin n) := j.val - i.val
  have hinj : Set.InjOn shift (Ioi i : Set (Fin n)) := by
    intro j hj k hk h
    simp only [coe_Ioi, Set.mem_Ioi] at hj hk
    have hj' : i.val < j.val := hj
    have hk' : i.val < k.val := hk
    apply Fin.ext
    dsimp [shift] at h
    omega
  have hsub : (Ioi i).image shift ⊆ Icc 1 n := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
    have hl : i < j := mem_Ioi.mp hj
    have hj' : i.val < j.val := hl
    have hj'' := j.isLt
    exact mem_Icc.mpr ⟨by dsimp [shift]; omega, by dsimp [shift]; omega⟩
  calc
    _ = ∑ k ∈ (Ioi i).image shift, (k : ℝ)⁻¹ := (sum_image hinj).symm
    _ ≤ ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity
    _ = _ := by simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv]

/-- Interlacing an increasing tuple with an arithmetic progression increases
the log Vandermonde determinant by at most one harmonic sum per row. -/
theorem log_det_vandermonde_interlaced_grid_le {n : ℕ} {start step : ℝ}
    (hstep : 0 < step) (u : Fin n → ℝ) (hu : StrictMono u)
    (hlower : ∀ i, start + step * i.val ≤ u i)
    (hupper : ∀ i, u i ≤ start + step * ((i.val : ℝ) + 1)) :
    Real.log (Matrix.vandermonde u).det ≤
      Real.log (Matrix.vandermonde (fun i : Fin n => start + step * i.val)).det +
        n * (1 + Real.log n) := by
  let v (i : Fin n) := start + step * i.val
  have hv : StrictMono v := fun i j hij => by
    dsimp [v]
    have hcast : (i.val : ℝ) < (j.val : ℝ) := by
      exact Nat.cast_lt.mpr (show i.val < j.val from hij)
    exact add_lt_add_right (mul_lt_mul_of_pos_left hcast hstep) _
  have hdet (f : Fin n → ℝ) (h : StrictMono f) :
      Real.log (Matrix.vandermonde f).det =
        ∑ i : Fin n, ∑ j ∈ Ioi i, Real.log (f j - f i) := by
    rw [Matrix.det_vandermonde, Real.log_prod]
    · apply sum_congr rfl
      intro i _
      exact Real.log_prod fun j hj => (sub_pos.mpr (h (mem_Ioi.mp hj))).ne'
    · intro i _
      exact (prod_pos fun j hj => sub_pos.mpr (h (mem_Ioi.mp hj))).ne'
  have hpoint (i j : Fin n) (hij : i < j) :
      Real.log (u j - u i) ≤ Real.log (v j - v i) + ((j.val - i.val : ℕ) : ℝ)⁻¹ := by
    have hd : 0 < ((j.val - i.val : ℕ) : ℝ) := by
      exact_mod_cast (Nat.sub_pos_of_lt (show i.val < j.val from hij))
    have hd' : ((j.val - i.val : ℕ) : ℝ) = (j.val : ℝ) - i.val := by
      exact Nat.cast_sub (show i.val ≤ j.val from hij.le)
    have hgrid : v j - v i = step * ((j.val - i.val : ℕ) : ℝ) := by
      dsimp [v]
      rw [hd']
      ring
    have hdiff := sub_pos.mpr (hu hij)
    have hvdiff := sub_pos.mpr (hv hij)
    have hr : (u j - u i) / (v j - v i) ≤ 1 + ((j.val - i.val : ℕ) : ℝ)⁻¹ := by
      apply (div_le_iff₀ hvdiff).mpr
      rw [hgrid, show (1 + ((j.val - i.val : ℕ) : ℝ)⁻¹) *
          (step * ((j.val - i.val : ℕ) : ℝ)) =
          step * (((j.val - i.val : ℕ) : ℝ) + 1) by field_simp, hd']
      linarith [hlower i, hupper j]
    have hlog := Real.log_le_sub_one_of_pos (div_pos hdiff hvdiff)
    rw [Real.log_div hdiff.ne' hvdiff.ne'] at hlog
    linarith
  change Real.log (Matrix.vandermonde u).det ≤ Real.log (Matrix.vandermonde v).det + _
  rw [hdet _ hu, hdet _ hv]
  calc
    _ ≤ ∑ i : Fin n, (∑ j ∈ Ioi i, Real.log (v j - v i) + (harmonic n : ℝ)) := by
      apply sum_le_sum
      intro i _
      calc
        _ ≤ ∑ j ∈ Ioi i, (Real.log (v j - v i) + ((j.val - i.val : ℕ) : ℝ)⁻¹) :=
          sum_le_sum fun j hj => hpoint i j (mem_Ioi.mp hj)
        _ ≤ _ := by rw [sum_add_distrib]; exact add_le_add_right (sum_inv_distance_le_harmonic i) _
    _ ≤ _ := by
      rw [sum_add_distrib]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      gcongr
      exact harmonic_le_one_add_log n

/-- The Vandermonde determinant on a concatenated tuple factors into two
within-block determinants and the cross differences. -/
theorem det_vandermonde_append {R : Type*} [CommRing R] {m n : ℕ}
    (u : Fin m → R) (v : Fin n → R) :
    (Matrix.vandermonde (Fin.append u v)).det =
      (Matrix.vandermonde u).det * (Matrix.vandermonde v).det *
        ∏ i : Fin m, ∏ j : Fin n, (v j - u i) := by
  have hleft (i : Fin m) :
      ∏ j ∈ Ioi (Fin.castAdd n i), (Fin.append u v j - u i) =
        (∏ j ∈ Ioi i, (u j - u i)) * ∏ j : Fin n, (v j - u i) := by
    rw [← filter_lt_eq_Ioi, prod_filter, ← filter_lt_eq_Ioi, prod_filter, Fin.prod_univ_add]
    have hcross (j : Fin n) : Fin.castAdd n i < Fin.natAdd m j := by
      change i.val < m + j.val
      omega
    have hsame (j : Fin m) : Fin.castAdd n i < Fin.castAdd n j ↔ i < j := Iff.rfl
    simp [hsame, hcross]
  have hright (i : Fin n) :
      ∏ j ∈ Ioi (Fin.natAdd m i), (Fin.append u v j - v i) =
        ∏ j ∈ Ioi i, (v j - v i) := by
    rw [← filter_lt_eq_Ioi, prod_filter, ← filter_lt_eq_Ioi, prod_filter, Fin.prod_univ_add]
    have hcross (j : Fin m) : ¬Fin.natAdd m i < Fin.castAdd n j := by
      change ¬m + i.val < j.val
      omega
    have hsame (j : Fin n) : Fin.natAdd m i < Fin.natAdd m j ↔ i < j :=
      Fin.natAdd_lt_natAdd_iff m
    simp [hsame, hcross]
  rw [Matrix.det_vandermonde, Fin.prod_univ_add, Matrix.det_vandermonde,
    Matrix.det_vandermonde]
  simp only [Fin.append_left, Fin.append_right, hleft, hright, prod_mul_distrib]
  ac_rfl

/-- The row factor of Lemma 15.24: appending positive, separated entries to
a nonpositive prefix contributes at least their product to the prefix size
power. Here the parameters use the increasing order of Mathlib's determinant. -/
theorem log_det_vandermonde_append_ge {m n : ℕ}
    (u : Fin m → ℝ) (v : Fin n → ℝ) (hu : StrictMono u)
    (hu₀ : ∀ i, u i ≤ 0) (hv : ∀ j, 0 < v j)
    (hgap : ∀ i j, i < j → 1 ≤ v j - v i) :
    Real.log (Matrix.vandermonde u).det + m * ∑ j : Fin n, Real.log (v j) ≤
      Real.log (Matrix.vandermonde (Fin.append u v)).det := by
  have huD : 0 < (Matrix.vandermonde u).det := by
    rw [Matrix.det_vandermonde]
    exact prod_pos fun i _ => prod_pos fun j hj => sub_pos.mpr (hu (mem_Ioi.mp hj))
  have hvD : 1 ≤ (Matrix.vandermonde v).det := by
    rw [Matrix.det_vandermonde]
    exact one_le_prod₀ fun i _ => one_le_prod₀ fun j hj => hgap i j (mem_Ioi.mp hj)
  have hcross : (∏ j : Fin n, v j ^ m) ≤ ∏ i : Fin m, ∏ j : Fin n, (v j - u i) := by
    calc
      _ = ∏ i : Fin m, ∏ j : Fin n, v j := by
        rw [prod_comm]
        simp
      _ ≤ _ := by
        refine prod_le_prod₀ (fun _ _ => (prod_pos fun j _ => hv j).le) fun i _ => ?_
        exact prod_le_prod₀ (fun j _ => (hv j).le) fun j _ => by linarith [hu₀ i]
  have hbase : 0 < ∏ j : Fin n, v j ^ m := prod_pos fun j _ => pow_pos (hv j) _
  have hle : (Matrix.vandermonde u).det * (∏ j : Fin n, v j ^ m) ≤
      (Matrix.vandermonde (Fin.append u v)).det := by
    rw [det_vandermonde_append]
    have hcross₀ := hbase.le.trans hcross
    calc
      _ ≤ (Matrix.vandermonde u).det * ∏ i : Fin m, ∏ j : Fin n, (v j - u i) :=
        mul_le_mul_of_nonneg_left hcross huD.le
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right huD.le hvD) hcross₀
  have hl := Real.log_le_log (mul_pos huD hbase) hle
  rw [Real.log_mul huD.ne' hbase.ne', Real.log_prod (fun j _ => (pow_pos (hv j) m).ne')] at hl
  simpa [Real.log_pow, ← Finset.mul_sum] using hl

end Utilities
