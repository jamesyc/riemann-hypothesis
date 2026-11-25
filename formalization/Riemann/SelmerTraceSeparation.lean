module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Utilities.GaloisIntegralProduct

@[expose] public section

open scoped BigOperators

namespace Riemann

/-- The geometric Frobenius trace for the Eisenstein triple in
Proposition 17.21 and Remark 17.23. The parameter q is the residue norm. -/
noncomputable def selmerEisensteinTrace (q e : ℕ) (z : ℂ) : ℂ :=
  ((q : ℂ) ^ e)⁻¹ * z + 1 + (q : ℂ) ^ e * z⁻¹

/-- The Eisenstein trace is separated from the closed disk of radius three
containing the traces of pure normalized triples. -/
theorem three_lt_norm_selmerEisensteinTrace {q e : ℕ} {z : ℂ}
    (hq : 7 ≤ q) (he : 0 < e) (hz : ‖z‖ = 1) :
    3 < ‖selmerEisensteinTrace q e z‖ := by
  let x : ℂ := (q : ℂ) ^ e
  have hx : 7 ≤ ‖x‖ := by
    rw [show ‖x‖ = (q : ℝ) ^ e by simp [x, norm_pow]]
    have hq' : (7 : ℝ) ≤ q := by exact_mod_cast hq
    have hq₁ : (1 : ℝ) ≤ q := by linarith
    exact hq'.trans (by simpa using pow_le_pow_right₀ hq₁ (show 1 ≤ e by omega))
  have hsmall : ‖x⁻¹ * z + 1‖ ≤ 2 := by
    calc
      _ ≤ ‖x⁻¹ * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖x‖⁻¹ + 1 := by rw [norm_mul, norm_inv, hz, mul_one, norm_one]
      _ ≤ _ := by
        have h : ‖x‖⁻¹ ≤ 1 := by
          simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) (show 1 ≤ ‖x‖ by linarith)
        linarith
  have hlarge : ‖x * z⁻¹‖ = ‖x‖ := by rw [norm_mul, norm_inv, hz, inv_one, mul_one]
  have htriangle := norm_sub_le (x⁻¹ * z + 1 + x * z⁻¹) (x⁻¹ * z + 1)
  rw [add_sub_cancel_left, hlarge] at htriangle
  change (3 : ℝ) < ‖x⁻¹ * z + 1 + x * z⁻¹‖
  linarith

/-- Purity of the normalized eigenvalues rules out equality with the
Eisenstein trace for every root of unity, before any choice of a prime above
the coefficient characteristic. -/
theorem pureTripleTrace_ne_selmerEisensteinTrace
    {q e n : ℕ} {z : ℂ} (hq : 7 ≤ q) (he : 0 < e) (hn : n ≠ 0) (hz : z ^ n = 1)
    (eigenvalue : Fin 3 → ℂ) (hpure : ∀ i, ‖eigenvalue i‖ = 1) :
    (∑ i, eigenvalue i) ≠ selmerEisensteinTrace q e z := by
  have htrace : ‖∑ i, eigenvalue i‖ ≤ 3 := by
    refine (norm_sum_le _ _).trans_eq ?_
    simp [hpure]
  intro heq
  rw [heq] at htrace
  exact (three_lt_norm_selmerEisensteinTrace hq he (Complex.norm_eq_one_of_pow_eq_one hz hn)).not_ge htrace

/-- Produce the nonzero integer in the rank-three Count step from a pure
trace family whose cleared differences are integrally and Galois-stably
indexed. The indexing retains multiplicities of coincident traces. -/
theorem exists_selmerTraceCertificate
    {L I : Type*} [Field L] [CharZero L] [Algebra ℚ L]
    [IsGalois ℚ L] [FiniteDimensional ℚ L] [Fintype I]
    (emb : L →ₐ[ℚ] ℂ) {q e : ℕ} (hq : 7 ≤ q) (he : 0 < e)
    (tr z : I → L) (hz : ∀ i, ∃ d : ℕ, 0 < d ∧ z i ^ d = 1)
    (hpure : ∀ i, ‖emb (tr i)‖ ≤ 3) (hint : ∀ i, IsIntegral ℤ ((q : L) ^ e * tr i)) :
    let x : L := (q : L) ^ e
    let f (i : I) := x * tr i - (z i + x + x ^ 2 * (z i)⁻¹)
    (∀ σ : L ≃ₐ[ℚ] L, ∃ π : Equiv.Perm I, ∀ i, σ (f i) = f (π i)) →
    ∃ n : ℤ, n ≠ 0 ∧ (n : L) = ∏ i, f i ∧
      Real.log |(n : ℝ)| ≤ (Fintype.card I : ℝ) * Real.log (6 * ((q : ℝ) ^ e) ^ 2) := by
  let x : L := (q : L) ^ e
  let f (i : I) := x * tr i - (z i + x + x ^ 2 * (z i)⁻¹)
  dsimp only
  intro hperm
  have hxL : x ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hxC : emb x = (q : ℂ) ^ e := by simp [x]
  have hxC' : (q : ℂ) ^ e ≠ 0 := by rw [← hxC]; exact (map_ne_zero emb).mpr hxL
  have hnormx : ‖emb x‖ = (q : ℝ) ^ e := by rw [hxC]; simp [norm_pow]
  have hxnorm₁ : 1 ≤ (q : ℝ) ^ e := one_le_pow₀ (by exact_mod_cast (show 1 ≤ q by omega))
  have hzC (i : I) : ‖emb (z i)‖ = 1 := by
    obtain ⟨d, hd, h⟩ := hz i
    exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, h, map_one]) hd.ne'
  have hI (i : I) : IsIntegral ℤ (f i) := by
    obtain ⟨d, hd, h⟩ := hz i
    have hroot : IsIntegral ℤ (z i) := IsIntegral.of_pow hd (by rw [h]; exact isIntegral_one)
    have hinv : IsIntegral ℤ (z i)⁻¹ := IsIntegral.of_pow hd
      (by rw [inv_pow, h, inv_one]; exact isIntegral_one)
    have hxint : IsIntegral ℤ x := (isIntegral_natCast (R := ℤ) (B := L) q).pow e
    exact (hint i).sub ((hroot.add hxint).add ((hxint.pow 2).mul hinv))
  have hneq (i : I) : f i ≠ 0 := by
    have heis : emb (f i) = (q : ℂ) ^ e * (emb (tr i) - selmerEisensteinTrace q e (emb (z i))) := by
      unfold f selmerEisensteinTrace
      simp only [map_sub, map_mul, map_add, map_pow, map_inv₀, hxC]
      field_simp [hxC']
    have ht : emb (tr i) ≠ selmerEisensteinTrace q e (emb (z i)) := by
      intro h
      exact (three_lt_norm_selmerEisensteinTrace hq he (hzC i)).not_ge (h ▸ hpure i)
    exact fun h => (mul_ne_zero hxC' (sub_ne_zero.mpr ht)) (heis ▸ by rw [h, map_zero])
  obtain ⟨N, hN, hprod⟩ := Utilities.exists_int_of_galoisIntegralProduct f hI hneq hperm
  refine ⟨N, hN, hprod, ?_⟩
  have hnorm (i : I) : ‖emb (f i)‖ ≤ 6 * ((q : ℝ) ^ e) ^ 2 := by
    have h₁ : ‖emb (x * tr i)‖ ≤ (q : ℝ) ^ e * 3 := by
      rw [map_mul, norm_mul, hnormx]
      gcongr
      exact hpure i
    have h₂ : ‖emb (z i + x + x ^ 2 * (z i)⁻¹)‖ ≤ 1 + (q : ℝ) ^ e + ((q : ℝ) ^ e) ^ 2 := by
      simp only [map_add, map_mul, map_inv₀, show emb (x ^ 2) = (emb x) ^ 2 from map_pow emb x 2]
      calc
        _ ≤ (‖emb (z i)‖ + ‖emb x‖) + ‖(emb x) ^ 2 * (emb (z i))⁻¹‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
        _ = _ := by rw [norm_mul, norm_pow, norm_inv, hnormx, hzC, inv_one, mul_one]
    unfold f
    rw [map_sub]
    calc
      _ ≤ ‖emb (x * tr i)‖ + ‖emb (z i + x + x ^ 2 * (z i)⁻¹)‖ := norm_sub_le _ _
      _ ≤ 6 * ((q : ℝ) ^ e) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hxnorm₁ (by positivity : 0 ≤ (q : ℝ) ^ e)]
  have hNcast : (N : ℂ) = ∏ i, emb (f i) := by
    simpa using congrArg emb hprod
  have hprod' : |(N : ℝ)| ≤ (6 * ((q : ℝ) ^ e) ^ 2) ^ Fintype.card I := by
    rw [← Complex.norm_intCast, hNcast, Complex.norm_prod]
    calc
      _ ≤ ∏ _i : I, 6 * ((q : ℝ) ^ e) ^ 2 :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hnorm i)
      _ = _ := by simp
  have hpos : 0 < |(N : ℝ)| := abs_pos.mpr (by exact_mod_cast hN)
  simpa [Real.log_pow] using Real.log_le_log hpos hprod'

end Riemann
