module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.ZetaValues

@[expose] public section

open scoped BigOperators

namespace Utilities

/-- A rational coefficient in the generalized Bernoulli sum. -/
noncomputable def generalizedBernoulliCoefficient (N k a : ℕ) : ℚ :=
  (N : ℚ) ^ ((k : ℤ) - 1) * (Polynomial.bernoulli k).eval ((a : ℚ) / N)

/-- The generalized Bernoulli number attached to a function on a residue ring. -/
noncomputable def generalizedBernoulliValue {R : Type*} [CommRing R] [Algebra ℚ R]
    {N : ℕ} (k : ℕ) (Φ : ZMod N → R) : R :=
  ∑ a ∈ Finset.Icc 1 N, Φ (a : ZMod N) * algebraMap ℚ R (generalizedBernoulliCoefficient N k a)

/-- The primitive character's generalized Bernoulli number. -/
noncomputable def primitiveBernoulliValue {R : Type*} [CommRing R] [Algebra ℚ R]
    {N : ℕ} (k : ℕ) (χ : DirichletCharacter R N) : R :=
  generalizedBernoulliValue k (χ.primitiveCharacter : ZMod χ.conductor → R)

/-- The denominator multiplier used for generalized Bernoulli numbers. -/
def generalizedBernoulliDenominator (N k : ℕ) : ℕ := N * primorial (k + 1)

/-- A common complex archimedean bound for the normalized values. -/
noncomputable def generalizedBernoulliHeightBound (N k : ℕ) : ℝ :=
  16 * (N : ℝ) ^ (k + 1) * (k.factorial : ℝ)

/-- Uniform Fourier-series bound for the Bernoulli polynomials on the unit interval. -/
theorem abs_bernoulliFun_le {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun k x| ≤ 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  have hsum := hasSum_one_div_nat_pow_mul_fourier hk hx
  have hnorm_fourier (n : ℤ) (y : UnitAddCircle) :
      ‖fourier n y + (-1) ^ k * fourier (-n) y‖ ≤ 2 := by
    calc
      _ ≤ ‖fourier n y‖ + ‖(-1 : ℂ) ^ k * fourier (-n) y‖ := norm_add_le _ _
      _ = 2 := by simp [norm_pow, one_add_one_eq_two]
  have hnorm :
      ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
        ≤ 2 * (Real.pi ^ 2 / 6) := by
    rw [← hsum.tsum_eq]
    refine tsum_of_norm_bounded (hasSum_zeta_two.mul_left 2) fun n => ?_
    rw [norm_mul]
    have hn : ‖1 / (n : ℂ) ^ k‖ ≤ 1 / (n : ℝ) ^ (2 : ℕ) := by
      rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp [zero_pow (by omega : k ≠ 0)]
      · exact one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ (by exact_mod_cast hpos) hk)
    exact (mul_le_mul hn (hnorm_fourier _ _) (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
  rw [norm_mul, norm_div, norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, Complex.norm_two] at hnorm
  have hscaled := hnorm.trans (show 2 * (Real.pi ^ 2 / 6) ≤ 4 by nlinarith [Real.pi_pos, Real.pi_lt_d2])
  have hkfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ k := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hkfact] at hscaled
  exact (le_div_iff₀ hpi).mpr (by simpa only [mul_comm] using hscaled)

theorem norm_generalizedBernoulliValue_le {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (Φ : ZMod N → ℂ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) :
    ‖generalizedBernoulliValue k Φ‖ ≤ 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  let A : ℝ := 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold generalizedBernoulliValue
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (generalizedBernoulliCoefficient N k a)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ Finset.Icc 1 N, (N : ℝ) ^ ((k : ℤ) - 1) * A := by
      apply Finset.sum_le_sum
      intro a ha
      have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
      have hq : (0 : ℚ) < N := by exact_mod_cast hN
      have hq1 : (a : ℚ) / N ≤ 1 := (div_le_one hq).mpr (by exact_mod_cast haN)
      have hArg : ((((a : ℚ) / N : ℚ) : ℝ)) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by positivity, by exact_mod_cast hq1⟩
      have hB := abs_bernoulliFun_le hk hArg
      have hcoeff (q : ℚ) :
          (((Polynomial.bernoulli k).eval q : ℚ) : ℝ) = bernoulliFun k (q : ℝ) := by
        rw [bernoulliFun, Polynomial.eval_map_algebraMap, ← eq_ratCast (algebraMap ℚ ℝ) q,
          Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]
      rw [norm_mul, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
      unfold generalizedBernoulliCoefficient
      push_cast
      rw [abs_mul, abs_of_pos (zpow_pos hNr _), hcoeff]
      calc
        _ ≤ 1 * ((N : ℝ) ^ ((k : ℤ) - 1) * A) := mul_le_mul (hΦ _)
          (mul_le_mul_of_nonneg_left hB (zpow_pos hNr _).le) (by positivity) zero_le_one
        _ = _ := one_mul _
    _ = _ := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
        zpow_sub_one₀ hNr.ne', zpow_natCast]
      dsimp [A]
      field_simp

theorem norm_generalizedBernoulliDenominator_mul_le {M N k : ℕ}
    (hM : 0 < M) (hMN : M ≤ N) (hk : 2 ≤ k)
    (Φ : ZMod M → ℂ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) :
    ‖(generalizedBernoulliDenominator N k : ℂ) * generalizedBernoulliValue k Φ‖ ≤
      generalizedBernoulliHeightBound N k := by
  have hnorm := norm_generalizedBernoulliValue_le hM hk Φ hΦ
  have hprimorial : (primorial (k + 1) : ℝ) ≤ 4 ^ (k + 1) := by
    exact_mod_cast primorial_le_four_pow (k + 1)
  have h4 : (4 : ℝ) ^ k ≤ (2 * Real.pi) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) k
  have hpi : 0 < (2 * Real.pi) ^ k := by positivity
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  rw [norm_mul, Complex.norm_natCast, generalizedBernoulliDenominator, generalizedBernoulliHeightBound]
  push_cast
  calc
    _ ≤ (N : ℝ) * 4 ^ (k + 1) * (4 * (N : ℝ) ^ k * k.factorial / (2 * Real.pi) ^ k) := by
      gcongr
      exact hnorm.trans (by gcongr)
    _ = (16 * (N : ℝ) ^ (k + 1) * k.factorial) * (4 ^ k / (2 * Real.pi) ^ k) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one hpi).mpr h4)

theorem norm_normalized_primitiveBernoulliValue_le {N k : ℕ} [NeZero N] (hk : 2 ≤ k)
    (χ : DirichletCharacter ℂ N) :
    ‖(generalizedBernoulliDenominator N k : ℂ) * primitiveBernoulliValue k χ‖ ≤
      generalizedBernoulliHeightBound N k :=
  norm_generalizedBernoulliDenominator_mul_le (Nat.pos_of_ne_zero χ.conductor_ne_zero)
    (Nat.le_of_dvd (NeZero.pos _) χ.conductor_dvd_level) hk _ χ.primitiveCharacter.norm_le_one

/-- A primorial through `k + 1` clears the Bernoulli denominators through degree `k`. -/
theorem exists_int_primorial_mul_bernoulli (k j : ℕ) (hjk : j ≤ k) :
    ∃ z : ℤ, (primorial (k + 1) : ℚ) * bernoulli j = z := by
  have hdvd (p : ℕ) (hp : p.Prime) (hpk : p ≤ k + 1) : p ∣ primorial (k + 1) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | hodd
  · obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
    let S := (Finset.range (2 * m + 2)).filter fun p => p.Prime ∧ p - 1 ∣ 2 * m
    let P := primorial (k + 1)
    have hz' : bernoulli (2 * m) = (z : ℚ) - ∑ p ∈ S, (1 : ℚ) / p := by
      dsimp [S]
      rw [hz]
      ring
    refine ⟨(P : ℤ) * z - ∑ p ∈ S, ((P / p : ℕ) : ℤ), ?_⟩
    rw [show m + m = 2 * m by omega, Int.cast_sub, Int.cast_mul, Int.cast_sum]
    simp only [Int.cast_natCast]
    rw [hz', mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpM, hpprime, _⟩ := Finset.mem_filter.mp hp
    have hpP : p ∣ P := hdvd p hpprime (by have := Finset.mem_range.mp hpM; omega)
    rw [Nat.cast_div hpP (Nat.cast_ne_zero.mpr hpprime.ne_zero)]
    ring
  · rcases lt_or_ge 1 j with hj | hj
    · exact ⟨0, by simp [bernoulli_eq_zero_of_odd hodd hj]⟩
    · obtain rfl : j = 1 := by obtain ⟨m, hm⟩ := hodd; omega
      obtain ⟨d, hd⟩ := hdvd 2 Nat.prime_two (by omega)
      refine ⟨-(d : ℤ), ?_⟩
      rw [bernoulli_one, hd]
      push_cast
      ring

/-- Multiplying the generalized Bernoulli coefficient by the level leaves
ordinary nonnegative powers of the level in its polynomial expansion. -/
theorem mul_generalizedBernoulliCoefficient_eq_sum {N : ℕ} (k a : ℕ) (hN : 0 < N) :
    (N : ℚ) * generalizedBernoulliCoefficient N k a =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * bernoulli j *
        (N : ℚ) ^ j * (a : ℚ) ^ (k - j) := by
  have hNr : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [generalizedBernoulliCoefficient, ← mul_assoc, ← zpow_one_add₀ hNr,
    add_sub_cancel, zpow_natCast, Polynomial.bernoulli, Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpow : (N : ℚ) ^ k = (N : ℚ) ^ j * (N : ℚ) ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjk]
  rw [Polynomial.eval_monomial, div_pow, hpow]
  field_simp

/-- The common denominator clears each rational coefficient of the sum. -/
theorem exists_int_denominator_mul_generalizedBernoulliCoefficient {N : ℕ} (k a : ℕ)
    (hN : 0 < N) :
    ∃ z : ℤ, (generalizedBernoulliDenominator N k : ℚ) *
      generalizedBernoulliCoefficient N k a = z := by
  suffices h : (generalizedBernoulliDenominator N k : ℚ) *
      generalizedBernoulliCoefficient N k a ∈ (Int.castRingHom ℚ).range by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, hz.symm⟩
  rw [generalizedBernoulliDenominator, Nat.cast_mul, mul_comm (N : ℚ), mul_assoc,
    mul_generalizedBernoulliCoefficient_eq_sum k a hN, Finset.mul_sum]
  apply Subring.sum_mem
  intro j hj
  obtain ⟨z, hz⟩ := exists_int_primorial_mul_bernoulli k j
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  refine ⟨(k.choose j : ℤ) * z * (N : ℤ) ^ j * (a : ℤ) ^ (k - j), ?_⟩
  rw [eq_intCast]
  push_cast
  rw [← hz]
  ring

theorem denominator_mul_generalizedBernoulliValue_mem_subring
    {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ)
    (Φ : ZMod N → R) (A : Subring R) (hN : 0 < N)
    (hΦ : ∀ a, Φ a ∈ A) :
    (generalizedBernoulliDenominator N k : R) * generalizedBernoulliValue k Φ ∈ A := by
  rw [generalizedBernoulliValue, Finset.mul_sum]
  apply A.sum_mem
  intro a _
  obtain ⟨z, hz⟩ := exists_int_denominator_mul_generalizedBernoulliCoefficient k a hN
  have hz' : (generalizedBernoulliDenominator N k : R) *
      algebraMap ℚ R (generalizedBernoulliCoefficient N k a) = (z : R) := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, hz, map_intCast]
  rw [mul_left_comm, hz']
  exact A.mul_mem (hΦ _) (intCast_mem A z)

theorem sum_Icc_natCast_zmod {A : Type*} [AddCommMonoid A] {N : ℕ} [NeZero N]
    (f : ZMod N → A) :
    (∑ a ∈ Finset.Icc 1 N, f (a : ZMod N)) = ∑ a : ZMod N, f a := by
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N))
    (fun a : ZMod N => if a.val = 0 then N else a.val) ?_ ?_ ?_ ?_ ?_
  · exact fun _ _ => Finset.mem_univ _
  · intro a _
    refine Finset.mem_Icc.mpr ?_
    by_cases h : a.val = 0
    · rw [ite_eq_left h]
      exact ⟨NeZero.pos N, le_rfl⟩
    · rw [ite_eq_right h]
      exact ⟨Nat.pos_of_ne_zero h, (ZMod.val_lt a).le⟩
  · intro a ha
    obtain ⟨ha₀, haN⟩ := Finset.mem_Icc.mp ha
    simp only [ZMod.val_natCast]
    rcases lt_or_ge a N with h | h
    · rw [Nat.mod_eq_of_lt h, ite_eq_right (by omega)]
    · obtain rfl : a = N := le_antisymm haN h
      simp
  · intro a _
    by_cases h : a.val = 0
    · simpa [h] using ((ZMod.val_eq_zero a).mp h).symm
    · simp [h]
  · exact fun _ _ => rfl

/-- At a negative integer, the Dirichlet series of a periodic function is
the corresponding normalized generalized Bernoulli value. -/
theorem zmodLFunction_one_sub_nat_eq_generalizedBernoulli {N k : ℕ} [NeZero N]
    (hk : 2 ≤ k) (Φ : ZMod N → ℂ) :
    ZMod.LFunction Φ (1 - k) = -generalizedBernoulliValue k Φ / k := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hpow : (N : ℂ) ^ (-(1 - (k : ℂ))) = (N : ℂ) ^ ((k : ℤ) - 1) := by
    rw [show -(1 - (k : ℂ)) = ((((k : ℤ) - 1) : ℤ) : ℂ) by push_cast; ring,
      Complex.cpow_intCast]
  rw [ZMod.LFunction, hpow, ← sum_Icc_natCast_zmod, generalizedBernoulliValue,
    Finset.mul_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨ha₀, haN⟩ := Finset.mem_Icc.mp ha
  have hx₀ : (0 : ℝ) ≤ a / N := by positivity
  have hx₁ : (a : ℝ) / N ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast haN)
  have hzeta :
      HurwitzZeta.hurwitzZeta (((a : ℝ) / N : ℝ) : UnitAddCircle) (1 - k) =
        -1 / (k : ℂ) *
          ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval (((a : ℝ) / N : ℝ) : ℂ) := by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
    have hm : m ≠ 0 := by omega
    rw [show (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) by push_cast; ring]
    simpa only [Nat.cast_add, Nat.cast_one] using
      HurwitzZeta.hurwitzZeta_neg_nat (k := m) hm ⟨hx₀, hx₁⟩
  rw [ZMod.toAddCircle_natCast, hzeta, generalizedBernoulliCoefficient,
    map_mul, map_zpow₀, map_natCast, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  have hq : (algebraMap ℚ ℂ) ((a : ℚ) / N) = (((a : ℝ) / N : ℝ) : ℂ) := by
    rw [map_div₀, map_natCast, map_natCast]
    push_cast
    rfl
  rw [hq]
  have hk₀ : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp

/-- The primitive Bernoulli values that match the twist parity are nonzero. -/
theorem primitiveBernoulliValue_ne_zero {N k : ℕ} [NeZero N] (hk : 2 ≤ k)
    (χ : DirichletCharacter ℂ N) (hparity : χ (-1) = (-1) ^ k) :
    primitiveBernoulliValue k χ ≠ 0 := by
  let ψ := χ.primitiveCharacter
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hparψ : ψ (-1) = (-1) ^ k := by
    have h := χ.primitiveCharacter_apply_of_isCoprime (a := (-1 : ℤ))
      (show IsCoprime (-1 : ℤ) N from ⟨-1, 0, by norm_num⟩)
    have h' : ψ (-1) = χ (-1) := by simpa only [Int.cast_neg, Int.cast_one] using h
    exact h'.trans hparity
  have hnonpos : (1 - (k : ℂ)).re ≤ 0 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.natCast_re]
    exact sub_nonpos.mpr (by exact_mod_cast (by omega : 1 ≤ k))
  have hgamma : ψ.gammaFactor (1 - k) ≠ 0 := by
    intro hzero
    rcases Nat.even_or_odd k with he | ho
    · have hEven : ψ.Even := hparψ.trans he.neg_one_pow
      obtain ⟨m, hm⟩ := (DirichletCharacter.gammaFactor_eq_zero_iff_of_even hEven).mp hzero
      have heq : (1 : ℂ) + 2 * (m : ℂ) = k := by linear_combination hm
      have heq' : 1 + 2 * m = k := by exact_mod_cast heq
      obtain ⟨b, hb⟩ := he
      omega
    · have hOdd : ψ.Odd := hparψ.trans ho.neg_one_pow
      obtain ⟨m, hm⟩ := (DirichletCharacter.gammaFactor_eq_zero_iff_of_odd hOdd).mp hzero
      have heq : (2 : ℂ) + 2 * (m : ℂ) = k := by linear_combination hm
      have heq' : 2 + 2 * m = k := by exact_mod_cast heq
      obtain ⟨b, hb⟩ := ho
      omega
  have hL : ψ.LFunction (1 - k) ≠ 0 :=
    fun hzero => hgamma ((DirichletCharacter.LFunction_eq_zero_iff_of_re_nonpos hψ hnonpos).mp hzero).1
  intro h
  apply hL
  change ZMod.LFunction (ψ : ZMod χ.conductor → ℂ) (1 - k) = 0
  rw [zmodLFunction_one_sub_nat_eq_generalizedBernoulli hk]
  change generalizedBernoulliValue k (ψ : ZMod χ.conductor → ℂ) = 0 at h
  rw [h, neg_zero, zero_div]

/-- The Euler factors relating the primitive and imprimitive values are
nonzero at `1 - k`, so the Bernoulli value has the same nonvanishing. -/
theorem generalizedBernoulliValue_ne_zero_of_parity {N k : ℕ} [NeZero N] (hk : 2 ≤ k)
    (χ : DirichletCharacter ℂ N) (hparity : χ (-1) = (-1) ^ k) :
    generalizedBernoulliValue k (χ : ZMod N → ℂ) ≠ 0 := by
  let ψ := χ.primitiveCharacter
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψB : generalizedBernoulliValue k (ψ : ZMod χ.conductor → ℂ) ≠ 0 :=
    primitiveBernoulliValue_ne_zero hk χ hparity
  have hk₀ : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hψL : ψ.LFunction (1 - k) ≠ 0 := by
    change ZMod.LFunction (ψ : ZMod χ.conductor → ℂ) (1 - k) ≠ 0
    rw [zmodLFunction_one_sub_nat_eq_generalizedBernoulli hk]
    exact div_ne_zero (neg_ne_zero.mpr hψB) hk₀
  have hs : (1 : ℂ) - (k : ℂ) ≠ 1 := by
    intro h
    apply hk₀
    linear_combination -h
  have hlevel := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level ψ (Or.inr hs)
  rw [show ψ.changeLevel χ.conductor_dvd_level = χ from χ.changeLevel_primitiveCharacter,
    show -((1 : ℂ) - (k : ℂ)) = ((k - 1 : ℕ) : ℂ) by rw [Nat.cast_sub (by omega)]; ring] at hlevel
  simp only [Complex.cpow_natCast] at hlevel
  have hprod : (∏ p ∈ N.primeFactors, (1 - ψ p * (p : ℂ) ^ (k - 1))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    by_cases hu : IsUnit (p : ZMod χ.conductor)
    · have hnorm : ‖ψ (p : ZMod χ.conductor)‖ = 1 := by
        obtain ⟨u, hu⟩ := hu
        rw [← hu]
        exact ψ.unit_norm_eq_one u
      intro hz
      have h := congrArg norm (sub_eq_zero.mp hz)
      rw [norm_one, norm_mul, hnorm, norm_pow, Complex.norm_natCast, one_mul] at h
      have hlt : 1 < p ^ (k - 1) :=
        Nat.one_lt_pow (by omega) (Nat.prime_of_mem_primeFactors hp).one_lt
      exact hlt.ne (by exact_mod_cast h)
    · rw [MulChar.map_nonunit ψ hu, zero_mul, sub_zero]
      exact one_ne_zero
  have hL : χ.LFunction (1 - k) ≠ 0 := hlevel.symm ▸ mul_ne_zero hψL hprod
  intro hz
  apply hL
  change ZMod.LFunction (χ : ZMod N → ℂ) (1 - k) = 0
  rw [zmodLFunction_one_sub_nat_eq_generalizedBernoulli hk, hz, neg_zero, zero_div]

private theorem isIntegral_dirichletCharacter_value {R : Type*} [CommRing R]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) (a : ZMod N) :
    IsIntegral ℤ (χ a) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hpow : χ (u : ZMod N) ^ orderOf u = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
    exact IsIntegral.of_pow (orderOf_pos u) (hpow ▸ isIntegral_one)
  · rw [MulChar.map_nonunit χ ha]
    exact isIntegral_zero

/-- The common denominator makes the primitive generalized Bernoulli value integral. -/
theorem isIntegral_normalized_primitiveBernoulliValue {R : Type*} [CommRing R] [Algebra ℚ R]
    {N k : ℕ} [NeZero N] (χ : DirichletCharacter R N) :
    IsIntegral ℤ ((generalizedBernoulliDenominator N k : R) * primitiveBernoulliValue k χ) := by
  let M := χ.conductor
  let ψ := χ.primitiveCharacter
  let : NeZero M := ⟨χ.conductor_ne_zero⟩
  have hM : 0 < M := NeZero.pos _
  have hint : IsIntegral ℤ
      ((generalizedBernoulliDenominator M k : R) * generalizedBernoulliValue k (ψ : ZMod M → R)) :=
    denominator_mul_generalizedBernoulliValue_mem_subring k _ (integralClosure ℤ R).toSubring hM
      (isIntegral_dirichletCharacter_value ψ)
  have hdiv : generalizedBernoulliDenominator M k ∣ generalizedBernoulliDenominator N k := by
    obtain ⟨u, hu⟩ := χ.conductor_dvd_level
    refine ⟨u, ?_⟩
    unfold generalizedBernoulliDenominator
    change N * primorial (k + 1) = χ.conductor * primorial (k + 1) * u
    calc
      _ = (χ.conductor * u) * primorial (k + 1) := congrArg (· * primorial (k + 1)) hu
      _ = _ := by ring
  obtain ⟨u, hu⟩ := hdiv
  unfold primitiveBernoulliValue
  rw [hu, Nat.cast_mul, mul_comm (generalizedBernoulliDenominator M k : R) (u : R), mul_assoc]
  exact (isIntegral_natCast u).mul hint

theorem norm_prod_normalized_primitiveBernoulliValue_le {N k : ℕ} [NeZero N] (hk : 2 ≤ k)
    (S : Finset (DirichletCharacter ℂ N)) :
    ‖∏ χ ∈ S, (generalizedBernoulliDenominator N k : ℂ) * primitiveBernoulliValue k χ‖ ≤
      (generalizedBernoulliHeightBound N k) ^ S.card := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _ ∈ S, generalizedBernoulliHeightBound N k :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun χ _ =>
        norm_normalized_primitiveBernoulliValue_le hk χ)
    _ = _ := by simp

end Utilities
