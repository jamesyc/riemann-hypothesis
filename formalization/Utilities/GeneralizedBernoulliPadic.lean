module

public import Utilities.GeneralizedBernoulli
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

namespace Utilities

variable (p : ℕ) [Fact p.Prime]

/-- A single factor of the local prime clears the denominator of a Bernoulli number. -/
theorem mul_bernoulli_mem_padicInt (j : ℕ) :
    (p : ℚ_[p]) * (bernoulli j : ℚ_[p]) ∈ PadicInt.subring p := by
  let P := primorial (j + 1)
  have hp : p.Prime := Fact.out
  have hP : (P : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (primorial_ne_zero _)
  have hmul : multiplicity p P ≤ 1 := by
    rw [Nat.multiplicity_eq_factorization hp]
    exact (squarefree_primorial _).natFactorization_le_one p
  have hratio : (p : ℚ_[p]) / (P : ℚ_[p]) ∈ PadicInt.subring p := by
    rw [PadicInt.mem_subring_iff, Padic.norm_le_one_iff_val_nonneg, div_eq_mul_inv,
      Padic.valuation_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (inv_ne_zero hP),
      Padic.valuation_inv, Padic.valuation_p, Padic.valuation_natCast]
    omega
  obtain ⟨z, hz⟩ := exists_int_primorial_mul_bernoulli j j le_rfl
  have hz' := congrArg (Rat.castHom ℚ_[p]) hz
  rw [map_mul, map_natCast, map_intCast] at hz'
  change (P : ℚ_[p]) * (bernoulli j : ℚ_[p]) = (z : ℚ_[p]) at hz'
  have heq : (p : ℚ_[p]) * (bernoulli j : ℚ_[p]) = (p : ℚ_[p]) / (P : ℚ_[p]) * z := by
    rw [← hz']
    field_simp
  rw [heq]
  exact (PadicInt.subring p).mul_mem hratio (intCast_mem _ z)

/-- At a prime dividing the level, the level-scaled Bernoulli coefficient is integral. -/
theorem mul_generalizedBernoulliCoefficient_mem_padicInt {N : ℕ}
    (hN : 0 < N) (hpN : p ∣ N) (k a : ℕ) :
    (N : ℚ_[p]) * (generalizedBernoulliCoefficient N k a : ℚ_[p]) ∈ PadicInt.subring p := by
  let S := PadicInt.subring p
  have hs := congrArg (Rat.castHom ℚ_[p]) (mul_generalizedBernoulliCoefficient_eq_sum k a hN)
  simp only [map_mul, map_sum, map_pow, map_natCast, Rat.coe_castHom] at hs
  rw [hs]
  apply S.sum_mem
  intro j _
  apply S.mul_mem _ (S.pow_mem (natCast_mem S a) _)
  rw [mul_assoc]
  apply S.mul_mem (natCast_mem S (k.choose j))
  obtain ⟨m, hm⟩ := hpN
  cases j with
  | zero => simp
  | succ j =>
    have heq : (bernoulli (j + 1) : ℚ_[p]) * (N : ℚ_[p]) ^ (j + 1) =
        ((p : ℚ_[p]) * (bernoulli (j + 1) : ℚ_[p])) * ((m : ℚ_[p]) * (N : ℚ_[p]) ^ j) := by
      rw [pow_succ', hm, Nat.cast_mul]
      ring
    rw [heq]
    exact S.mul_mem (mul_bernoulli_mem_padicInt p (j + 1))
      (S.mul_mem (natCast_mem S m) (S.pow_mem (natCast_mem S N) j))

end Utilities
