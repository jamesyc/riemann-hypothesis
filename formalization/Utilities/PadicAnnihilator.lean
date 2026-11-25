module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace Utilities

/-- A nonzero integer divides a power of the p-adic prime with bounded
logarithmic size. -/
theorem exists_padic_prime_pow_of_intCast (ℓ : ℕ) [Fact ℓ.Prime] (X : ℤ) (hX : X ≠ 0) :
    ∃ r : ℕ, (r : ℝ) * Real.log ℓ ≤ Real.log (X.natAbs : ℝ) ∧
      (X : ℤ_[ℓ]) ∣ (ℓ : ℤ_[ℓ]) ^ r := by
  have hp : ℓ.Prime := Fact.out
  obtain ⟨r, m, hm, hfactor⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hX) ℓ hp.one_lt.ne'
  have hm₀ : 0 < m := Nat.pos_of_ne_zero (fun h => hm (h ▸ dvd_zero ℓ))
  have hpbound : ℓ ^ r ≤ X.natAbs := hfactor ▸ Nat.le_mul_of_pos_right _ hm₀
  have hlog := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hp.pos) r)
    (show (ℓ : ℝ) ^ r ≤ (X.natAbs : ℝ) by exact_mod_cast hpbound)
  rw [Real.log_pow] at hlog
  have hu : IsUnit (m : ℤ_[ℓ]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr (hp.coprime_iff_not_dvd.mpr hm))
  have hdiv : (X : ℤ_[ℓ]) ∣ ((X.natAbs : ℤ) : ℤ_[ℓ]) :=
    map_dvd (Int.castRingHom ℤ_[ℓ]) (Int.dvd_natAbs.mpr dvd_rfl)
  refine ⟨r, hlog, hdiv.trans ?_⟩
  rw [hfactor, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow]
  exact hu.mul_right_dvd.mpr dvd_rfl

/-- A nonzero integer annihilator can be replaced by a prime-power
annihilator of the same logarithmic budget. -/
theorem exists_padic_prime_pow_smul_eq_zero_of_intCast (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] (X : ℤ) (hX : X ≠ 0)
    (hkill : ∀ x : M, (X : ℤ_[ℓ]) • x = 0) :
    ∃ r : ℕ, (r : ℝ) * Real.log ℓ ≤ Real.log (X.natAbs : ℝ) ∧
      ∀ x : M, (ℓ : ℤ_[ℓ]) ^ r • x = 0 := by
  obtain ⟨r, hr, b, hb⟩ := exists_padic_prime_pow_of_intCast ℓ X hX
  refine ⟨r, hr, fun x => ?_⟩
  rw [hb, mul_comm, mul_smul, hkill x, smul_zero]

/-- An integer annihilator on a natural multiple gives an annihilator
on the original vector by multiplying the two scalars. -/
theorem padicInt_intCast_mul_nat_smul_eq_zero {ℓ : ℕ} [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    (X : ℤ) (d : ℕ) (x : M) (h : (X : ℤ_[ℓ]) • (d • x) = 0) :
    ((X * (d : ℤ) : ℤ) : ℤ_[ℓ]) • x = 0 := by
  rw [Int.cast_mul, Int.cast_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
  exact h

end Utilities
