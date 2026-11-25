module

public import Utilities.AbsoluteCyclotomicInertia
public import Utilities.RationalPrime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open NumberField
open scoped NumberField Pointwise

namespace Utilities

/-- At a rational prime congruent to one modulo the order, every element
of the decomposition group fixes the corresponding roots of unity. -/
theorem stabilizer_fixes_root_of_modEq_one {L : Type*} [Field L] [Algebra ℚ L]
    {p n : ℕ} [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (hp : p ≡ 1 [MOD n])
    {g : Gal(L/ℚ)} (hg : g ∈ MulAction.stabilizer Gal(L/ℚ) P)
    {z : L} (hz : z ^ n = 1) : g z = z := by
  have hp₀ : p.Prime := Fact.out
  have hcop : p.Coprime n :=
    Nat.coprime_of_mul_modEq_one 1 (by simpa using hp)
  have hnP : (n : 𝓞 L) ∉ P := fun h =>
    (hp₀.coprime_iff_not_dvd.mp hcop)
      ((natCast_mem_iff_dvd_of_liesOver_rationalPrime P p n).mp h)
  have hn : n ≠ 0 := fun h => hnP (by simp [h])
  let y : 𝓞 L := ⟨z, IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hz ▸ isIntegral_one)⟩
  have hy : y ^ n = 1 := RingOfIntegers.ext hz
  let f := MulSemiringAction.toRingAut Gal(L/ℚ) (𝓞 L) g
  have hfy : (g • y) ^ n = 1 := (map_pow f y n).symm.trans (congrArg f hy |>.trans (map_one f))
  let B := Ideal.span {(p : ℤ)}
  let _ : B.IsMaximal := rationalPrime_isMaximal p
  let _ : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P B
  let K := 𝓞 L ⧸ P
  let _ : Field K := Ideal.Quotient.field P
  let j := Ideal.Quotient.mk P
  let _ : CharP K p := charP_ringOfIntegers_quotient_of_liesOver P p
  have hybar : (j y) ^ n = 1 := (map_pow j y n).symm.trans (by rw [hy, map_one])
  have hp1 : n ∣ p - 1 := (Nat.modEq_iff_dvd' hp₀.one_lt.le).mp hp.symm
  have hyFrob : (j y) ^ p = j y := by
    obtain ⟨k, hk⟩ := hp1
    have he : p = n * k + 1 :=
      (Nat.sub_add_cancel hp₀.one_lt.le).symm.trans (congrArg (· + 1) hk)
    rw [he, pow_succ, pow_mul, hybar, one_pow, one_mul]
  have hsub := (Subfield.mem_bot_iff_pow_eq_self K p).mpr hyFrob
  have hmem := (Polynomial.mem_primeSubfieldFinset K p).mpr hsub
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hmem
  have hyCast : j y = (a.val : K) := by
    change ZMod.castHom (dvd_refl p) K a = j y at ha
    rw [← ha]
    exact ZMod.cast_eq_val a
  let gbar := Ideal.Quotient.stabilizerHom P B Gal(L/ℚ) ⟨g, hg⟩
  have hbar : j (g • y) = j y := by
    change gbar (j y) = j y
    rw [hyCast, map_natCast]
  have hyfix := eq_of_pow_eq_one_of_sub_mem_prime P hnP hfy hy (Ideal.Quotient.eq.mp hbar)
  exact congrArg (fun a : 𝓞 L => (a : L)) hyfix

end Utilities
