module

public import Utilities.CyclotomicCarryPrincipal
public import Utilities.RationalPrimeSieve
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Int
import Utilities.IdealClassPrimeSieve
import Mathlib.RingTheory.RamificationInertia.Inertia

@[expose] public section

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors

namespace Utilities

variable (E : Type*) [Field E] [NumberField E]

variable (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ E]

omit [NeZero N] [IsCyclotomicExtension {N} ℚ E] in
private theorem excludedPrime_lower_norm (v : cyclotomicExcludedPrimeSet N E)
    (hN : ¬ (rationalPrimeBelow E v.val).val ∣ N) :
    (rationalPrimeBelow E v.val).val ^ 2 ≤ Ideal.absNorm v.val.asIdeal := by
  let P := v.val.asIdeal
  let q := rationalPrimeBelow E v.val
  let _ : P.IsPrime := v.val.isPrime
  let _ : Infinite (𝓞 E) := Infinite.of_injective (Nat.cast : ℕ → 𝓞 E) Nat.cast_injective
  have he : q.val ^ P.inertiaDeg ℤ = Ideal.absNorm P := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P
  have hf : 2 ≤ P.inertiaDeg ℤ := by
    have hpos := Ideal.inertiaDeg_pos P ℤ
    by_contra h
    have h1 : P.inertiaDeg ℤ = 1 := by omega
    rw [h1, pow_one] at he
    let _ : Finite (𝓞 E ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient v.val.ne_bot
    let _ : Fintype (𝓞 E ⧸ P) := Fintype.ofFinite _
    have hc : Fintype.card (𝓞 E ⧸ P) = q.val := by
      rw [← Nat.card_eq_fintype_card, ← Ideal.absNorm_eq_natCard, he]
    let e := ZMod.ringEquivOfPrime (R := 𝓞 E ⧸ P) q.property hc
    let red := e.symm.toRingHom.comp (Ideal.Quotient.mk P)
    have hred : RingHom.ker red = P := by
      ext x
      change e.symm (Ideal.Quotient.mk P x) = 0 ↔ x ∈ P
      rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
    exact v.property ⟨q.val, q.property, hN, red, hred⟩
  rw [← he]
  exact Nat.pow_le_pow_right q.property.pos hf

omit [IsCyclotomicExtension {N} ℚ E] in
/-- Primes omitted from the cyclotomic residue calculation have
summable inverse norms. -/
theorem summable_inverse_norm_cyclotomicExcludedPrimeSet :
    Summable (fun v : cyclotomicExcludedPrimeSet N E => (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹) :=
  summable_inverse_norm_of_rational_square E N (cyclotomicExcludedPrimeSet N E)
    (excludedPrime_lower_norm E N)

/-- Every carry product in a cyclotomic field is principal. The argument uses
the degree-one primes to generate the class group. -/
theorem cyclotomicCarryIdealProduct_principal (x y : ZMod N) (I : (Ideal (𝓞 E))⁰) :
    (cyclotomicCarryIdealProduct N E x y I).val.IsPrincipal :=
  cyclotomicCarryIdealProduct_principal_of_summable_excludedPrimes N E
    (summable_inverse_norm_cyclotomicExcludedPrimeSet E N) x y I

local notation "χ" => MulEquiv.symm (IsCyclotomicExtension.Rat.galEquivZMod N E)

/-- The integral smoothed weight-one Stickelberger element annihilates the
cyclotomic class group. -/
theorem cyclotomicWeightOneClassAction_eq_zero (a : ℕ) (ha : a.Coprime N)
    (c : Additive (ClassGroup (𝓞 E))) :
    (numberFieldClassGroupGaloisAction ℚ E).asAlgebraHom
      (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha) c = 0 :=
  cyclotomicWeightOneClassAction_eq_zero_of_summable_excludedPrimes N E
    (summable_inverse_norm_cyclotomicExcludedPrimeSet E N) a ha c

end Utilities
