module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.NatInt

@[expose] public section

open NumberField

namespace Utilities

/-- A nonzero prime of a field’s ring of integers lies over a rational prime. -/
theorem exists_rationalPrime_below {L : Type*} [Field L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (hne : P ≠ ⊥) : ∃ p : ℕ, p.Prime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  obtain ⟨p, hp, he⟩ := (Ideal.isPrime_int_iff.mp (inferInstance : (P.under ℤ).IsPrime)).resolve_left
    (Ideal.under_ne_bot ℤ hne)
  exact ⟨p, hp, ⟨he.symm⟩⟩

theorem natCast_mem_iff_dvd_of_liesOver_rationalPrime {L : Type*} [Field L] (P : Ideal (𝓞 L))
    (p m : ℕ) [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (m : 𝓞 L) ∈ P ↔ p ∣ m := by
  have h : (m : 𝓞 L) ∈ P ↔ (m : ℤ) ∈ P.under ℤ := by
    change _ ↔ algebraMap ℤ (𝓞 L) (m : ℤ) ∈ P
    rw [map_natCast]
  rw [h, ← Ideal.over_def P (Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/-- The characteristic of the residue ring at a prime above a rational prime. -/
theorem charP_ringOfIntegers_quotient_of_liesOver {L : Type*} [Field L]
    (P : Ideal (𝓞 L)) (p : ℕ) [P.LiesOver (Ideal.span {(p : ℤ)})] :
    CharP (𝓞 L ⧸ P) p where
  cast_eq_zero_iff a := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_mem_iff_dvd_of_liesOver_rationalPrime P p a

/-- A rational prime generates a maximal ideal of the integers. -/
theorem rationalPrime_isMaximal (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : ℤ)}).IsMaximal := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  exact ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hp.ne_zero)

/-- A prime containing a rational prime lies over the corresponding integer ideal. -/
theorem liesOver_rationalPrime_of_mem {L : Type*} [Field L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞 L) ∈ P) :
    P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hmem : (p : ℤ) ∈ P.under ℤ := by
    change algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P
    simpa only [map_natCast] using hp
  exact ⟨(rationalPrime_isMaximal p).eq_of_le
    (inferInstance : (P.under ℤ).IsPrime).ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)⟩

/-- Primes containing the same rational prime contract to the same ideal of `𝓞 ℚ`. -/
theorem under_ratPrime_eq_of_mem {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (P Q : Ideal (𝓞 Ω)) [P.IsPrime] [Q.IsPrime]
    (hp : (ℓ : 𝓞 Ω) ∈ P) (hq : (ℓ : 𝓞 Ω) ∈ Q) :
    P.under (𝓞 ℚ) = Q.under (𝓞 ℚ) := by
  have hsurj : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := by
    have he : algebraMap ℤ (𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm.toRingHom := Subsingleton.elim _ _
    rw [he]
    exact Rat.ringOfIntegersEquiv.symm.surjective
  apply Ideal.comap_injective_of_surjective _ hsurj
  change (P.under (𝓞 ℚ)).under ℤ = (Q.under (𝓞 ℚ)).under ℤ
  rw [Ideal.under_under, Ideal.under_under,
    ← (liesOver_rationalPrime_of_mem P ℓ hp).over, ← (liesOver_rationalPrime_of_mem Q ℓ hq).over]

end Utilities
