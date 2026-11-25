module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Invariant.Galois

@[expose] public section

open IsCyclotomicExtension
open scoped NumberField

namespace Utilities

/-- At a prime over the rational prime `p`, the arithmetic Frobenius exponent is `p`. -/
theorem numberField_isArithFrobAt_iff {K : Type*} [Field K] [Algebra ℚ K] {p : ℕ}
    (P : Ideal (𝓞 K)) [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : K ≃ₐ[ℚ] K) :
    IsArithFrobAt ℤ σ P ↔ ∀ z : 𝓞 K, σ • z - z ^ p ∈ P := by
  change (∀ z : 𝓞 K, σ • z - z ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P) ↔ _
  rw [← P.over_def (Ideal.span {(p : ℤ)}), Int.card_ideal_quot]

/-- A Frobenius lift at an integral prime of a Galois number field. -/
theorem numberField_exists_isArithFrobAt {K : Type*} [Field K] [Algebra ℚ K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ P := by
  have hbase : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  let _ : Finite (𝓞 K ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hbase P)
  let _ : Algebra.IsInvariant ℤ (𝓞 K) (K ≃ₐ[ℚ] K) := by
    let h := Algebra.isInvariant_of_isGalois ℤ ℚ K (𝓞 K)
    refine ⟨fun z hz => h.isInvariant z ?_⟩
    intro σ
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 K) K (galRestrict ℤ ℚ K (𝓞 K) σ z) = algebraMap (𝓞 K) K z
    rw [algebraMap_galRestrict_apply]
    exact congrArg (fun a : 𝓞 K => (a : K)) (hz σ)
  exact IsArithFrobAt.exists_of_isInvariant ℤ (K ≃ₐ[ℚ] K) P

/-- The restriction of an arithmetic Frobenius to a normal subfield is again
arithmetic Frobenius at the prime below it. -/
theorem numberField_isArithFrobAt_restrictNormal_tower {K : Type*} [Field K] [Algebra ℚ K]
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra F K] [IsScalarTower ℚ F K]
    [Normal ℚ F] {p : ℕ}
    (Q : Ideal (𝓞 F)) (P : Ideal (𝓞 K)) [P.LiesOver Q]
    [Q.LiesOver (Ideal.span {(p : ℤ)})] {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ P) :
    IsArithFrobAt ℤ (σ.restrictNormal F) Q := by
  let _ : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P Q _
  apply (numberField_isArithFrobAt_iff (p := p) Q _).mpr
  intro z
  have hsmul : algebraMap (𝓞 F) (𝓞 K) (σ.restrictNormal F • z) =
      σ • algebraMap (𝓞 F) (𝓞 K) z := by
    apply NumberField.RingOfIntegers.ext
    exact σ.restrictNormal_commutes F (z : F)
  rw [Ideal.over_def P Q]
  change algebraMap (𝓞 F) (𝓞 K) (σ.restrictNormal F • z - z ^ p) ∈ P
  rw [map_sub, map_pow, hsmul]
  exact (numberField_isArithFrobAt_iff (p := p) P σ).mp hσ _

/-- The restriction of an arithmetic Frobenius to a normal subfield is again
arithmetic Frobenius at the prime below it. -/
theorem numberField_isArithFrobAt_restrictNormal {K : Type*} [Field K] [Algebra ℚ K]
    (F : IntermediateField ℚ K) [Normal ℚ F] {p : ℕ}
    (Q : Ideal (𝓞 F)) (P : Ideal (𝓞 K)) [P.LiesOver Q]
    [Q.LiesOver (Ideal.span {(p : ℤ)})] {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ P) :
    IsArithFrobAt ℤ (σ.restrictNormal F) Q :=
  numberField_isArithFrobAt_restrictNormal_tower F (p := p) Q P hσ

/-- In the cyclotomic unit coordinates, Frobenius acts as the rational prime
on every conductor divisor prime to that rational prime. This includes
Frobenius lifts at primes ramified in the full cyclotomic field. -/
theorem cyclotomic_frobenius_unitsMap_eq {n m p : ℕ} [NeZero n] [NeZero m]
    [Fact p.Prime] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.LiesOver (Ideal.span {(p : ℤ)})] {σ : K ≃ₐ[ℚ] K}
    (hσ : IsArithFrobAt ℤ σ P) (hmn : m ∣ n) (hp : p.Coprime m) :
    ZMod.unitsMap hmn (Rat.galEquivZMod n K σ) = ZMod.unitOfCoprime p hp := by
  have hfactor : ∃ r, n = m * r := hmn
  obtain ⟨r, hr⟩ := hfactor
  let ζ := zeta n ℚ K ^ r
  have hζ : IsPrimitiveRoot ζ m :=
    (zeta_spec n ℚ K).pow (NeZero.pos n) (hr.trans (mul_comm m r))
  have hζint := hζ.toInteger_isPrimitiveRoot
  have hm : (m : 𝓞 K) ∉ P := by
    intro hm
    have hmem : (m : ℤ) ∈ P.under ℤ := by
      change algebraMap ℤ (𝓞 K) (m : ℤ) ∈ P
      simpa only [map_natCast] using hm
    rw [← P.over_def (Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton] at hmem
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hp (by exact_mod_cast hmem)
  have hpow := hσ.apply_of_pow_eq_one hζint.pow_eq_one hm
  rw [← P.over_def (Ideal.span {(p : ℤ)}), Int.card_ideal_quot] at hpow
  change σ • hζ.toInteger = hζ.toInteger ^ p at hpow
  have hnroot : hζ.toInteger ^ n = 1 := (hζint.pow_eq_one_iff_dvd n).mpr hmn
  rw [Rat.galEquivZMod_smul_of_pow_eq n K σ hnroot,
    (hζint.isOfFinOrder (NeZero.ne m)).pow_inj_mod, ← hζint.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff'] at hpow
  apply Units.ext
  simpa only [ZMod.unitsMap_val, ZMod.natCast_val, ZMod.coe_unitOfCoprime] using hpow

end Utilities
