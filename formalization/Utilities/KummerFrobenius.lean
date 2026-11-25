module

public import Utilities.CyclotomicFrobenius
public import Utilities.RationalPrime
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

open NumberField
open scoped NumberField

namespace Utilities

section

variable {L : Type*} [Field L] [Algebra ℚ L]
  {p : ℕ} (P : Ideal (𝓞 L))
  [hover : P.LiesOver (Ideal.span {(p : ℤ)})] {φ : Gal(L/ℚ)} (hφ : IsArithFrobAt ℤ φ P)

include hover hφ

/-- Away from the root order, arithmetic Frobenius acts by the rational
prime power on roots of unity, including on an algebraic closure. -/
theorem numberField_isArithFrobAt_apply_root {n : ℕ} (hn : ¬ p ∣ n)
    {z : L} (hz : z ^ n = 1) : φ z = z ^ p := by
  have hn₀ : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
  let w : 𝓞 L := ⟨z, IsIntegral.of_pow (Nat.pos_of_ne_zero hn₀) (hz ▸ isIntegral_one)⟩
  have hw : w ^ n = 1 := RingOfIntegers.ext hz
  have hnP : (n : 𝓞 L) ∉ P := (natCast_mem_iff_dvd_of_liesOver_rationalPrime P p n).not.mpr hn
  have h := hφ.apply_of_pow_eq_one hw hnP
  rw [← P.over_def (Ideal.span {(p : ℤ)}), Int.card_ideal_quot] at h
  exact congrArg (fun a : 𝓞 L => (a : L)) h

/-- Fixing the roots of unity of order prime to the residue characteristic
is equivalent to the corresponding congruence on the rational prime. -/
theorem numberField_isArithFrobAt_fixes_roots_iff [IsAlgClosed L] {n : ℕ} (hn : ¬ p ∣ n) :
    (∀ z : L, z ^ n = 1 → φ z = z) ↔ p ≡ 1 [MOD n] := by
  have hn₀ : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
  let _ : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  let _ : NeZero (n : L) := ⟨Nat.cast_ne_zero.mpr hn₀⟩
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := (inferInstance : HasEnoughRootsOfUnity L n).prim
    have he : ζ ^ p = ζ ^ (1 : ℕ) :=
      (numberField_isArithFrobAt_apply_root P hφ hn hζ.pow_eq_one).symm.trans
        ((h ζ hζ.pow_eq_one).trans (pow_one ζ).symm)
    rwa [(hζ.isOfFinOrder hn₀).pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at he
  · intro h z hz
    have hfinite : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn₀, hz⟩
    calc
      φ z = z ^ p := numberField_isArithFrobAt_apply_root P hφ hn hz
      _ = z ^ (1 : ℕ) := hfinite.pow_eq_pow_iff_modEq.mpr (h.of_dvd (orderOf_dvd_of_pow_eq_one hz))
      _ = z := pow_one z

/-- If Frobenius fixes a nonzero radical, its residue lies in the prime
field. This gives the multiplicative order bound for its radicand. -/
theorem orderOf_natCast_dvd_of_isArithFrobAt_fixes_radical
    [Fact p.Prime] [P.IsPrime] {m a k : ℕ} (hm : m ≠ 0) (ha : ¬ p ∣ a) (hk : p - 1 = m * k)
    {z : L} (hz : z ^ m = (a : L)) (hfix : φ z = z) :
    orderOf (a : ZMod p) ∣ k := by
  let y : 𝓞 L := ⟨z, IsIntegral.of_pow (Nat.pos_of_ne_zero hm) (hz ▸ isIntegral_natCast a)⟩
  let B := 𝓞 L ⧸ P
  let _ : CharP B p := charP_ringOfIntegers_quotient_of_liesOver P p
  let j := Ideal.Quotient.mk P
  have hy : y ^ m = (a : 𝓞 L) := RingOfIntegers.ext hz
  have hyfix : φ • y = y := RingOfIntegers.ext hfix
  have hybar : (j y) ^ m = (a : B) := by rw [← map_pow, hy, map_natCast]
  have hy₀ : j y ≠ 0 := by
    intro h
    have hzero : (a : B) = 0 := by rw [← hybar, h, zero_pow hm]
    exact ha ((CharP.cast_eq_zero_iff B p a).mp hzero)
  have hpow : (j y) ^ p = j y := by
    have h := (numberField_isArithFrobAt_iff (p := p) P φ).mp hφ y
    rw [hyfix] at h
    rw [← map_pow]
    exact (Ideal.Quotient.eq.mpr h).symm
  have hp : p.Prime := Fact.out
  have hpow₁ : (j y) ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ hy₀
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hpow, one_mul]
  apply orderOf_dvd_of_pow_eq_one
  apply ZMod.castHom_injective B
  rw [map_pow, map_natCast, map_one, ← hybar, ← pow_mul, ← hk]
  exact hpow₁

end

/-- The cyclotomic restrictions and a fixed Kummer radical give both
the splitting congruence and the prime-to-ℓ order required of an
auxiliary prime in the Frobenius count. -/
theorem kummerAuxiliaryPrime_conditions_of_isArithFrobAt
    {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
    {p ℓ n m a : ℕ} [Fact p.Prime] (hn : n.Coprime ℓ)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    {φ : Gal(L/ℚ)} (hφ : IsArithFrobAt ℤ φ P) (haway : ¬ p ∣ n * m * ℓ * a)
    (hroots : ∀ z : L, z ^ (n * m) = 1 → φ z = z)
    (hnext : ¬ ∀ z : L, z ^ (n * m * ℓ) = 1 → φ z = z)
    {z : L} (hz : z ^ m = (a : L)) (hfix : φ z = z) :
    p ≡ 1 [MOD n * m] ∧ ¬ ℓ ∣ orderOf (a : ZMod p) := by
  have h₁ : ¬ p ∣ n * m * ℓ := fun hd => haway (hd.trans (dvd_mul_right _ _))
  have h₂ : ¬ p ∣ n * m := fun hd => h₁ (hd.trans (dvd_mul_right _ _))
  have ha : ¬ p ∣ a := fun hd => haway (hd.trans (dvd_mul_left _ _))
  have hm : m ≠ 0 := fun h => h₂ (by simp [h])
  have hmod := (numberField_isArithFrobAt_fixes_roots_iff P hφ h₂).mp hroots
  have hnot := (numberField_isArithFrobAt_fixes_roots_iff P hφ h₁).not.mp hnext
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hp.one_le).mp hmod.symm
  have hkℓ : ¬ ℓ ∣ k := by
    rintro ⟨j, rfl⟩
    apply hnot
    symm
    exact (Nat.modEq_iff_dvd' hp.one_le).mpr ⟨j, by simpa only [mul_assoc] using hk⟩
  have hk' : p - 1 = m * (n * k) := hk.trans (by ac_rfl)
  have horder := orderOf_natCast_dvd_of_isArithFrobAt_fixes_radical P hφ hm ha hk' hz hfix
  exact ⟨hmod, fun hd => hkℓ (hn.symm.dvd_of_dvd_mul_left (hd.trans horder))⟩

end Utilities
