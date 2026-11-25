module

public import Utilities.NumberFieldTorsion
public import Utilities.PadicTateFiniteRestriction
import Mathlib.Algebra.Ring.Commute
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

namespace Utilities

/-- Complex conjugation agrees with restriction to a normal intermediate field. -/
theorem algEquiv_complexConjugation_restrictNormal (E L : Type*) [Field E] [Field L]
    [Algebra ℚ E] [Algebra ℚ L] [Algebra E L] [IsScalarTower ℚ E L] [Normal ℚ E] [Normal ℚ L]
    (ι : L →ₐ[ℚ] ℂ) :
    (algEquiv_complexConjugation L ι).restrictNormal E =
      algEquiv_complexConjugation E (ι.domRestrict E) := by
  ext x
  apply (ι.domRestrict E).injective
  let τ := algEquiv_complexConjugation L ι
  change (ι.domRestrict E) (τ.restrictNormal E x) =
    (ι.domRestrict E) (algEquiv_complexConjugation E (ι.domRestrict E) x)
  rw [algEquiv_complexConjugation_apply E]
  change ι (algebraMap E L (τ.restrictNormal E x)) = star (ι (algebraMap E L x))
  rw [τ.restrictNormal_commutes E]
  exact algEquiv_complexConjugation_apply L ι _

/-- The p-adic cyclotomic character takes complex conjugation to minus one. -/
theorem cyclotomicCharacter_complexConjugation (L : Type) [Field L]
    [Algebra ℚ L] [Normal ℚ L] [IsAlgClosed L] (ι : L →ₐ[ℚ] ℂ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hodd : ℓ ≠ 2) :
    cyclotomicCharacter L ℓ (algEquiv_complexConjugation L ι).toRingEquiv = -1 := by
  let τ := algEquiv_complexConjugation L ι
  let χ := cyclotomicCharacter L ℓ τ.toRingEquiv
  have hτ : τ.toRingEquiv ^ 2 = 1 := by
    rw [pow_two]
    apply RingEquiv.ext
    exact algEquiv_complexConjugation_involutive L ι
  have hsq : (χ : ℤ_[ℓ]) ^ 2 = 1 := by
    change ((cyclotomicCharacter L ℓ τ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) ^ 2 = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hτ, map_one, Units.val_one]
  let _ : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hp : ℓ.Prime := Fact.out
  have hne : (χ : ℤ_[ℓ]) ≠ 1 := by
    intro hχ
    let _ : NeZero (ℓ : L) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L ℓ
    let _ : Fact (1 < ℓ ^ 1) := ⟨by simpa only [pow_one] using hp.one_lt⟩
    have hmod : (χ : ℤ_[ℓ]).toZModPow 1 = 1 := by rw [hχ, map_one]
    have hfixed := (cyclotomicCharacter_toZModPow_eq_iff ℓ L 1 τ.toRingEquiv 1).mp hmod ζ
      (by simpa only [pow_one] using hζ.pow_eq_one)
    rw [ZMod.val_one, pow_one] at hfixed
    have hnorm : ‖ι ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
      (by rw [← map_pow, hζ.pow_eq_one, map_one]) hp.ne_zero
    have hinv : τ ζ = ζ⁻¹ := by
      apply ι.injective
      change ι (algEquiv_complexConjugation L ι ζ) = ι ζ⁻¹
      rw [algEquiv_complexConjugation_apply, map_inv₀]
      exact (Complex.inv_eq_conj hnorm).symm
    have hζ₀ : ζ ≠ 0 := by
      intro h0
      have h := hζ.pow_eq_one
      rw [h0, zero_pow hp.ne_zero] at h
      exact zero_ne_one h
    have he : ζ = ζ⁻¹ := hfixed.symm.trans hinv
    have hpow : ζ ^ 2 = 1 := by
      calc
        ζ ^ 2 = ζ * ζ⁻¹ := by rw [pow_two, ← he]
        _ = 1 := mul_inv_cancel₀ hζ₀
    exact (Nat.dvd_prime Nat.prime_two).mp ((hζ.pow_eq_one_iff_dvd 2).mp hpow)
      |>.elim hp.ne_one hodd
  apply Units.ext
  have hneg := (sq_eq_one_iff.mp hsq).resolve_left hne
  simpa only [Units.val_neg, Units.val_one] using hneg

theorem padicTateScalarOnAut_complexConjugation (L : Type) [Field L]
    [Algebra ℚ L] [Normal ℚ L] [IsAlgClosed L] (ι : L →ₐ[ℚ] ℂ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hodd : ℓ ≠ 2) (i : ℕ) :
    padicTateScalarOnAut L ℓ i (algEquiv_complexConjugation L ι).toRingEquiv = (-1 : ℤ_[ℓ]) ^ i := by
  change ((cyclotomicCharacter L ℓ (algEquiv_complexConjugation L ι).toRingEquiv ^
    (-(i : ℤ)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = _
  rw [cyclotomicCharacter_complexConjugation L ι ℓ hodd, zpow_neg, zpow_natCast,
    ← inv_pow, inv_neg, inv_one, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end Utilities
