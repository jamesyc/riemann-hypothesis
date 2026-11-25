module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

@[expose] public section

namespace Utilities

/-- An odd prime dividing `d + 1` is a square modulo a prime `d ≡ 3 (mod 4)`. -/
theorem isSquare_zmod_of_dvd_add_one {p d : ℕ} [Fact p.Prime] [Fact d.Prime]
    (hp : p ≠ 2) (hd : d % 4 = 3) (hdiv : p ∣ d + 1) :
    IsSquare (p : ZMod d) := by
  have hcast : (d : ZMod p) = -1 := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    exact hdiv
  have hne : p ≠ d := by
    intro heq
    subst d
    simp at hcast
  have hd₂ : d ≠ 2 := by omega
  have hpOdd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  by_cases hp₁ : p % 4 = 1
  · apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp₁ hd₂).mp
    rw [hcast, ZMod.exists_sq_eq_neg_one_iff]
    omega
  · have hp₃ : p % 4 = 3 := by omega
    by_contra hn
    have hsq := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp₃ hd hne).mpr hn
    rw [hcast, ZMod.exists_sq_eq_neg_one_iff] at hsq
    exact hsq hp₃

/-- A square root of a unit in a prime residue field lifts to its unit group. -/
theorem isSquare_zmodUnit_of_isSquare_coe {p : ℕ} [Fact p.Prime]
    {u : (ZMod p)ˣ} (hu : IsSquare (u : ZMod p)) : IsSquare u := by
  obtain ⟨a, ha⟩ := hu
  have ha₀ : a ≠ 0 := by
    intro h
    exact u.ne_zero (by simpa only [h, zero_mul] using ha)
  exact ⟨Units.mk0 a ha₀, Units.ext ha⟩

end Utilities
