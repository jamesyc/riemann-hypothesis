module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Nat.Prime.Factorial

@[expose] public section

namespace Utilities

variable (p : ℕ) [Fact p.Prime]

/-- Extend the finite-field power sum over units to all residues at positive degree. -/
theorem sum_zmod_pow_of_pos (n : ℕ) (hn : 0 < n) :
    (∑ x : ZMod p, x ^ n) = if p - 1 ∣ n then -1 else 0 := by
  classical
  let u : (ZMod p)ˣ ↪ ZMod p := ⟨Units.val, Units.val_injective⟩
  have hu : Finset.univ.map u = (Finset.univ : Finset (ZMod p)) \ {0} := by
    ext x
    simp only [u, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_singleton,
      Function.Embedding.coeFn_mk]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  calc
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod p)) \ {0}, x ^ n := by
      rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))),
        Finset.sum_singleton, zero_pow hn.ne', add_zero]
    _ = ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ n := by rw [← hu, Finset.sum_map]; rfl
    _ = _ := by simpa only [ZMod.card, Units.val_pow_eq_pow_val] using FiniteField.sum_pow_units (ZMod p) n

private theorem sum_zmod_pow_below_two_mul (n : ℕ) (hn : 0 < n) (h : n < 2 * (p - 1)) :
    (∑ x : ZMod p, x ^ n) = if n = p - 1 then -1 else 0 := by
  rw [sum_zmod_pow_of_pos p n hn]
  have hp : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  suffices hb : p - 1 ∣ n ↔ n = p - 1 by simp only [hb]
  refine ⟨?_, fun hb => hb ▸ dvd_refl _⟩
  rintro ⟨k, rfl⟩
  have hk₀ : k ≠ 0 := by intro hk; simp [hk] at hn
  have hk₂ : k < 2 := (Nat.mul_lt_mul_left hp).mp (by simpa only [Nat.mul_comm] using h)
  obtain rfl : k = 1 := by omega
  exact Nat.mul_one _

/-- The exact binomial coefficient in the reduction of a Jacobi sum with
positive exponents below the order of the unit group. -/
theorem sum_zmod_pow_mul_sub_pow_eq (i j : ℕ) (hi : 0 < i) (hip : i < p - 1) (hjp : j < p - 1) :
    (∑ x : ZMod p, x ^ i * (1 - x) ^ j) =
      if p - 1 ≤ i + j then
        -((-1 : ZMod p) ^ (p - 1 - i) * (j.choose (p - 1 - i) : ZMod p))
      else 0 := by
  let r := p - 1 - i
  let a (k : ℕ) : ZMod p := (-1) ^ k * (j.choose k : ZMod p)
  have hexpand (x : ZMod p) : (1 - x) ^ j =
      ∑ k ∈ Finset.range (j + 1), a k * x ^ k := by
    rw [sub_eq_neg_add, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [a]
    rw [show -x = (-1 : ZMod p) * x by simp, mul_pow, one_pow, mul_one]
    ring
  have hsum : (∑ x : ZMod p, x ^ i * (1 - x) ^ j) =
      ∑ k ∈ Finset.range (j + 1), a k * (∑ x : ZMod p, x ^ (i + k)) := by
    simp_rw [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro x _
    rw [pow_add]
    ring
  have hselect : (∑ k ∈ Finset.range (j + 1), a k * ∑ x : ZMod p, x ^ (i + k)) =
      ∑ k ∈ Finset.range (j + 1), if r = k then -a k else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := Finset.mem_range.mp hk
    rw [sum_zmod_pow_below_two_mul p (i + k) (by omega) (by omega)]
    by_cases h : i + k = p - 1
    · rw [ite_eq_left h, ite_eq_left (show r = k by dsimp [r]; omega), mul_neg_one]
    · rw [ite_eq_right h, ite_eq_right (show r ≠ k by dsimp [r]; omega), mul_zero]
  rw [hsum, hselect, Finset.sum_ite_eq]
  have hr : r ∈ Finset.range (j + 1) ↔ p - 1 ≤ i + j := by
    rw [Finset.mem_range]
    dsimp [r]
    omega
  rw [if_congr hr rfl rfl]

/-- The Jacobi reduction vanishes exactly in the absence of a residue carry. -/
theorem sum_zmod_pow_mul_sub_pow_eq_zero_iff
    (i j : ℕ) (hi : 0 < i) (hip : i < p - 1) (hjp : j < p - 1) :
    (∑ x : ZMod p, x ^ i * (1 - x) ^ j) = 0 ↔ i + j < p - 1 := by
  rw [sum_zmod_pow_mul_sub_pow_eq p i j hi hip hjp]
  by_cases h : p - 1 ≤ i + j
  · rw [ite_eq_left h, iff_false_intro (not_lt_of_ge h), iff_false]
    apply neg_ne_zero.mpr
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdiv
    have hk : p - 1 - i ≤ j := by omega
    have hfac : p ∣ j.factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hk]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdiv _) _
    have := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hfac
    omega
  · rw [ite_eq_right h]
    exact iff_of_true rfl (lt_of_not_ge h)

section CharZero

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- The product of a nondegenerate Jacobi sum and the sum of the inverse
characters is the residue characteristic, also over an integral domain. -/
theorem jacobiSum_zmod_mul_inv_eq_prime {χ ψ : MulChar (ZMod p) R}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    jacobiSum χ ψ * jacobiSum χ⁻¹ ψ⁻¹ = (p : R) := by
  let K := FractionRing R
  let f := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  let _ : CharZero K := charZero_of_injective_algebraMap hf
  have hc : ringChar K ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
    exact (Fact.out : p.Prime).ne_zero.symm
  have hχψ' : χ.ringHomComp f * ψ.ringHomComp f ≠ 1 := by
    rw [← MulChar.ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hf).mpr hχψ
  apply hf
  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp, ← MulChar.ringHomComp_inv,
    ← MulChar.ringHomComp_inv, map_natCast]
  simpa only [ZMod.card] using jacobiSum_mul_jacobiSum_inv hc (MulChar.ringHomComp_ne_one_iff hf |>.mpr hχ)
    (MulChar.ringHomComp_ne_one_iff hf |>.mpr hψ) hχψ'

end CharZero

/-- Transfer the finite-field carry criterion through a residue map. -/
theorem map_jacobiSum_eq_zero_iff_of_power_reductions
    {R : Type*} [CommRing R] (f : R →+* ZMod p) {χ ψ : MulChar (ZMod p) R}
    {i j : ℕ} (hi : 0 < i) (hip : i < p - 1) (hjp : j < p - 1)
    (hχ : ∀ x, f (χ x) = x ^ i) (hψ : ∀ x, f (ψ x) = x ^ j) :
    f (jacobiSum χ ψ) = 0 ↔ i + j < p - 1 := by
  simp only [jacobiSum, map_sum, map_mul, hχ, hψ]
  exact sum_zmod_pow_mul_sub_pow_eq_zero_iff p i j hi hip hjp

end Utilities
