module

public import Utilities.HigherStickelberger
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RepresentationTheory.Basic
import Mathlib.NumberTheory.Multiplicity
import Utilities.GeneralizedBernoulliPadic
import Utilities.HigherStickelbergerCoefficients

@[expose] public section

namespace Utilities

variable {N : ℕ} [NeZero N] {G : Type*} [CommGroup G] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The odd-prime lifting-the-exponent formula makes the binomial quotient integral. -/
private theorem pow_sub_one_div_mul_mem_padicInt (hodd : ℓ ≠ 2) {a k : ℕ}
    (ha : 1 < a) (hdiv : ℓ ∣ a - 1) (hk : k ≠ 0) :
    ((a : ℚ_[ℓ]) ^ k - 1) / (((a : ℚ_[ℓ]) - 1) * k) ∈ PadicInt.subring ℓ := by
  have hℓ : ℓ.Prime := Fact.out
  have hcoprime : ¬ ℓ ∣ a := by
    intro h
    have heq : a - (a - 1) = 1 := by omega
    exact hℓ.not_dvd_one (by simpa only [heq] using Nat.dvd_sub h hdiv)
  have hpow : 1 < a ^ k := one_lt_pow₀ ha hk
  have hA : ((a - 1 : ℕ) : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.sub_ne_zero_of_lt ha)
  have hk' : (k : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have htop : ((a ^ k - 1 : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_ne_zero_of_lt hpow)
  have hval : multiplicity ℓ (a ^ k - 1) = multiplicity ℓ (a - 1) + multiplicity ℓ k := by
    simpa only [one_pow] using Nat.multiplicity_pow_sub_pow (hℓ.odd_of_ne_two hodd) ha hdiv hcoprime hk
  rw [← Nat.cast_one (R := ℚ_[ℓ]), ← Nat.cast_sub ha.le, ← Nat.cast_pow, ← Nat.cast_sub hpow.le,
    PadicInt.mem_subring_iff, Padic.norm_le_one_iff_val_nonneg, div_eq_mul_inv,
    Padic.valuation_mul htop (inv_ne_zero (mul_ne_zero hA hk')), Padic.valuation_inv,
    Padic.valuation_mul hA hk']
  simp only [Padic.valuation_natCast, hval, Nat.cast_add, add_neg_cancel, le_refl]

/-- The smoothed Bernoulli coefficients are integral at every odd prime dividing the level. -/
theorem smoothedBernoulliCoefficient_mem_padicInt (hodd : ℓ ≠ 2) {k : ℕ}
    (hk : k ≠ 0) (hℓN : ℓ ∣ N) (r : ℕ) :
    (1 - ((2 * N + 1 : ℕ) : ℚ_[ℓ]) ^ k) *
      ((generalizedBernoulliCoefficient N k r : ℚ_[ℓ]) / k) ∈ PadicInt.subring ℓ := by
  let a := 2 * N + 1
  let B : ℚ_[ℓ] := (generalizedBernoulliCoefficient N k r : ℚ)
  let S := PadicInt.subring ℓ
  have hN : 0 < N := NeZero.pos N
  have ha : 1 < a := by dsimp [a]; omega
  have ha' : (a : ℚ_[ℓ]) - 1 = 2 * N := by
    dsimp [a]
    push_cast
    ring
  have hdiv : ℓ ∣ a - 1 := by simpa [a] using dvd_mul_of_dvd_right hℓN 2
  have hq := pow_sub_one_div_mul_mem_padicInt ℓ hodd ha hdiv hk
  have hB := mul_generalizedBernoulliCoefficient_mem_padicInt ℓ hN hℓN k r
  change (1 - (a : ℚ_[ℓ]) ^ k) * (B / k) ∈ S
  have heq : (1 - (a : ℚ_[ℓ]) ^ k) * (B / k) =
      (-2 : ℚ_[ℓ]) * (((a : ℚ_[ℓ]) ^ k - 1) / (((a : ℚ_[ℓ]) - 1) * k)) * ((N : ℚ_[ℓ]) * B) := by
    rw [ha']
    field_simp [Nat.cast_ne_zero.mpr hk, Nat.cast_ne_zero.mpr (NeZero.ne N)]
    ring
  rw [heq]
  exact S.mul_mem (S.mul_mem (S.neg_mem (natCast_mem S 2)) hq) hB

/-- The integral p-adic model at an odd prime dividing the level,
with smoothing at `2 * N + 1`. -/
noncomputable def padicHigherStickelberger (π : (ZMod N)ˣ →* G) {k : ℕ}
    (hk : k ≠ 0) (hodd : ℓ ≠ 2) (hℓN : ℓ ∣ N) : MonoidAlgebra ℤ_[ℓ] G :=
  -∑ u : (ZMod N)ˣ, MonoidAlgebra.single (π u)⁻¹
    (Padic.lift ((1 - ((2 * N + 1 : ℕ) : ℚ_[ℓ]) ^ k) *
      ((generalizedBernoulliCoefficient N k (u : ZMod N).val : ℚ_[ℓ]) / (k : ℚ_[ℓ])))
      (smoothedBernoulliCoefficient_mem_padicInt ℓ hodd hk hℓN (u : ZMod N).val))

/-- The p-adic model lifts the rational higher Stickelberger element. -/
theorem map_padicHigherStickelberger_eq_rational (π : (ZMod N)ˣ →* G) {k : ℕ}
    (hk : k ≠ 0) (hodd : ℓ ≠ 2) (hℓN : ℓ ∣ N) :
    MonoidAlgebra.mapRingHom G PadicInt.Coe.ringHom (padicHigherStickelberger ℓ π hk hodd hℓN) =
      MonoidAlgebra.mapRingHom G (Rat.castHom ℚ_[ℓ])
        (rationalHigherStickelberger π k (2 * N + 1) (by simp)) := by
  have hau := zmodUnitOfCoprime_two_mul_add_one_eq_one N
  rw [padicHigherStickelberger, rationalHigherStickelberger, rationalStickelbergerTheta, hau, map_one π, inv_one]
  simp only [map_mul, map_sub, map_one, map_neg, map_sum, MonoidAlgebra.mapRingHom_single,
    map_pow, map_div₀, map_natCast, Rat.coe_castHom, PadicInt.Coe.ringHom_apply]
  rw [mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  conv_rhs => rw [MonoidAlgebra.one_def, ← MonoidAlgebra.single_sub, MonoidAlgebra.single_mul_single, one_mul]
  rfl

/-- Any p-adic integral lift of the rational higher element differs from the
integral model by exactly the same denominator multiplier as over ℚ. -/
theorem map_integralHigherStickelberger_padic_eq_smul (π : (ZMod N)ˣ →* G) {k a : ℕ}
    (hk : k ≠ 0) (ha : a.Coprime N) (w : MonoidAlgebra ℤ_[ℓ] G)
    (hw : MonoidAlgebra.mapRingHom G PadicInt.Coe.ringHom w =
      MonoidAlgebra.mapRingHom G (Rat.castHom ℚ_[ℓ]) (rationalHigherStickelberger π k a ha)) :
    MonoidAlgebra.mapRingHom G (Int.castRingHom ℤ_[ℓ]) (integralHigherStickelberger π k a ha) =
      ((k : ℤ_[ℓ]) * generalizedBernoulliDenominator N k) • w := by
  ext g
  let x := (integralHigherStickelberger π k a ha).coeff g
  let y := (rationalHigherStickelberger π k a ha).coeff g
  have hwg : (w.coeff g : ℚ_[ℓ]) = (y : ℚ_[ℓ]) := by
    have h := congrArg (fun z : MonoidAlgebra ℚ_[ℓ] G => z.coeff g) hw
    simp only [MonoidAlgebra.coeff_mapRingHom] at h
    exact h
  have hQ : (x : ℚ) = ((k : ℚ) * generalizedBernoulliDenominator N k) * y := by
    have h := congrArg (fun z : MonoidAlgebra ℚ G => z.coeff g)
      (map_integralHigherStickelberger_eq_smul π hk ha)
    simp only [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at h
    exact h
  simp only [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  change ((x : ℤ_[ℓ]) : ℚ_[ℓ]) =
    ((((k : ℤ_[ℓ]) * generalizedBernoulliDenominator N k) * w.coeff g : ℤ_[ℓ]) : ℚ_[ℓ])
  rw [PadicInt.coe_intCast, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_natCast,
    PadicInt.coe_natCast, hwg]
  have h := congrArg (Rat.castHom ℚ_[ℓ]) hQ
  rwa [map_intCast, map_mul, map_mul, map_natCast, map_natCast] at h

/-- Annihilation by a p-adic lift of the rational element implies
annihilation by the denominator-cleared integer element. -/
theorem integralHigherStickelberger_annihilation_of_padicLift (π : (ZMod N)ˣ →* G) {k a : ℕ}
    (hk : k ≠ 0) (ha : a.Coprime N) (w : MonoidAlgebra ℤ_[ℓ] G)
    (hw : MonoidAlgebra.mapRingHom G PadicInt.Coe.ringHom w =
      MonoidAlgebra.mapRingHom G (Rat.castHom ℚ_[ℓ]) (rationalHigherStickelberger π k a ha))
    {X : Type*} [AddCommGroup X] [Module ℤ_[ℓ] X] (ρ : Representation ℤ_[ℓ] G X)
    (x : X) (hkill : ρ.asAlgebraHom w x = 0) :
    ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (Int.castRingHom ℤ_[ℓ])
      (integralHigherStickelberger π k a ha)) x = 0 := by
  rw [map_integralHigherStickelberger_padic_eq_smul ℓ π hk ha w hw,
    map_smul, LinearMap.smul_apply, hkill, smul_zero]

end Utilities
