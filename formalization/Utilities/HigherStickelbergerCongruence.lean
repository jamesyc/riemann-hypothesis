module

public import Utilities.HigherStickelbergerCoefficients
public import Utilities.HigherStickelbergerPadic
import Utilities.HigherStickelbergerLevels

@[expose] public section

namespace Utilities

private theorem exists_bernoulliCoefficient_remainder {N : ℕ} (hN : 0 < N) (i x : ℕ) :
    ∃ z : ℤ, (N : ℚ) * generalizedBernoulliCoefficient N (i + 1) x =
      (x : ℚ) ^ (i + 1) - ((i : ℚ) + 1) / 2 * (N : ℚ) * (x : ℚ) ^ i +
        (N : ℚ) ^ 2 / (primorial (i + 2) : ℚ) * z := by
  let P := primorial (i + 2)
  let t (j : ℕ) : ℚ := (((i + 1).choose j : ℕ) : ℚ) * bernoulli j *
    (N : ℚ) ^ j * (x : ℚ) ^ (i + 1 - j)
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hP : (P : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (primorial_ne_zero _)
  have hsplit : (N : ℚ) * generalizedBernoulliCoefficient N (i + 1) x =
      (∑ j ∈ Finset.range i, t (j + 2)) + t 1 + t 0 := by
    rw [mul_generalizedBernoulliCoefficient_eq_sum (i + 1) x hN]
    change (∑ j ∈ Finset.range (i + 1 + 1), t j) = _
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have htail : (P : ℚ) / (N : ℚ) ^ 2 * (∑ j ∈ Finset.range i, t (j + 2)) ∈
      (Int.castRingHom ℚ).range := by
    rw [Finset.mul_sum]
    apply Subring.sum_mem
    intro j hj
    have hjk : j + 2 ≤ i + 1 := by have := Finset.mem_range.mp hj; omega
    obtain ⟨z, hz⟩ := exists_int_primorial_mul_bernoulli (i + 1) (j + 2) hjk
    refine ⟨((i + 1).choose (j + 2) : ℤ) * z * (N : ℤ) ^ j * (x : ℤ) ^ (i + 1 - (j + 2)), ?_⟩
    rw [eq_intCast]
    push_cast
    rw [← hz]
    dsimp only [t, P]
    have hsub : i + 1 - (j + 2) = i - (j + 1) := by omega
    rw [pow_add (N : ℚ) j 2, hsub]
    field_simp
  obtain ⟨z, hz⟩ := htail
  have hz' : (P : ℚ) / (N : ℚ) ^ 2 * (∑ j ∈ Finset.range i, t (j + 2)) = (z : ℚ) := hz.symm
  refine ⟨z, ?_⟩
  have hrest : (∑ j ∈ Finset.range i, t (j + 2)) = (N : ℚ) ^ 2 / (P : ℚ) * z := by
    rw [← hz']
    field_simp
  rw [hsplit, hrest]
  simp only [t, Nat.choose_zero_right, Nat.choose_one_right, bernoulli_zero, bernoulli_one,
    Nat.cast_one, Nat.cast_add, Nat.add_sub_cancel, Nat.sub_zero, pow_zero, pow_one, one_mul, mul_one]
  ring

private theorem exists_add_mul_pow_succ_remainder (x N q i : ℕ) :
    ∃ z : ℕ, (x + N * q) ^ (i + 1) =
      x ^ (i + 1) + (i + 1) * N * q * x ^ i + N ^ 2 * z := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i hi =>
    obtain ⟨z, hz⟩ := hi
    refine ⟨z * (x + N * q) + (i + 1) * q ^ 2 * x ^ i, ?_⟩
    rw [pow_succ (x + N * q) (i + 1), hz, pow_succ x (i + 1), pow_succ x i]
    ring

variable {N : ℕ} [NeZero N]

/-- The difference from the twisted weight-one coefficient is the level times
an integer divided by the weight and a single Bernoulli primorial. -/
theorem smoothedBernoulliCoefficient_eq_weightOne_add_remainder
    (i a : ℕ) (ha : a.Coprime N) (hodd : Odd a) (b : (ZMod N)ˣ) :
    ∃ z : ℤ, smoothedBernoulliCoefficient (i + 1) a ha b =
      (smoothedWeightOneCoefficient a ha b : ℚ) * ((b : ZMod N).val : ℚ) ^ i +
        (N : ℚ) / (((i + 1 : ℕ) : ℚ) * (primorial (i + 2) : ℚ)) * z := by
  let x := (b : ZMod N).val
  let y := inverseSmoothingResidue a ha b
  let q := a * y / N
  let P := primorial (i + 2)
  let k : ℚ := (i : ℚ) + 1
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hk : k ≠ 0 := by dsimp [k]; positivity
  have hP : (P : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (primorial_ne_zero _)
  have h2P : 2 ∣ P := Nat.prime_two.dvd_primorial_iff.mpr (by omega)
  have hhalf : ((P / 2 : ℕ) : ℚ) = (P : ℚ) / 2 := Nat.cast_div h2P (by norm_num)
  have hxy : (a : ℚ) * y = (x : ℚ) + (N : ℚ) * q := by
    exact_mod_cast mul_inverseSmoothingResidue_eq a ha b
  have ha' : a = 2 * (a / 2) + 1 := by obtain ⟨d, hd⟩ := hodd; omega
  have hA : (a : ℚ) = 2 * ((a / 2 : ℕ) : ℚ) + 1 := by exact_mod_cast ha'
  obtain ⟨u, hu⟩ := exists_add_mul_pow_succ_remainder x N q i
  have hpower : (a : ℚ) ^ (i + 1) * (y : ℚ) ^ (i + 1) =
      (x : ℚ) ^ (i + 1) + k * (N : ℚ) * q * (x : ℚ) ^ i + (N : ℚ) ^ 2 * u := by
    rw [← mul_pow, hxy]
    dsimp only [k]
    exact_mod_cast hu
  have hmod : x ≡ x + N * q [MOD N] := by simp [Nat.ModEq]
  have hle : x ^ i ≤ (x + N * q) ^ i := Nat.pow_le_pow_left (Nat.le_add_right _ _) _
  obtain ⟨v, hv⟩ := (Nat.modEq_iff_dvd' hle).mp (hmod.pow i)
  have hv' : (x + N * q) ^ i = x ^ i + N * v := by omega
  have hfirst : (a : ℚ) ^ (i + 1) * (y : ℚ) ^ i =
      (a : ℚ) * ((x : ℚ) ^ i + (N : ℚ) * v) := by
    rw [pow_succ (a : ℚ), mul_right_comm, ← mul_pow, hxy]
    have h := show ((x : ℚ) + (N : ℚ) * q) ^ i = (x : ℚ) ^ i + (N : ℚ) * v by exact_mod_cast hv'
    rw [h, mul_comm]
  obtain ⟨zx, hx⟩ := exists_bernoulliCoefficient_remainder (NeZero.pos N) i x
  obtain ⟨zy, hy⟩ := exists_bernoulliCoefficient_remainder (NeZero.pos N) i y
  let z : ℤ := (P : ℤ) * u - ((P / 2 : ℕ) : ℤ) * (i + 1 : ℕ) * a * v + (a : ℤ) ^ (i + 1) * zy - zx
  have hzQ : (z : ℚ) =
      (P : ℚ) * u - ((P / 2 : ℕ) : ℚ) * k * a * v + (a : ℚ) ^ (i + 1) * zy - zx := by
    simp only [z, k, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_one, Nat.cast_add, Nat.cast_one]
  refine ⟨z, mul_left_cancel₀ (mul_ne_zero hN hk) ?_⟩
  have hscale : (N : ℚ) * k * smoothedBernoulliCoefficient (i + 1) a ha b =
      (a : ℚ) ^ (i + 1) * ((N : ℚ) * generalizedBernoulliCoefficient N (i + 1) y) -
      (N : ℚ) * generalizedBernoulliCoefficient N (i + 1) x := by
    unfold smoothedBernoulliCoefficient
    push_cast
    change _ * _ * ((_ - _) / k) = _
    field_simp
    ring
  calc
    _ = ((a : ℚ) ^ (i + 1) * (y : ℚ) ^ (i + 1) - (x : ℚ) ^ (i + 1)) -
        k / 2 * (N : ℚ) * ((a : ℚ) ^ (i + 1) * (y : ℚ) ^ i - (x : ℚ) ^ i) +
        (N : ℚ) ^ 2 / (P : ℚ) * ((a : ℚ) ^ (i + 1) * (zy : ℚ) - (zx : ℚ)) := by
      rw [hscale, hy, hx]
      dsimp only [k, P]
      ring
    _ = _ := by
      rw [hpower, hfirst, hzQ]
      simp only [smoothedWeightOneCoefficient, Int.cast_sub, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
      change _ = (N : ℚ) * k * (((q : ℚ) - ((a / 2 : ℕ) : ℚ)) * (x : ℚ) ^ i +
        (N : ℚ) / (k * (P : ℚ)) * _)
      rw [hhalf, hA]
      dsimp only [k]
      field_simp
      ring

variable {G : Type*} [CommGroup G]

/-- At sufficient p-power precision, any p-adic lift of the rational higher element
is congruent to the integral twisted weight-one element at that level. -/
theorem exists_twistedWeightOne_eq_add_pow_smul_of_lift
    (p : ℕ) [Fact p.Prime] (π : (ZMod N)ˣ →* G) (i a r : ℕ)
    (ha : a.Coprime N) (hodd : Odd a) (hdiv : p ^ (r + multiplicity p (i + 1) + 1) ∣ N)
    (w : MonoidAlgebra ℤ_[p] G)
    (hw : MonoidAlgebra.mapRingHom G PadicInt.Coe.ringHom w =
      MonoidAlgebra.mapRingHom G (Rat.castHom ℚ_[p]) (rationalHigherStickelberger π (i + 1) a ha)) :
    ∃ v : MonoidAlgebra ℤ_[p] G,
      MonoidAlgebra.mapRingHom G (Int.castRingHom ℤ_[p]) (twistedWeightOneStickelberger π i a ha) =
        w + (p : ℤ_[p]) ^ r • v := by
  classical
  let D := (i + 1) * primorial (i + 2)
  have hp : p.Prime := Fact.out
  have hD : (D : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (mul_ne_zero (Nat.succ_ne_zero i) (primorial_ne_zero _))
  have hp' : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hN : (N : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hvalP : multiplicity p (primorial (i + 2)) ≤ 1 := by
    rw [Nat.multiplicity_eq_factorization hp]
    exact (squarefree_primorial _).natFactorization_le_one p
  have hvalD : multiplicity p D ≤ multiplicity p (i + 1) + 1 := by
    dsimp only [D]
    rw [Nat.multiplicity_mul (Nat.succ_ne_zero i) (primorial_ne_zero _)]
    exact Nat.add_le_add_left hvalP _
  have hvalN := (Nat.pow_dvd_iff_le_multiplicity hp.ne_one (NeZero.ne N)).mp hdiv
  have hc : (N : ℚ_[p]) / ((D : ℚ_[p]) * (p : ℚ_[p]) ^ r) ∈ PadicInt.subring p := by
    have hpr := pow_ne_zero r hp'
    rw [PadicInt.mem_subring_iff, Padic.norm_le_one_iff_val_nonneg, div_eq_mul_inv,
      Padic.valuation_mul hN (inv_ne_zero (mul_ne_zero hD hpr)), Padic.valuation_inv,
      Padic.valuation_mul hD hpr, Padic.valuation_pow, Padic.valuation_p, mul_one,
      Padic.valuation_natCast, Padic.valuation_natCast]
    omega
  let c : ℤ_[p] := Padic.lift ((N : ℚ_[p]) / ((D : ℚ_[p]) * (p : ℚ_[p]) ^ r)) hc
  have hscale : (p : ℚ_[p]) ^ r * (c : ℚ_[p]) = (N : ℚ_[p]) / D := by
    change (p : ℚ_[p]) ^ r * ((N : ℚ_[p]) / ((D : ℚ_[p]) * (p : ℚ_[p]) ^ r)) = _
    field_simp
  choose z hz using smoothedBernoulliCoefficient_eq_weightOne_add_remainder i a ha hodd
  refine ⟨∑ b : (ZMod N)ˣ, MonoidAlgebra.single (π b)⁻¹ (-(z b : ℤ_[p]) * c), ?_⟩
  apply MonoidAlgebra.map_injective (M := G) PadicInt.Coe.ringHom.toAddMonoidHom Subtype.coe_injective
  change MonoidAlgebra.mapRingHom G PadicInt.Coe.ringHom _ =
    MonoidAlgebra.mapRingHom G PadicInt.Coe.ringHom _
  rw [map_add, hw, rationalHigherStickelberger_eq_sum_smoothedBernoulliCoefficient,
    twistedWeightOneStickelberger, Finset.smul_sum]
  simp only [MonoidAlgebra.smul_single', map_sum, MonoidAlgebra.mapRingHom_single,
    map_mul, map_pow, map_natCast, map_intCast, map_neg, Rat.coe_castHom]
  rw [← Finset.sum_add_distrib]
  simp only [← MonoidAlgebra.single_add]
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg (MonoidAlgebra.single (π b)⁻¹)
  have hb := congrArg (Rat.castHom ℚ_[p]) (hz b)
  simp only [map_add, map_mul, map_div₀, map_pow, map_natCast, map_intCast, Rat.coe_castHom] at hb
  have hD' : (D : ℚ_[p]) = ((i + 1 : ℕ) : ℚ_[p]) * (primorial (i + 2) : ℚ_[p]) := Nat.cast_mul _ _
  rw [← hD'] at hb
  change (smoothedWeightOneCoefficient a ha b : ℚ_[p]) * ((b : ZMod N).val : ℚ_[p]) ^ i =
    (smoothedBernoulliCoefficient (i + 1) a ha b : ℚ_[p]) +
      (p : ℚ_[p]) ^ r * (-(z b : ℚ_[p]) * (c : ℚ_[p]))
  rw [hb]
  linear_combination (z b : ℚ_[p]) * hscale

/-- At every sufficiently high level of the cyclotomic tower, the twisted
weight-one element approximates the integral higher element to precision `p ^ r`. -/
theorem exists_twistedWeightOne_eq_padicHigherStickelberger_add_pow_smul
    (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) (hpN : p ∣ N)
    (π : (ZMod N)ˣ →* G) (i r m : ℕ) (hm : r + multiplicity p (i + 1) + 1 ≤ m) :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    let a := 2 * N + 1
    let ha : a.Coprime N := by simp [a]
    let ha' : a.Coprime (N * p ^ m) := ha.mul_right ((ha.coprime_dvd_right hpN).pow_right m)
    ∃ v : MonoidAlgebra ℤ_[p] G,
      MonoidAlgebra.mapRingHom G (Int.castRingHom ℤ_[p])
        (twistedWeightOneStickelberger (π.comp (ZMod.unitsMap (dvd_mul_right N (p ^ m)))) i a ha') =
      padicHigherStickelberger p π (Nat.succ_ne_zero i) hodd hpN + (p : ℤ_[p]) ^ r • v := by
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let a := 2 * N + 1
  have ha : a.Coprime N := by simp [a]
  have haodd : Odd a := ⟨N, rfl⟩
  have ha' : a.Coprime (N * p ^ m) := ha.mul_right ((ha.coprime_dvd_right hpN).pow_right m)
  exact exists_twistedWeightOne_eq_add_pow_smul_of_lift p _ i a r ha' haodd
    (dvd_trans (pow_dvd_pow p hm) (dvd_mul_left _ _)) _ (by
      rw [rationalHigherStickelberger_mul_pow hpN π m (i + 1) a ha]
      exact map_padicHigherStickelberger_eq_rational p π (Nat.succ_ne_zero i) hodd hpN)

/-- If the error is a multiple of a scalar killing a vector, two algebra
elements have the same action on that vector. -/
theorem algHom_end_apply_eq_of_eq_add_smul
    {R S X : Type*} [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid X] [Module R X]
    (ρ : S →ₐ[R] Module.End R X) {u v w : S} {c : R} {x : X}
    (h : u = v + c • w) (hx : c • x = 0) : ρ u x = ρ v x := by
  rw [h, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, ← (ρ w).map_smul,
    hx, map_zero, add_zero]

end Utilities
