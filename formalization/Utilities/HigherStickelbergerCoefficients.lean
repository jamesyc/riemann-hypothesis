module

public import Utilities.HigherStickelberger

@[expose] public section

namespace Utilities

theorem zmodUnitOfCoprime_two_mul_add_one_eq_one (N : ℕ) :
    ZMod.unitOfCoprime (2 * N + 1) (by simp : (2 * N + 1).Coprime N) = 1 := by
  apply Units.ext
  simp [Nat.cast_add, Nat.cast_mul]

variable {N : ℕ} [NeZero N] {G : Type*}

/-- The representative of the unit obtained by undoing the smoothing permutation. -/
def inverseSmoothingResidue (a : ℕ) (ha : a.Coprime N) (b : (ZMod N)ˣ) : ℕ :=
  ((ZMod.unitOfCoprime a ha)⁻¹ * b : (ZMod N)ˣ).val.val

/-- The smoothing displacement is a multiple of the level, with quotient
given by ordinary Euclidean division of the product. -/
theorem mul_inverseSmoothingResidue_eq (a : ℕ) (ha : a.Coprime N) (b : (ZMod N)ˣ) :
    a * inverseSmoothingResidue a ha b =
      (b : ZMod N).val + N * (a * inverseSmoothingResidue a ha b / N) := by
  let u := ZMod.unitOfCoprime a ha
  have hcast : ((a * inverseSmoothingResidue a ha b : ℕ) : ZMod N) = b.val := by
    rw [Nat.cast_mul, inverseSmoothingResidue, ZMod.natCast_zmod_val]
    change u.val * (u⁻¹ * b).val = b.val
    rw [← Units.val_mul, mul_inv_cancel_left]
  have hmod : a * inverseSmoothingResidue a ha b % N = (b : ZMod N).val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast
  rw [← hmod]
  exact (Nat.mod_add_div _ _).symm

/-- The contribution at a unit before summing over the fibers of the Galois map. -/
noncomputable def smoothedBernoulliCoefficient
    (k a : ℕ) (ha : a.Coprime N) (b : (ZMod N)ˣ) : ℚ :=
  ((a : ℚ) ^ k * generalizedBernoulliCoefficient N k (inverseSmoothingResidue a ha b) -
    generalizedBernoulliCoefficient N k (b : ZMod N).val) / k

variable [CommGroup G] in
theorem rationalHigherStickelberger_eq_sum_smoothedBernoulliCoefficient
    (π : (ZMod N)ˣ →* G) (k a : ℕ) (ha : a.Coprime N) :
    rationalHigherStickelberger π k a ha =
      ∑ b : (ZMod N)ˣ, MonoidAlgebra.single (π b)⁻¹ (smoothedBernoulliCoefficient k a ha b) := by
  let u := ZMod.unitOfCoprime a ha
  let S : MonoidAlgebra ℚ G := MonoidAlgebra.single (π u)⁻¹ ((a : ℚ) ^ k)
  let f (b : (ZMod N)ˣ) : MonoidAlgebra ℚ G :=
    MonoidAlgebra.single (π b)⁻¹ (generalizedBernoulliCoefficient N k b.val.val / k)
  change (1 - S) * (-(∑ b : (ZMod N)ˣ, f b)) = _
  rw [mul_neg, sub_mul, one_mul, neg_sub, Finset.mul_sum]
  have hreindex : (∑ b : (ZMod N)ˣ, S * f b) = ∑ b : (ZMod N)ˣ, S * f (u⁻¹ * b) :=
    (Equiv.sum_comp (Equiv.mulLeft u⁻¹) (fun b => S * f b)).symm
  rw [hreindex, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have hindex : (π u)⁻¹ * (π (u⁻¹ * b))⁻¹ = (π b)⁻¹ := by
    rw [← mul_inv_rev, ← map_mul, mul_comm, mul_inv_cancel_left]
  dsimp only [S, f]
  rw [MonoidAlgebra.single_mul_single, hindex, ← MonoidAlgebra.single_sub]
  apply congrArg (MonoidAlgebra.single (π b)⁻¹)
  unfold smoothedBernoulliCoefficient inverseSmoothingResidue
  ring

/-- The Euclidean quotient with the integral smoothing correction at weight one. -/
def smoothedWeightOneCoefficient (a : ℕ) (ha : a.Coprime N) (b : (ZMod N)ˣ) : ℤ :=
  ((a * inverseSmoothingResidue a ha b / N : ℕ) : ℤ) - (a / 2 : ℕ)

/-- At weight one the smoothed coefficient is the Euclidean quotient minus
the half-integer smoothing correction, which is integral for odd `a`. -/
theorem smoothedBernoulliCoefficient_one
    (a : ℕ) (ha : a.Coprime N) (hodd : Odd a) (b : (ZMod N)ˣ) :
    smoothedBernoulliCoefficient 1 a ha b = (smoothedWeightOneCoefficient a ha b : ℚ) := by
  rw [smoothedWeightOneCoefficient, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  let y := inverseSmoothingResidue a ha b
  let x := (b : ZMod N).val
  let q := a * y / N
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hxy : (a : ℚ) * y = (x : ℚ) + (N : ℚ) * q := by
    exact_mod_cast mul_inverseSmoothingResidue_eq a ha b
  have hdiv : (a : ℚ) * ((y : ℚ) / N) = (x : ℚ) / N + q := by
    rw [← mul_div_assoc, hxy, add_div, mul_div_cancel_left₀ _ hN]
  have ha' : a = 2 * (a / 2) + 1 := by obtain ⟨d, hd⟩ := hodd; omega
  have haQ : (a : ℚ) = 2 * ((a / 2 : ℕ) : ℚ) + 1 := by exact_mod_cast ha'
  have hB (r : ℕ) : generalizedBernoulliCoefficient N 1 r = (r : ℚ) / N - (2 : ℚ)⁻¹ := by
    simp [generalizedBernoulliCoefficient, Polynomial.bernoulli_one]
  change ((a : ℚ) ^ 1 * generalizedBernoulliCoefficient N 1 y -
    generalizedBernoulliCoefficient N 1 x) / (1 : ℚ) = (q : ℚ) - ((a / 2 : ℕ) : ℚ)
  rw [hB, hB, pow_one, div_one, mul_sub, hdiv, haQ]
  ring

variable [Group G] in
/-- The integral weight-one element with each contribution twisted by the
corresponding residue raised to the given power. -/
noncomputable def twistedWeightOneStickelberger
    (π : (ZMod N)ˣ →* G) (i a : ℕ) (ha : a.Coprime N) : MonoidAlgebra ℤ G :=
  ∑ b : (ZMod N)ˣ, MonoidAlgebra.single (π b)⁻¹
    (smoothedWeightOneCoefficient a ha b * ((b : ZMod N).val : ℤ) ^ i)

variable [CommGroup G] in
theorem map_twistedWeightOneStickelberger_zero
    (π : (ZMod N)ˣ →* G) (a : ℕ) (ha : a.Coprime N) (hodd : Odd a) :
    MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ) (twistedWeightOneStickelberger π 0 a ha) =
      rationalHigherStickelberger π 1 a ha := by
  rw [rationalHigherStickelberger_eq_sum_smoothedBernoulliCoefficient, twistedWeightOneStickelberger, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [smoothedBernoulliCoefficient_one a ha hodd b]
  simp only [pow_zero, mul_one, MonoidAlgebra.mapRingHom_single]
  rfl

end Utilities
