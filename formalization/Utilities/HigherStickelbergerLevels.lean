module

public import Utilities.HigherStickelberger
import Utilities.GeneralizedBernoulliDistribution
import Utilities.ZModUnits

@[expose] public section

namespace Utilities

variable {N m : ℕ} [NeZero N] [NeZero m] {G : Type*} [CommGroup G]

/-- The rational theta element is compatible with extending the level
without introducing any new prime divisors. -/
theorem rationalStickelbergerTheta_mul_level
    (hcoprime : ∀ r : ℕ, r.Coprime N → r.Coprime (N * m))
    (π : (ZMod N)ˣ →* G) (k : ℕ) :
    rationalStickelbergerTheta (π.comp (ZMod.unitsMap (dvd_mul_right N m))) k =
      rationalStickelbergerTheta π k := by
  unfold rationalStickelbergerTheta
  congr 1
  simp only [MonoidHom.comp_apply]
  rw [sum_zmodUnits_mul_level hcoprime fun b r =>
    MonoidAlgebra.single (π b)⁻¹ (generalizedBernoulliCoefficient (N * m) k r / k)]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ j ∈ Finset.range m, (MonoidAlgebra.singleAddHom (π b)⁻¹)
    (generalizedBernoulliCoefficient (N * m) k ((b : ZMod N).val + j * N) / k)) = _
  rw [← map_sum, ← Finset.sum_div,
    ← generalizedBernoulliCoefficient_distribution (NeZero.pos N) (NeZero.pos m)]
  rfl

/-- Smoothing commutes with changing to a level with the same prime divisors. -/
theorem rationalHigherStickelberger_mul_level
    (hcoprime : ∀ r : ℕ, r.Coprime N → r.Coprime (N * m))
    (π : (ZMod N)ˣ →* G) (k a : ℕ) (ha : a.Coprime N) :
    rationalHigherStickelberger (π.comp (ZMod.unitsMap (dvd_mul_right N m))) k a (hcoprime a ha) =
      rationalHigherStickelberger π k a ha := by
  simp only [rationalHigherStickelberger, rationalStickelbergerTheta_mul_level hcoprime,
    MonoidHom.comp_apply, zmodUnitsMap_unitOfCoprime _ ha]

/-- The higher element at level `N * p ^ j` descends to the same rational element
at level `N` when `p` already divides `N`. -/
theorem rationalHigherStickelberger_mul_pow {p : ℕ} [NeZero p] (hpN : p ∣ N)
    (π : (ZMod N)ˣ →* G) (j k a : ℕ) (ha : a.Coprime N) :
    rationalHigherStickelberger (π.comp (ZMod.unitsMap (dvd_mul_right N (p ^ j)))) k a
      (ha.mul_right ((ha.coprime_dvd_right hpN).pow_right j)) =
      rationalHigherStickelberger π k a ha :=
  rationalHigherStickelberger_mul_level
    (fun _ hr => hr.mul_right ((hr.coprime_dvd_right hpN).pow_right j)) π k a ha

end Utilities
