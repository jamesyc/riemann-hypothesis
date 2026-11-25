module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

@[expose] public section

open IsDedekindDomain

namespace Utilities

variable {R K V Y : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [AddCommGroup Y] [Module R Y] [Module K Y] [IsScalarTower R K Y]

/-- A field-valued bilinear pairing whose values on the two lattices are
integral at every finite place takes values in the integral dual. -/
theorem exists_integralDualMap_of_valuation_le_one
    (N : Submodule R V) (M : Submodule R Y) (B : V →ₗ[K] Y →ₗ[K] K)
    (hval : ∀ (v : HeightOneSpectrum R) (z : N) (y : M),
      v.valuation K (B z y) ≤ 1) :
    ∃ B₀ : N →ₗ[R] Module.Dual R M, ∀ (z : N) (y : M),
      algebraMap R K (B₀ z y) = B z y := by
  let k : R →ₗ[R] K := Algebra.linearMap R K
  have hk : Function.Injective k := IsFractionRing.injective R K
  have hint (z : N) (y : M) : B (N.subtype z) (M.subtype y) ∈ LinearMap.range k :=
    HeightOneSpectrum.mem_integers_of_valuation_le_one K _ (fun v => hval v z y)
  refine ⟨LinearMap.restrictScalarsRange₂ N.subtype M.subtype k hk B hint, ?_⟩
  exact fun z y => LinearMap.restrictScalarsRange₂_apply N.subtype M.subtype k hk B hint z y

/-- The same integrality conclusion when the local divisibility is stated on
unscaled lattices and the input lattice lies in their rescalings by
`(π v ^ s v)⁻¹`. For a uniformizer the divisibility inequality is the
additive valuation bound `ordᵥ ≥ s v`. -/
theorem exists_integralDualMap_of_local_divisibility
    (N : Submodule R V) (M : Submodule R Y) (B : V →ₗ[K] Y →ₗ[K] K)
    (N₀ : HeightOneSpectrum R → Set V) (π : HeightOneSpectrum R → K)
    (s : HeightOneSpectrum R → ℕ) (hπ : ∀ v, π v ≠ 0)
    (hval : ∀ (v : HeightOneSpectrum R) (z : V), z ∈ N₀ v → ∀ y : M,
      v.valuation K (B z y) ≤ v.valuation K (π v) ^ s v)
    (hrescale : ∀ (v : HeightOneSpectrum R) (z : N), ∃ z₀ ∈ N₀ v,
      (z : V) = (π v ^ s v)⁻¹ • z₀) :
    ∃ B₀ : N →ₗ[R] Module.Dual R M, ∀ (z : N) (y : M),
      algebraMap R K (B₀ z y) = B z y := by
  apply exists_integralDualMap_of_valuation_le_one N M B
  intro v z y
  obtain ⟨z₀, hz₀, hz⟩ := hrescale v z
  have hp : v.valuation K (π v) ^ s v ≠ 0 :=
    pow_ne_zero _ ((v.valuation K).ne_zero_iff.mpr (hπ v))
  rw [hz, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_pow]
  exact (mul_le_mul_of_nonneg_left (hval v z₀ hz₀ y) zero_le).trans_eq
    (inv_mul_cancel₀ hp)

end Utilities
