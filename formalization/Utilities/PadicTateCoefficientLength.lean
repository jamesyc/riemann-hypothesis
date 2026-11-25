module

public import Utilities.PadicTateTorsion
public import Utilities.DVREvaluationLength
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

open scoped TensorProduct

namespace Utilities

variable (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [Algebra ℤ_[p] S]
local notation "W" => S ⊗[ℤ_[p]] PadicTateQuotient p

private theorem baseChange_smul_id_apply {M : Type} [AddCommGroup M] [Module ℤ_[p] M]
    (a : ℤ_[p]) (x : S ⊗[ℤ_[p]] M) :
    (a • (LinearMap.id : M →ₗ[ℤ_[p]] M)).baseChange S x = algebraMap ℤ_[p] S a • x := by
  rw [LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply,
    IsScalarTower.algebraMap_smul]

/-- Flat scalar extension preserves the cyclic torsion layers of the Tate
coefficient and their annihilators. -/
theorem exists_extendedPadicTate_torsion_generator [Module.Flat ℤ_[p] S]
    (a : ℤ_[p]) (ha : a ≠ 0) :
    ∃ w : W, (∀ y : S, y • w = 0 ↔ algebraMap ℤ_[p] S a ∣ y) ∧
      ∀ x : W, algebraMap ℤ_[p] S a • x = 0 → ∃ y : S, y • w = x := by
  let f := padicTateTorsionMap p a
  let m := a • (LinearMap.id : ℤ_[p] →ₗ[ℤ_[p]] ℤ_[p])
  let t := a • (LinearMap.id : PadicTateQuotient p →ₗ[ℤ_[p]] PadicTateQuotient p)
  let u := TensorProduct.AlgebraTensorModule.rid ℤ_[p] S S
  have hm : m.range = Ideal.span {a} := by
    ext x
    rw [LinearMap.mem_range, Ideal.mem_span_singleton]
    exact exists_congr fun y => eq_comm
  have hex₁ : Function.Exact m f :=
    LinearMap.exact_iff.mpr ((padicTateTorsionMap_ker p a ha).trans hm.symm)
  have hex₂ : Function.Exact f t := by
    rw [LinearMap.exact_iff, padicTateTorsionMap_range p a ha]
    rfl
  have h₁ : Function.Exact (m.baseChange S) (f.baseChange S) :=
    Module.Flat.lTensor_exact S hex₁
  have h₂ : Function.Exact (f.baseChange S) (t.baseChange S) :=
    Module.Flat.lTensor_exact S hex₂
  let g : S →ₗ[S] W := (f.baseChange S).comp u.symm.toLinearMap
  have hg (y : S) : g y = y • g 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  refine ⟨g 1, fun y => ?_, fun x hx => ?_⟩
  · rw [← hg]
    change f.baseChange S (u.symm y) = 0 ↔ algebraMap ℤ_[p] S a ∣ y
    rw [h₁]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨u z, ?_⟩
      rw [baseChange_smul_id_apply p S a] at hz
      simpa only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul] using
        (congrArg u hz).symm
    · rintro ⟨z, rfl⟩
      refine ⟨u.symm z, ?_⟩
      rw [baseChange_smul_id_apply p S a, ← map_smul, smul_eq_mul]
  · have ht : t.baseChange S x = 0 := by
      dsimp only [t]
      rwa [baseChange_smul_id_apply p S a]
    obtain ⟨z, hz⟩ := (h₂ x).mp ht
    exact ⟨u z, by rw [← hg]; simpa only [g, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hz⟩

/-- A divisor of a prime power has a cyclic Tate coefficient layer with the
specified principal annihilator. -/
theorem exists_extendedPadicTate_torsion_generator_of_dvd_pow [IsDomain S] [Module.Flat ℤ_[p] S]
    (hpS : (p : S) ≠ 0) {a : S} (r : ℕ) (hdvd : a ∣ (p : S) ^ r) :
    ∃ w : W, (∀ y : S, y • w = 0 ↔ a ∣ y) ∧
      ∀ x : W, a • x = 0 → ∃ y : S, y • w = x := by
  have hp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpow : (p : S) ^ r ≠ 0 := pow_ne_zero _ hpS
  obtain ⟨v, hv, hspan⟩ := exists_extendedPadicTate_torsion_generator p S ((p : ℤ_[p]) ^ r) (pow_ne_zero _ hp)
  rw [map_pow, map_natCast] at hv hspan
  obtain ⟨b, hb⟩ := hdvd
  have hab : a * b ≠ 0 := hb ▸ hpow
  have ha : a ≠ 0 := left_ne_zero_of_mul hab
  have hb₀ : b ≠ 0 := right_ne_zero_of_mul hab
  rw [hb] at hv hspan
  refine ⟨b • v, fun y => ?_, fun x hx => ?_⟩
  · rw [smul_smul, hv, mul_dvd_mul_iff_right hb₀]
  · obtain ⟨y, hy⟩ := hspan x (by rw [mul_comm, mul_smul, hx, smul_zero])
    have hkill : (a * y) • v = 0 := by rw [mul_smul, hy, hx]
    have hdiv : b ∣ y := (mul_dvd_mul_iff_left ha).mp ((hv _).mp hkill)
    obtain ⟨z, rfl⟩ := hdiv
    exact ⟨z, by rw [smul_smul, mul_comm, hy]⟩

/-- The length of a torsion slice in the scalar-extended Tate module is
the valuation of its annihilator. -/
theorem extendedPadicTate_length_torsionBy_of_dvd_pow [IsDomain S] [IsDiscreteValuationRing S]
    [Module.Flat ℤ_[p] S] (hpS : (p : S) ≠ 0) {a : S} (r : ℕ) (hdvd : a ∣ (p : S) ^ r) :
    Module.length S (Submodule.torsionBy S W a) = IsDiscreteValuationRing.addVal S a := by
  have ha : a ≠ 0 := fun h => (pow_ne_zero r hpS) (zero_dvd_iff.mp (h ▸ hdvd))
  obtain ⟨w, hann, hspan⟩ := exists_extendedPadicTate_torsion_generator_of_dvd_pow p S hpS r hdvd
  exact dvr_length_torsionBy_of_generator ha w hann hspan

end Utilities
