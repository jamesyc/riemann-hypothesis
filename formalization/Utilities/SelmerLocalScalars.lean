module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Utilities.SelmerLocalVanishing

@[expose] public section

namespace Utilities

/-- Multiplication by a nonzero coefficient is surjective on the fraction
field modulo the coefficient ring. -/
theorem fractionQuotient_smul_surjective {O F : Type*} [CommRing O] [Field F] [Algebra O F]
    (a : O) (ha : algebraMap O F a ≠ 0) :
    Function.Surjective (fun x : F ⧸ LinearMap.range (Algebra.linearMap O F) => a • x) := by
  let Q := LinearMap.range (Algebra.linearMap O F)
  intro y
  obtain ⟨b, rfl⟩ := Q.mkQ_surjective y
  refine ⟨Q.mkQ ((algebraMap O F a)⁻¹ * b), ?_⟩
  change a • Q.mkQ ((algebraMap O F a)⁻¹ * b) = Q.mkQ b
  rw [← map_smul, Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- A nontrivial root of unity of invertible order has invertible
difference from one. This supplies the ramified scalar in Lemma 17.18. -/
theorem isUnit_root_sub_one_of_isUnit_order {O : Type*} [CommRing O] [IsDomain O] {z : O} {n : ℕ}
    (hn : IsUnit (n : O)) (hz : z ^ n = 1) (hne : z ≠ 1) :
    IsUnit (z - 1) :=
  isUnit_of_dvd_unit (sub_one_dvd_natCast_of_pow_eq_one hz hne) hn

/-- A positive Frobenius norm to a positive twist cannot equal a root of
unity in characteristic zero. -/
theorem natCast_pow_mul_root_ne_one {F : Type*} [Field F] [CharZero F]
    {q e n : ℕ} {z : F} (hq : 2 ≤ q) (he : 0 < e) (hn : 0 < n) (hz : z ^ n = 1) :
    (q : F) ^ e * z ≠ 1 := by
  intro h
  have hpow := congrArg (fun x : F => x ^ n) h
  rw [mul_pow, hz, mul_one, one_pow, ← pow_mul] at hpow
  have hq₁ : 1 < q := by omega
  have hlt : 1 < q ^ (e * n) := one_lt_pow₀ hq₁ (Nat.mul_pos he hn).ne'
  have heq : q ^ (e * n) = 1 := by exact_mod_cast hpow
  omega

namespace DiscreteGaloisModule

variable {O F G : Type} [CommRing O] [Field F] [Algebra O F]
  [Group G] [TopologicalSpace G]

/-- The ramified case of Lemma 17.18 on the actual fraction-field quotient
module. A local root of unity of invertible order kills the inertia invariants. -/
theorem exists_coboundary_of_ramified_scalar [IsDomain O]
    (A : DiscreteGaloisModule O G) {f : G → A.rep} (hf : f ∈ A.continuousCocycles₁)
    (j : A.rep ≃ₗ[O] (F ⧸ LinearMap.range (Algebra.linearMap O F)))
    (scalar : G → O) (hscalar : ∀ g a, j (A.rep.ρ g a) = scalar g • j a)
    (D : Subgroup G) (hD : D.Normal)
    (hram : ∃ d ∈ D, ∃ n : ℕ, IsUnit (n : O) ∧ scalar d ^ n = 1 ∧ scalar d ≠ 1)
    (hloc : ∃ a : A.rep, ∀ d ∈ D, f d = A.rep.ρ d a - a) :
    ∃ a : A.rep, ∀ g, f g = A.rep.ρ g a - a := by
  apply exists_coboundary_of_trivial_on_normal_of_no_fixed A hf D hD _ hloc
  intro a ha
  obtain ⟨d, hd, n, hn, hpow, hne⟩ := hram
  have hu := isUnit_root_sub_one_of_isUnit_order hn hpow hne
  apply j.injective
  rw [map_zero, ← hu.smul_eq_zero, sub_smul, one_smul, ← hscalar, ha d hd, sub_self]

/-- The unramified case of Lemma 17.18 with the geometric Frobenius scalar.
The quotient topology enters through dense generation, and surjectivity
follows on the fraction-field quotient. -/
theorem exists_coboundary_of_unramified_frobenius_scalar [CharZero F]
    (A : DiscreteGaloisModule O G) {f : G → A.rep} (hf : f ∈ A.continuousCocycles₁)
    (j : A.rep ≃ₗ[O] (F ⧸ LinearMap.range (Algebra.linearMap O F)))
    (scalar : G → O) (hscalar : ∀ g a, j (A.rep.ρ g a) = scalar g • j a)
    (D : Subgroup G) (φ : G)
    (hdense : Dense ((D ⊔ Subgroup.zpowers φ : Subgroup G) : Set G))
    (htriv : ∀ d ∈ D, scalar d = 1)
    {q e n : ℕ} {z : F} (hq : 2 ≤ q) (he : 0 < e) (hn : 0 < n) (hz : z ^ n = 1)
    (hφ : algebraMap O F (scalar φ) = ((q : F) ^ e * z)⁻¹)
    (hloc : ∃ a : A.rep, ∀ d ∈ D, f d = A.rep.ρ d a - a) :
    ∃ a : A.rep, ∀ g, f g = A.rep.ρ g a - a := by
  apply exists_coboundary_of_trivial_inertia_of_frobenius_surjective A hf D φ hdense _ _ hloc
  · intro d hd a
    apply j.injective
    rw [hscalar, htriv d hd, one_smul]
  · have hcoeff : algebraMap O F (scalar φ - 1) ≠ 0 := by
      rw [map_sub, map_one, hφ, sub_ne_zero]
      intro heq
      exact natCast_pow_mul_root_ne_one hq he hn hz (by simpa using congrArg Inv.inv heq)
    intro a
    obtain ⟨x, hx⟩ := fractionQuotient_smul_surjective (scalar φ - 1) hcoeff (j a)
    refine ⟨j.symm x, j.injective ?_⟩
    simpa only [map_sub, hscalar, LinearEquiv.apply_symm_apply, sub_smul, one_smul] using hx

end DiscreteGaloisModule

end Utilities
