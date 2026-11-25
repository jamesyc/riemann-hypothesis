module

public import Utilities.PadicTateTwist
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Compactness.Compact

@[expose] public section

namespace Utilities

/-- Divide by a scalar and reduce modulo the p-adic integers. -/
noncomputable def padicTateTorsionMap (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
    ℤ_[p] →ₗ[ℤ_[p]] PadicTateQuotient p :=
  (padicIntegerImage p).mkQ.comp ((a : ℚ_[p])⁻¹ • Algebra.linearMap ℤ_[p] ℚ_[p])

theorem padicTateTorsionMap_apply (p : ℕ) [Fact p.Prime] (a x : ℤ_[p]) :
    padicTateTorsionMap p a x = (padicIntegerImage p).mkQ ((a : ℚ_[p])⁻¹ * x) := rfl

theorem padicTateTorsionMap_ker (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) (ha : a ≠ 0) :
    (padicTateTorsionMap p a).ker = Ideal.span {a} := by
  have haQ : (a : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr ha
  ext x
  rw [LinearMap.mem_ker, padicTateTorsionMap_apply, Ideal.mem_span_singleton]
  constructor
  · intro hzero
    have h : (a : ℚ_[p])⁻¹ * x ∈ padicIntegerImage p :=
      (Submodule.Quotient.mk_eq_zero _).mp hzero
    obtain ⟨y, hy⟩ := h
    change (y : ℚ_[p]) = (a : ℚ_[p])⁻¹ * x at hy
    refine ⟨y, ?_⟩
    apply Subtype.ext
    rw [PadicInt.coe_mul, hy, ← mul_assoc, mul_inv_cancel₀ haQ, one_mul]
  · rintro ⟨y, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨y, ?_⟩
    change (y : ℚ_[p]) = (a : ℚ_[p])⁻¹ * ((a * y : ℤ_[p]) : ℚ_[p])
    rw [PadicInt.coe_mul, ← mul_assoc, inv_mul_cancel₀ haQ, one_mul]

theorem padicTateTorsionMap_range (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) (ha : a ≠ 0) :
    (padicTateTorsionMap p a).range = Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) a := by
  have haQ : (a : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr ha
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change a • padicTateTorsionMap p a x = 0
    rw [← map_smul, ← LinearMap.mem_ker, padicTateTorsionMap_ker p a ha, Ideal.mem_span_singleton]
    exact ⟨x, rfl⟩
  · intro hz
    obtain ⟨b, rfl⟩ := (padicIntegerImage p).mkQ_surjective z
    have hb : a • b ∈ padicIntegerImage p :=
      (Submodule.Quotient.mk_eq_zero _).mp (by
        change (padicIntegerImage p).mkQ (a • b) = 0
        rw [map_smul]
        exact hz)
    obtain ⟨x, hx⟩ := hb
    change (x : ℚ_[p]) = (a : ℚ_[p]) * b at hx
    exact ⟨x, by rw [padicTateTorsionMap_apply, hx, ← mul_assoc, inv_mul_cancel₀ haQ, one_mul]⟩

/-- The torsion map for the prime itself. -/
noncomputable def padicTateFirstTorsionMap (p : ℕ) [Fact p.Prime] :
    ℤ_[p] →ₗ[ℤ_[p]] PadicTateQuotient p :=
  padicTateTorsionMap p (p : ℤ_[p])

theorem padicTateFirstTorsionMap_apply (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
    padicTateFirstTorsionMap p a = (padicIntegerImage p).mkQ ((p : ℚ_[p])⁻¹ * a) := rfl

theorem padicTateFirstTorsionMap_ker (p : ℕ) [Fact p.Prime] :
    (padicTateFirstTorsionMap p).ker = IsLocalRing.maximalIdeal ℤ_[p] := by
  rw [padicTateFirstTorsionMap, padicTateTorsionMap_ker, PadicInt.maximalIdeal_eq_span_p]
  exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

theorem padicTateFirstTorsionMap_range (p : ℕ) [Fact p.Prime] :
    (padicTateFirstTorsionMap p).range = Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) (p : ℤ_[p]) :=
  padicTateTorsionMap_range p _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- The p-torsion of `ℚp/ℤp` is additively the residue field. -/
noncomputable def padicTateFirstTorsionAddEquivZMod (p : ℕ) [Fact p.Prime] :
    Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) (p : ℤ_[p]) ≃+ ZMod p := by
  let f := padicTateFirstTorsionMap p
  let e := (LinearEquiv.ofEq _ _ (padicTateFirstTorsionMap_range p)).symm.trans f.quotKerEquivRange.symm
  let e' := e.trans (Submodule.quotEquivOfEq _ _ (padicTateFirstTorsionMap_ker p))
  exact e'.toAddEquiv.trans PadicInt.residueField.toAddEquiv

/-- Every element of the Tate coefficient quotient is killed by a prime power. -/
theorem exists_pow_smul_eq_zero_padicTateQuotient (p : ℕ) [Fact p.Prime]
    (a : PadicTateQuotient p) : ∃ r : ℕ, (p : ℤ_[p]) ^ r • a = 0 := by
  obtain ⟨b, rfl⟩ := (padicIntegerImage p).mkQ_surjective a
  by_cases hb : b = 0
  · simp [hb]
  let r := b.valuation.natAbs
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hval : 0 ≤ (((p : ℚ_[p]) ^ r) * b).valuation := by
    rw [Padic.valuation_mul (pow_ne_zero _ hp) hb, Padic.valuation_pow, Padic.valuation_p, mul_one]
    dsimp only [r]
    omega
  refine ⟨r, ?_⟩
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero (padicIntegerImage p)).mpr
    ⟨Padic.lift _ ((Padic.norm_le_one_iff_val_nonneg _).mpr hval), rfl⟩

/-- A higher power of a scalar kills any vector killed by a lower power. -/
theorem pow_smul_eq_zero_of_le {R X : Type*} [CommSemiring R] [AddCommMonoid X] [Module R X]
    {a : R} {x : X} {m n : ℕ} (h : m ≤ n) (hx : a ^ m • x = 0) : a ^ n • x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm, mul_smul, hx, smul_zero]

/-- Compactness bounds the prime-power torsion of a continuous cocycle uniformly
over its Galois arguments, and therefore also bounds each Selmer class. -/
theorem exists_pow_smul_eq_zero_padicTateSelmerKernel (F : Type) [Field F]
    [CompactSpace (Field.absoluteGaloisGroup F)] (p : ℕ) [Fact p.Prime] (i : ℕ)
    (D : Set (Subgroup (Field.absoluteGaloisGroup F)))
    (x : (padicTateTwist F p i).selmerKernel D) : ∃ r : ℕ, (p : ℤ_[p]) ^ r • x = 0 := by
  let A := padicTateTwist F p i
  let C := A.locallyTrivialCocycles₁ D
  let B := (groupCohomology.coboundaries₁ A.rep).comap C.subtype
  obtain ⟨c, rfl⟩ := B.mkQ_surjective x
  let _ : TopologicalSpace A.rep := ⊥
  let _ : DiscreteTopology A.rep := ⟨rfl⟩
  have hc : Continuous c.val := c.property.1.2.continuous
  have hfinite : (Set.range c.val).Finite :=
    (isCompact_range hc).finite ((isDiscrete_univ_iff.mpr inferInstance).mono (Set.subset_univ _))
  choose n hn using fun a : A.rep => exists_pow_smul_eq_zero_padicTateQuotient p a
  obtain ⟨r, hr⟩ := (hfinite.image n).bddAbove
  refine ⟨r, ?_⟩
  have hrc : (p : ℤ_[p]) ^ r • c = 0 := by
    apply Subtype.ext
    funext g
    change (p : ℤ_[p]) ^ r • c.val g = 0
    have hgr : n (c.val g) ≤ r := hr (Set.mem_image_of_mem n ⟨g, rfl⟩)
    exact pow_smul_eq_zero_of_le hgr (hn (c.val g))
  rw [← map_smul, hrc, map_zero]

end Utilities
