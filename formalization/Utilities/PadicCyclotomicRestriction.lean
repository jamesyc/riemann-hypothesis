module

public import Utilities.PadicCyclotomicImage
public import Utilities.PadicTateTwist
public import Utilities.SelmerKernelEvaluation
import Utilities.CyclotomicRestriction
import Utilities.SelmerLocalVanishing
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Topology.Maps.Strict.Group

@[expose] public section

open groupCohomology

namespace Utilities

/-- The Tate action is trivial on the kernel of the cyclotomic character. -/
theorem padicTateTwist_ρ_apply_eq_self_on_padicCyclotomicKernel
    (F : Type) [Field F] (p : ℕ) [Fact p.Prime] (i : ℕ)
    {σ : Field.absoluteGaloisGroup F} (hσ : σ ∈ (padicCyclotomicUnitsMap F p).ker)
    (a : (padicTateTwist F p i).rep) :
    (padicTateTwist F p i).rep.ρ σ a = a := by
  let u := padicCyclotomicUnitsMap F p (show Gal(AlgebraicClosure F/F) from σ)
  have hu : u = 1 := MonoidHom.mem_ker.mp hσ
  change ((u ^ (-(i : ℤ)) : ℤ_[p]ˣ) : ℤ_[p]) • a = a
  rw [hu, one_zpow, Units.val_one, one_smul]

/-- Restriction to the kernel of the cyclotomic character detects continuous
first cohomology with coefficients in every nonzero negative Tate twist at an
odd prime. -/
theorem exists_tateCoboundary_of_zero_on_padicCyclotomicKernel
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (i : ℕ) (hi : 0 < i)
    {c : Field.absoluteGaloisGroup F → (padicTateTwist F p i).rep}
    (hc : c ∈ (padicTateTwist F p i).continuousCocycles₁)
    (hz : ∀ σ ∈ (padicCyclotomicUnitsMap F p).ker, c σ = 0) :
    ∃ a : (padicTateTwist F p i).rep, ∀ σ, c σ = (padicTateTwist F p i).rep.ρ σ a - a := by
  let χ : Field.absoluteGaloisGroup F →* ℤ_[p]ˣ := padicCyclotomicUnitsMap F p
  let A := padicTateTwist F p i
  obtain ⟨x, hx, hxord⟩ := exists_denseRange_zpow_padicCyclotomicUnitsMap F p hp
  change χ.range at x
  obtain ⟨τ, hτ⟩ := χ.rangeRestrict_surjective x
  let _ : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  have hχ : Continuous χ := padicCyclotomicUnitsMap_continuous F p
  let e := ContinuousMulEquiv.quotientKerEquivRange (hχ.isClosedMap.isStrictMap hχ)
  have he : e (QuotientGroup.mk' χ.ker τ) = x := hτ
  have he' : e.symm x = QuotientGroup.mk' χ.ker τ := by rw [← he, e.symm_apply_apply]
  have hdense : DenseRange (fun j : ℤ => QuotientGroup.mk' χ.ker τ ^ j) := by
    have hh := e.symm.surjective.denseRange.comp hx e.symm.continuous
    change DenseRange (fun j : ℤ => e.symm (x ^ j)) at hh
    have hpow : (fun j : ℤ => e.symm (x ^ j)) = (fun j : ℤ => (e.symm x) ^ j) :=
      funext (map_zpow e.symm x)
    rw [hpow, he'] at hh
    exact hh
  apply A.exists_coboundary_of_trivial_inertia_of_frobenius_surjective hc χ.ker τ
  · exact DiscreteGaloisModule.dense_sup_zpowers_of_dense_quotient χ.ker τ hdense
  · exact fun _ hσ => padicTateTwist_ρ_apply_eq_self_on_padicCyclotomicKernel F p i hσ
  · intro a
    let u : ℤ_[p]ˣ := χ τ ^ (-(i : ℤ))
    have hu : (u : ℤ_[p]) - 1 ≠ 0 := by
      intro h
      apply hxord
      refine isOfFinOrder_iff_zpow_eq_one.mpr ⟨-(i : ℤ), neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hi.ne'), ?_⟩
      rw [← hτ]
      apply Subtype.ext
      exact Units.ext (sub_eq_zero.mp h)
    obtain ⟨b, hb⟩ := padicTateQuotient_smul_surjective _ hu a
    exact ⟨b, by
      change (u : ℤ_[p]) • b - b = a
      simpa only [sub_smul, one_smul] using hb⟩
  · exact ⟨0, fun σ hσ => by simp [hz σ hσ]⟩

/-- If a cocycle vanishes on elements of the cyclotomic kernel that fix the
roots of order `N`, its totient multiple is a global coboundary. -/
theorem exists_tateCoboundary_totient_smul_of_zero_on_fixingRoots
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (i : ℕ) (hi : 0 < i) (N : ℕ) [NeZero N] (hN : 1 < N)
    {c : Field.absoluteGaloisGroup F → (padicTateTwist F p i).rep}
    (hc : c ∈ (padicTateTwist F p i).continuousCocycles₁)
    (hz : ∀ σ ∈ (padicCyclotomicUnitsMap F p).ker,
      (∀ ζ : AlgebraicClosure F, ζ ^ N = 1 → (show Gal(AlgebraicClosure F/F) from σ) ζ = ζ) →
      c σ = 0) :
    ∃ a : (padicTateTwist F p i).rep,
      ∀ σ, N.totient • c σ = (padicTateTwist F p i).rep.ρ σ a - a := by
  let A := padicTateTwist F p i
  have hc' : N.totient • c ∈ A.continuousCocycles₁ := A.continuousCocycles₁.nsmul_mem hc _
  refine exists_tateCoboundary_of_zero_on_padicCyclotomicKernel F p hp i hi hc' ?_
  intro σ hσ
  let H := (padicCyclotomicUnitsMap F p).ker
  have htriv (τ : Gal(AlgebraicClosure F/F)) (hτ : τ ∈ H) : A.rep.ρ τ = 1 :=
    LinearMap.ext fun a => padicTateTwist_ρ_apply_eq_self_on_padicCyclotomicKernel F p i hτ a
  exact totient_smul_cocycle_eq_zero_of_fixedRoots N hN A.rep H htriv ⟨c, hc.1⟩ hz hσ

/-- The finite-level vanishing criterion on a representative gives the
corresponding scalar annihilation on its Selmer class. -/
theorem totient_smul_selmerClass_eq_zero_of_zero_on_fixingRoots
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (i : ℕ) (hi : 0 < i) (N : ℕ) [NeZero N] (hN : 1 < N)
    (D : Set (Subgroup (Field.absoluteGaloisGroup F)))
    (c : (padicTateTwist F p i).locallyTrivialCocycles₁ D)
    (hz : ∀ σ ∈ (padicCyclotomicUnitsMap F p).ker,
      (∀ ζ : AlgebraicClosure F, ζ ^ N = 1 → (show Gal(AlgebraicClosure F/F) from σ) ζ = ζ) →
      c.val σ = 0) :
    N.totient • (Submodule.Quotient.mk c : (padicTateTwist F p i).selmerKernel D) = 0 := by
  let A := padicTateTwist F p i
  let B := (coboundaries₁ A.rep).comap (A.locallyTrivialCocycles₁ D).subtype
  obtain ⟨a, ha⟩ := exists_tateCoboundary_totient_smul_of_zero_on_fixingRoots F p hp i hi N hN
    c.property.1 hz
  change N.totient • B.mkQ c = 0
  rw [← map_nsmul]
  exact (Submodule.Quotient.mk_eq_zero B).mpr ⟨a, funext fun σ => (ha σ).symm⟩

/-- The kernel is viewed inside the absolute Galois group used for cohomology. -/
noncomputable abbrev padicCyclotomicKernel (F : Type) [Field F] (p : ℕ) [Fact p.Prime] :
    Subgroup (Field.absoluteGaloisGroup F) :=
  (show Field.absoluteGaloisGroup F →* ℤ_[p]ˣ from padicCyclotomicUnitsMap F p).ker

/-- Restriction of a Tate Selmer class to the cyclotomic kernel, where its
values are independent of the choice of cocycle representative. -/
noncomputable def padicTateSelmerRestriction (F : Type) [Field F] (p : ℕ) [Fact p.Prime] (i : ℕ)
    (D : Set (Subgroup (Field.absoluteGaloisGroup F))) :
    (padicTateTwist F p i).selmerKernel D →ₗ[ℤ_[p]]
      (padicCyclotomicKernel F p → (padicTateTwist F p i).rep) :=
  (padicTateTwist F p i).restrictSelmerKernelToTrivialSubgroup D (padicCyclotomicKernel F p)
    (fun _ hσ => LinearMap.ext (padicTateTwist_ρ_apply_eq_self_on_padicCyclotomicKernel F p i hσ))

@[simp]
theorem padicTateSelmerRestriction_mk (F : Type) [Field F] (p : ℕ) [Fact p.Prime] (i : ℕ)
    (D : Set (Subgroup (Field.absoluteGaloisGroup F)))
    (c : (padicTateTwist F p i).locallyTrivialCocycles₁ D) (σ : padicCyclotomicKernel F p) :
    padicTateSelmerRestriction F p i D (Submodule.Quotient.mk c) σ = c.val σ.val := rfl

/-- The finite-root vanishing condition stated directly on a Selmer class. -/
theorem totient_smul_selmerClass_eq_zero_of_restriction_eq_zero
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (i : ℕ) (hi : 0 < i) (N : ℕ) [NeZero N] (hN : 1 < N)
    (D : Set (Subgroup (Field.absoluteGaloisGroup F)))
    (x : (padicTateTwist F p i).selmerKernel D)
    (hz : ∀ σ : padicCyclotomicKernel F p,
      (∀ ζ : AlgebraicClosure F, ζ ^ N = 1 → (show Gal(AlgebraicClosure F/F) from σ.val) ζ = ζ) →
      padicTateSelmerRestriction F p i D x σ = 0) :
    N.totient • x = 0 := by
  let A := padicTateTwist F p i
  let B := (coboundaries₁ A.rep).comap (A.locallyTrivialCocycles₁ D).subtype
  obtain ⟨c, rfl⟩ := B.mkQ_surjective x
  exact totient_smul_selmerClass_eq_zero_of_zero_on_fixingRoots F p hp i hi N hN D c
    (fun σ hσ hfix => hz ⟨σ, hσ⟩ hfix)

end Utilities
