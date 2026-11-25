module

public import Utilities.SelmerKernel
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
variable (A : DiscreteGaloisModule k G) (S : Set (Subgroup G))

/-- If multiplication by a scalar is surjective on the coefficient module,
every Selmer class killed by that scalar has a cocycle representative killed by it. -/
theorem map_torsionBy_mkQ_eq (a : k) (ha : Function.Surjective (fun x : A.rep => a • x)) :
    let C := A.locallyTrivialCocycles₁ S
    let B := (coboundaries₁ A.rep).comap C.subtype
    (Submodule.torsionBy k C a).map B.mkQ = Submodule.torsionBy k (A.selmerKernel S) a := by
  intro C B
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a • x = 0 at hx
    change a • B.mkQ x = 0
    rw [← map_smul, hx, map_zero]
  · intro hz
    obtain ⟨f, rfl⟩ := B.mkQ_surjective z
    have hf : a • f ∈ B := (Submodule.Quotient.mk_eq_zero B).mp (by
      change B.mkQ (a • f) = 0
      rw [map_smul]
      exact hz)
    change (a • f).val ∈ coboundaries₁ A.rep at hf
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy⟩ := ha x
    change a • y = x at hy
    have hyBoundary : d₀₁ A.rep y ∈ coboundaries₁ A.rep := ⟨y, rfl⟩
    let c : C := ⟨d₀₁ A.rep y, A.coboundaries₁_le_locallyTrivial S hyBoundary⟩
    have hc : c ∈ B := hyBoundary
    have hfc : a • f = a • c := by
      apply Subtype.ext
      change (a • f).val = a • d₀₁ A.rep y
      rw [← map_smul, hy, hx]
    refine ⟨f - c, ?_, ?_⟩
    · change a • (f - c) = 0
      rw [smul_sub, hfc, sub_self]
    · have hcq : B.mkQ c = 0 := (Submodule.Quotient.mk_eq_zero B).mpr hc
      rw [map_sub, hcq, sub_zero]

/-- The size of the first torsion layer is bounded by that of the torsion cocycles. -/
theorem module_length_torsionBy_selmerKernel_le (a : k)
    (ha : Function.Surjective (fun x : A.rep => a • x)) :
    Module.length k (Submodule.torsionBy k (A.selmerKernel S) a) ≤
      Module.length k (Submodule.torsionBy k (A.locallyTrivialCocycles₁ S) a) := by
  let C := A.locallyTrivialCocycles₁ S
  let B := (coboundaries₁ A.rep).comap C.subtype
  let f := B.mkQ.comp (Submodule.torsionBy k C a).subtype
  have hf : f.range = Submodule.torsionBy k (A.selmerKernel S) a := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact A.map_torsionBy_mkQ_eq S a ha
  rw [← hf]
  exact Module.length_le_of_surjective _ f.surjective_rangeRestrict

end Utilities.DiscreteGaloisModule
