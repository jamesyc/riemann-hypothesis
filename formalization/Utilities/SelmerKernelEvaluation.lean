module

public import Utilities.SelmerKernel
import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
variable (A : DiscreteGaloisModule k G) (D : Set (Subgroup G))
variable (H : Subgroup G) (hH : ∀ σ ∈ H, A.rep.ρ σ = 1)

/-- On a subgroup acting trivially on the coefficients, evaluation descends
from cocycles to classes because every coboundary vanishes there. -/
def restrictSelmerKernelToTrivialSubgroup : A.selmerKernel D →ₗ[k] (H → A.rep) := by
  let C := A.locallyTrivialCocycles₁ D
  let B := (coboundaries₁ A.rep).comap C.subtype
  let restrict : C →ₗ[k] (H → A.rep) :=
    { toFun := fun c σ => c.val σ.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply B.liftQ restrict
  intro c hc
  obtain ⟨a, ha⟩ := show c.val ∈ coboundaries₁ A.rep from hc
  apply LinearMap.mem_ker.mpr
  funext σ
  change c.val σ.val = 0
  have heq : A.rep.ρ σ.val a - a = c.val σ.val := congrFun ha σ.val
  rw [← heq, hH _ σ.property, one_apply_eq_self, sub_self]

@[simp]
theorem restrictSelmerKernelToTrivialSubgroup_mk
    (c : A.locallyTrivialCocycles₁ D) (σ : H) :
    A.restrictSelmerKernelToTrivialSubgroup D H hH (Submodule.Quotient.mk c) σ =
      c.val σ.val := rfl

/-- The restriction of a Selmer class is an additive homomorphism on the
trivial-action subgroup, written additively in its argument. -/
def selmerRestrictionAddHom (x : A.selmerKernel D) : Additive H →+ A.rep where
  toFun σ := A.restrictSelmerKernelToTrivialSubgroup D H hH x σ.toMul
  map_zero' := by
    let C := A.locallyTrivialCocycles₁ D
    let B := (coboundaries₁ A.rep).comap C.subtype
    obtain ⟨c, rfl⟩ := B.mkQ_surjective x
    exact cocycles₁_map_one (⟨c.val, c.property.1.1⟩ : cocycles₁ A.rep)
  map_add' := by
    intro σ τ
    let C := A.locallyTrivialCocycles₁ D
    let B := (coboundaries₁ A.rep).comap C.subtype
    obtain ⟨c, rfl⟩ := B.mkQ_surjective x
    change c.val (σ.toMul.val * τ.toMul.val) = c.val σ.toMul.val + c.val τ.toMul.val
    rw [(mem_cocycles₁_iff c.val).mp c.property.1.1, hH _ σ.toMul.property,
      one_apply_eq_self, add_comm]

theorem isLocallyConstant_restrictSelmerKernelToTrivialSubgroup (x : A.selmerKernel D) :
    IsLocallyConstant (A.restrictSelmerKernelToTrivialSubgroup D H hH x) := by
  let C := A.locallyTrivialCocycles₁ D
  let B := (coboundaries₁ A.rep).comap C.subtype
  obtain ⟨c, rfl⟩ := B.mkQ_surjective x
  exact c.property.1.2.comp_continuous continuous_subtype_val

/-- At an argument in one of the Selmer local subgroups and in the
trivial-action subgroup, the restricted class evaluates to zero. -/
theorem restrictSelmerKernelToTrivialSubgroup_eq_zero_of_mem
    (x : A.selmerKernel D) (σ : H) {L : Subgroup G} (hL : L ∈ D) (hσ : σ.val ∈ L) :
    A.restrictSelmerKernelToTrivialSubgroup D H hH x σ = 0 := by
  let C := A.locallyTrivialCocycles₁ D
  let B := (coboundaries₁ A.rep).comap C.subtype
  obtain ⟨c, rfl⟩ := B.mkQ_surjective x
  obtain ⟨a, ha⟩ := c.property.2 L hL
  change c.val σ.val = 0
  rw [ha _ hσ, hH _ σ.property, one_apply_eq_self, sub_self]

end Utilities.DiscreteGaloisModule
