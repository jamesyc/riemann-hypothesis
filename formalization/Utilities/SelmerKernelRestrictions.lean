module

public import Utilities.SelmerKernel

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]

/-- Every cocycle trivial on a larger collection is trivial on a smaller one. -/
theorem locallyTrivialCocycles₁_le_of_subset (A : DiscreteGaloisModule k G)
    {S T : Set (Subgroup G)} (h : S ⊆ T) :
    A.locallyTrivialCocycles₁ T ≤ A.locallyTrivialCocycles₁ S :=
  fun _ hf => ⟨hf.1, fun D hD => hf.2 D (h hD)⟩

/-- The natural inclusion under weakening of local conditions. -/
def selmerKernel_of_subset (A : DiscreteGaloisModule k G)
    {S T : Set (Subgroup G)} (h : S ⊆ T) :
    A.selmerKernel T →ₗ[k] A.selmerKernel S := by
  let C := A.locallyTrivialCocycles₁ T
  let C' := A.locallyTrivialCocycles₁ S
  let B := (coboundaries₁ A.rep).comap C.subtype
  let B' := (coboundaries₁ A.rep).comap C'.subtype
  let f : C →ₗ[k] C' := Submodule.inclusion (A.locallyTrivialCocycles₁_le_of_subset h)
  exact B.mapQ B' f (fun _ hz => hz)

theorem selmerKernel_of_subset_injective (A : DiscreteGaloisModule k G)
    {S T : Set (Subgroup G)} (h : S ⊆ T) :
    Function.Injective (A.selmerKernel_of_subset h) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  let C := A.locallyTrivialCocycles₁ T
  let C' := A.locallyTrivialCocycles₁ S
  let B := (coboundaries₁ A.rep).comap C.subtype
  let B' := (coboundaries₁ A.rep).comap C'.subtype
  let f : C →ₗ[k] C' := Submodule.inclusion (A.locallyTrivialCocycles₁_le_of_subset h)
  obtain ⟨x, rfl⟩ := B.mkQ_surjective z
  have hx : B'.mkQ (f x) = 0 := LinearMap.mem_ker.mp hz
  rw [Submodule.mem_bot]
  exact (Submodule.Quotient.mk_eq_zero B).mpr
    (show f x ∈ B' from (Submodule.Quotient.mk_eq_zero B').mp hx)

end Utilities.DiscreteGaloisModule
