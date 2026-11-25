module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.Abel

@[expose] public section

open groupCohomology

namespace Utilities

/-- A representation on a discrete coefficient module has locally constant orbits. -/
structure DiscreteGaloisModule (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] where
  rep : Rep.{0} k G
  discreteOrbit : ∀ a : rep, IsLocallyConstant fun σ : G => rep.ρ σ a

namespace DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]

def continuousCocycles₁ (A : DiscreteGaloisModule k G) : Submodule k (G → A.rep) where
  carrier := {f | f ∈ cocycles₁ A.rep ∧ IsLocallyConstant f}
  zero_mem' := ⟨(cocycles₁ A.rep).zero_mem, IsLocallyConstant.const 0⟩
  add_mem' hf hg := ⟨(cocycles₁ A.rep).add_mem hf.1 hg.1, hf.2.comp₂ hg.2 (· + ·)⟩
  smul_mem' n _ hf := ⟨(cocycles₁ A.rep).smul_mem n hf.1, hf.2.comp (n • ·)⟩

/-- Cocycles whose restriction to each specified subgroup is a coboundary. -/
def locallyTrivialCocycles₁ (A : DiscreteGaloisModule k G)
    (restrictionGroups : Set (Subgroup G)) : Submodule k (G → A.rep) where
  carrier := {f | f ∈ A.continuousCocycles₁ ∧ ∀ D ∈ restrictionGroups,
    ∃ a : A.rep, ∀ σ ∈ D, f σ = A.rep.ρ σ a - a}
  zero_mem' := ⟨A.continuousCocycles₁.zero_mem, fun _ _ => ⟨0, fun _ _ => by simp⟩⟩
  add_mem' := by
    intro f h hf hh
    refine ⟨A.continuousCocycles₁.add_mem hf.1 hh.1, fun D hD => ?_⟩
    obtain ⟨a, ha⟩ := hf.2 D hD
    obtain ⟨b, hb⟩ := hh.2 D hD
    refine ⟨a + b, fun σ hσ => ?_⟩
    change f σ + h σ = A.rep.ρ σ (a + b) - (a + b)
    rw [ha σ hσ, hb σ hσ, map_add]
    abel
  smul_mem' := by
    intro n f hf
    refine ⟨A.continuousCocycles₁.smul_mem n hf.1, fun D hD => ?_⟩
    obtain ⟨a, ha⟩ := hf.2 D hD
    refine ⟨n • a, fun σ hσ => ?_⟩
    change n • f σ = A.rep.ρ σ (n • a) - n • a
    rw [ha σ hσ, (A.rep.ρ σ).map_smul, smul_sub]

theorem coboundaries₁_le_locallyTrivial (A : DiscreteGaloisModule k G)
    (restrictionGroups : Set (Subgroup G)) :
    coboundaries₁ A.rep ≤ A.locallyTrivialCocycles₁ restrictionGroups := by
  intro f hf
  obtain ⟨a, rfl⟩ := hf
  refine ⟨⟨d₀₁_apply_mem_cocycles₁ (A := A.rep) a, ?_⟩, fun _ _ => ⟨a, fun _ _ => rfl⟩⟩
  exact (A.discreteOrbit a).comp (· - a)

/-- The kernel on continuous H¹, computed as locally trivial cocycles
modulo the global coboundaries. -/
abbrev selmerKernel (A : DiscreteGaloisModule k G) (restrictionGroups : Set (Subgroup G)) :=
  (A.locallyTrivialCocycles₁ restrictionGroups) ⧸
    (coboundaries₁ A.rep).comap (A.locallyTrivialCocycles₁ restrictionGroups).subtype

end DiscreteGaloisModule

end Utilities
