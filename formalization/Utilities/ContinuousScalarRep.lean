module

public import Mathlib.RepresentationTheory.Continuous.TopRep

@[expose] public section

namespace Utilities

/-- A scalar character acts by continuous linear maps on a topological module. -/
def continuousScalarRepresentation {R G V : Type*} [CommRing R] [Monoid G]
    [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [TopologicalSpace R] [ContinuousSMul R V] (χ : G →* R) :
    ContRepresentation R G V :=
  .ofMonoidHom
    { toFun := fun g => χ g • ContinuousLinearMap.id R V
      map_one' := by
        ext v
        simp
      map_mul' := fun g h => by
        ext v
        simpa [mul_smul] using smul_comm (χ g) (χ h) v }

@[simp]
theorem continuousScalarRepresentation_apply {R G V : Type*} [CommRing R] [Monoid G]
    [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [TopologicalSpace R] [ContinuousSMul R V] (χ : G →* R) (g : G) (v : V) :
    continuousScalarRepresentation χ g v = χ g • v := rfl

end Utilities
