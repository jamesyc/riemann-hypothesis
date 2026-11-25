module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Neighborhood

@[expose] public section

open Filter
open scoped Topology

namespace Utilities

variable (K F L : Type*) [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [Normal K F]

local notation "p" => AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F
local notation "H" => MonoidHom.ker p

/-- An automorphism in the kernel of restriction to a normal field acts
as an automorphism over that field. -/
def restrictNormalKernelMulEquiv : H ≃* Gal(L/F) := by
  let f (σ : H) : Gal(L/F) :=
    { __ := σ.val.toRingEquiv
      commutes' := fun x => by
        have hσ : σ.val.restrictNormal F = 1 := σ.property
        change σ.val (algebraMap F L x) = _
        rw [← σ.val.restrictNormal_commutes F, hσ]
        rfl }
  let j (σ : Gal(L/F)) : H := ⟨σ.restrictScalars K, by
    apply MonoidHom.mem_ker.mpr
    apply AlgEquiv.ext
    intro x
    apply (algebraMap F L).injective
    change algebraMap F L ((σ.restrictScalars K).restrictNormal F x) = algebraMap F L x
    rw [AlgEquiv.restrictNormal_commutes]
    exact σ.commutes x⟩
  exact
    { toFun := f
      invFun := j
      left_inv := fun σ => Subtype.ext (AlgEquiv.ext fun x => rfl)
      right_inv := fun σ => AlgEquiv.ext fun x => rfl
      map_mul' := fun σ τ => AlgEquiv.ext fun x => rfl }

@[simp]
theorem restrictNormalKernelMulEquiv_apply (σ : H) (x : L) :
    restrictNormalKernelMulEquiv K F L σ x = (σ : Gal(L/K)) x := by
  rfl

@[simp]
theorem restrictNormalKernelMulEquiv_symm_coe (σ : Gal(L/F)) :
    ((restrictNormalKernelMulEquiv K F L).symm σ : Gal(L/K)) = σ.restrictScalars K := by
  rfl

/-- The Galois group over a finite normal field is homeomorphic to its
fixing subgroup, with the subgroup Krull topology. -/
def restrictNormalKernelContinuousMulEquiv [FiniteDimensional K F] : H ≃ₜ* Gal(L/F) := by
  let e := restrictNormalKernelMulEquiv K F L
  refine { e with continuous_toFun := ?_, continuous_invFun := ?_ }
  · change Continuous e
    apply continuous_of_continuousAt_one e
    rw [ContinuousAt, map_one]
    intro S hS
    obtain ⟨D, hf, hDS⟩ := (krullTopology_mem_nhds_one_iff F L S).mp hS
    let _ : FiniteDimensional F D := hf
    let T := D.restrictScalars K
    let _ : FiniteDimensional K T := FiniteDimensional.trans K F D
    have hT : {σ : H | (σ : Gal(L/K)) ∈ T.fixingSubgroup} ∈ 𝓝 1 :=
      (T.fixingSubgroup_isOpen.preimage continuous_subtype_val).mem_nhds T.fixingSubgroup.one_mem
    change e ⁻¹' S ∈ 𝓝 (1 : H)
    filter_upwards [hT] with σ hσ
    apply hDS
    change e σ ∈ D.fixingSubgroup
    change (σ : Gal(L/K)) ∈ T.fixingSubgroup at hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    exact fun x hx => hσ x hx
  · apply continuous_induced_rng.mpr
    let f : Gal(L/F) →* Gal(L/K) := AlgEquiv.restrictScalarsHom K
    change Continuous f
    apply continuous_of_continuousAt_one f
    rw [ContinuousAt, map_one]
    intro S hS
    obtain ⟨T, hf, hTS⟩ := (krullTopology_mem_nhds_one_iff K L S).mp hS
    let _ : FiniteDimensional K T := hf
    let j := IsScalarTower.toAlgHom K F L
    let _ : FiniteDimensional K j.fieldRange := j.equivFieldRange.toLinearEquiv.finiteDimensional
    let R := j.fieldRange ⊔ T
    let D : IntermediateField F L := R.toSubfield.toIntermediateField fun x =>
      (show j.fieldRange ≤ R from le_sup_left) (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    have hR : D.restrictScalars K = R := rfl
    let _ : FiniteDimensional K (D.restrictScalars K) := hR.symm ▸ inferInstanceAs (FiniteDimensional K R)
    let _ : FiniteDimensional K D := inferInstanceAs (FiniteDimensional K (D.restrictScalars K))
    let _ : FiniteDimensional F D := FiniteDimensional.right K F D
    apply (krullTopology_mem_nhds_one_iff F L _).mpr
    refine ⟨D, inferInstance, fun σ hσ => hTS ?_⟩
    change f σ ∈ T.fixingSubgroup
    change σ ∈ D.fixingSubgroup at hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hxR : x ∈ R := (show T ≤ R from le_sup_right) hx
    exact hσ x hxR

@[simp]
theorem restrictNormalKernelContinuousMulEquiv_apply [FiniteDimensional K F] (σ : H) (x : L) :
    restrictNormalKernelContinuousMulEquiv K F L σ x = (σ : Gal(L/K)) x := by
  rfl

@[simp]
theorem restrictNormalKernelContinuousMulEquiv_symm_coe [FiniteDimensional K F] (σ : Gal(L/F)) :
    ((restrictNormalKernelContinuousMulEquiv K F L).symm σ : Gal(L/K)) = σ.restrictScalars K := by
  rfl

end Utilities
