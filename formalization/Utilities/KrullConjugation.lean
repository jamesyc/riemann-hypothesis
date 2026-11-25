module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Neighborhood

@[expose] public section

open Filter
open scoped Topology

namespace Utilities

/-- Mathlib's fixing-subgroup equivalence is a homeomorphism for the Krull
and subgroup topologies when the intermediate field is finite over the base. -/
def fixingSubgroupContinuousMulEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] : E.fixingSubgroup ≃ₜ* Gal(L/E) := by
  let e := E.fixingSubgroupEquiv
  refine { e with continuous_toFun := ?_, continuous_invFun := ?_ }
  · change Continuous e
    apply continuous_of_continuousAt_one e
    rw [ContinuousAt, map_one]
    intro S hS
    obtain ⟨D, hD, hDS⟩ := (krullTopology_mem_nhds_one_iff E L S).mp hS
    let T := D.restrictScalars K
    have : FiniteDimensional K T := FiniteDimensional.trans K E D
    have hT : {σ : E.fixingSubgroup | (σ : Gal(L/K)) ∈ T.fixingSubgroup} ∈ 𝓝 1 :=
      (T.fixingSubgroup_isOpen.preimage continuous_subtype_val).mem_nhds
        (T.fixingSubgroup.one_mem)
    change e ⁻¹' S ∈ 𝓝 (1 : E.fixingSubgroup)
    filter_upwards [hT] with σ hσ
    change e σ ∈ S
    apply hDS
    change (σ : Gal(L/K)) ∈ T.fixingSubgroup at hσ
    change e σ ∈ D.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    exact fun x hx => hσ x hx
  · apply continuous_induced_rng.mpr
    let f := E.fixingSubgroup.subtype.comp e.symm.toMonoidHom
    change Continuous f
    apply continuous_of_continuousAt_one f
    rw [ContinuousAt, map_one]
    intro S hS
    obtain ⟨D, hD, hDS⟩ := (krullTopology_mem_nhds_one_iff K L S).mp hS
    let T : IntermediateField E L := IntermediateField.extendScalars (show E ≤ E ⊔ D from le_sup_left)
    have : FiniteDimensional K T := by
      change FiniteDimensional K (T.restrictScalars K)
      rw [IntermediateField.extendScalars_restrictScalars]
      infer_instance
    have : FiniteDimensional E T := FiniteDimensional.right K E T
    apply (krullTopology_mem_nhds_one_iff E L _).mpr
    refine ⟨T, inferInstance, fun σ hσ => hDS ?_⟩
    change σ ∈ T.fixingSubgroup at hσ
    change f σ ∈ D.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hDsup : D ≤ E ⊔ D := le_sup_right
    exact hσ x (hDsup hx)

@[simp]
theorem fixingSubgroupContinuousMulEquiv_apply {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] (σ : E.fixingSubgroup) (x : L) :
    fixingSubgroupContinuousMulEquiv E σ x = (σ : Gal(L/K)) x := rfl

/-- Equal subgroups carry the same topology and the same group structure. -/
def subgroupContinuousMulEquivOfEq {G : Type*} [Group G] [TopologicalSpace G]
    {S T : Subgroup G} (h : S = T) : S ≃ₜ* T where
  toMulEquiv := MulEquiv.subgroupCongr h
  continuous_toFun := continuous_induced_rng.mpr continuous_subtype_val
  continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val

@[simp]
theorem subgroupContinuousMulEquivOfEq_apply_coe {G : Type*} [Group G] [TopologicalSpace G]
    {S T : Subgroup G} (h : S = T) (σ : S) :
    (subgroupContinuousMulEquivOfEq h σ : G) = σ := rfl

variable (K F L : Type*) [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [Normal K F]

/-- An ambient automorphism conjugates the subgroup fixing a normal
intermediate field. -/
def relativeGaloisConj (τ : Gal(L/K)) : Gal(L/F) →* Gal(L/F) where
  toFun σ :=
    { __ := (τ * σ.restrictScalars K * τ⁻¹).toRingEquiv
      commutes' := fun x => by
        change τ (σ (τ.symm (algebraMap F L x))) = algebraMap F L x
        rw [← AlgEquiv.restrictNormal_commutes τ.symm F, σ.commutes,
          AlgEquiv.restrictNormal_commutes τ.symm F, AlgEquiv.apply_symm_apply] }
  map_one' := by
    apply AlgEquiv.restrictScalars_injective K
    change τ * (1 : Gal(L/K)) * τ⁻¹ = 1
    simp
  map_mul' σ σ' := by
    apply AlgEquiv.restrictScalars_injective K
    change τ * (σ * σ').restrictScalarsHom K * τ⁻¹ =
      (τ * σ.restrictScalarsHom K * τ⁻¹) * (τ * σ'.restrictScalarsHom K * τ⁻¹)
    rw [map_mul]
    group

theorem relativeGaloisConj_apply (τ : Gal(L/K)) (σ : Gal(L/F)) (x : L) :
    relativeGaloisConj K F L τ σ x = τ (σ (τ.symm x)) := rfl

@[simp]
theorem relativeGaloisConj_one (σ : Gal(L/F)) :
    relativeGaloisConj K F L 1 σ = σ := by
  ext x
  rfl

theorem relativeGaloisConj_mul (s t : Gal(L/K)) (σ : Gal(L/F)) :
    relativeGaloisConj K F L (s * t) σ =
      relativeGaloisConj K F L s (relativeGaloisConj K F L t σ) := by
  ext x
  rfl

theorem relativeGaloisConj_restrictScalars (s : Gal(L/K)) (σ : Gal(L/F)) :
    (relativeGaloisConj K F L s σ).restrictScalars K = s * σ.restrictScalars K * s⁻¹ := by
  ext x
  rfl

theorem relativeGaloisConj_restrictScalars_of_tower {E : Type*} [Field E]
    [Algebra K E] [Algebra F E] [Algebra E L] [IsScalarTower K E L]
    [IsScalarTower F E L] [Normal K E] (s : Gal(L/K)) (σ : Gal(L/E)) :
    (relativeGaloisConj K E L s σ).restrictScalars F =
      relativeGaloisConj K F L s (σ.restrictScalars F) := by
  ext x
  rfl

/-- Restriction to a normal intermediate extension commutes with relative
conjugation. -/
theorem relativeGaloisConj_restrictNormal {E : Type*} [Field E] [Algebra K E]
    [Algebra F E] [Algebra E L] [IsScalarTower K F E] [IsScalarTower K E L]
    [IsScalarTower F E L] [Normal K E] [Normal F E]
    (s : Gal(L/K)) (σ : Gal(L/F)) :
    (relativeGaloisConj K F L s σ).restrictNormal E =
      relativeGaloisConj K F E (s.restrictNormal E) (σ.restrictNormal E) := by
  ext x
  apply (algebraMap E L).injective
  rw [AlgEquiv.restrictNormal_commutes, relativeGaloisConj_apply, relativeGaloisConj_apply]
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes]
  have h : (s.restrictNormal E).symm = s.symm.restrictNormal E :=
    (map_inv (AlgEquiv.restrictNormalHom E) s).symm
  rw [h, AlgEquiv.restrictNormal_commutes]

/-- Relative conjugation by the inverse ambient automorphism is inverse
to the original conjugation. -/
theorem relativeGaloisConj_leftInverse (τ : Gal(L/K)) :
    Function.LeftInverse (relativeGaloisConj K F L τ.symm) (relativeGaloisConj K F L τ) := by
  intro σ
  apply AlgEquiv.ext
  intro x
  simp only [relativeGaloisConj_apply, AlgEquiv.symm_symm, AlgEquiv.symm_apply_apply]

theorem relativeGaloisConj_bijective (τ : Gal(L/K)) :
    Function.Bijective (relativeGaloisConj K F L τ) := by
  have hr : Function.LeftInverse (relativeGaloisConj K F L τ)
      (relativeGaloisConj K F L τ.symm) := by
    simpa only [AlgEquiv.symm_symm] using relativeGaloisConj_leftInverse K F L τ.symm
  exact ⟨(relativeGaloisConj_leftInverse K F L τ).injective, hr.surjective⟩

/-- The relative conjugation map is continuous for the Krull topology. -/
theorem relativeGaloisConj_continuous [FiniteDimensional K F] (τ : Gal(L/K)) :
    Continuous (relativeGaloisConj K F L τ) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro S hS
  obtain ⟨D, hD, hDS⟩ := (krullTopology_mem_nhds_one_iff F L S).mp hS
  let D' := (D.restrictScalars K).map τ.symm.toAlgHom
  let E' : IntermediateField F L := D'.toSubfield.toIntermediateField fun x => by
    refine ⟨algebraMap F L (τ.restrictNormal F x), D.algebraMap_mem _, ?_⟩
    change τ.symm (algebraMap F L (τ.restrictNormal F x)) = algebraMap F L x
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.symm_apply_apply]
  have hDF : FiniteDimensional K (D.restrictScalars K) := FiniteDimensional.trans K F D
  have hD' : FiniteDimensional K D' :=
    FiniteDimensional.of_injective
      (IntermediateField.equivMap (D.restrictScalars K) τ.symm.toAlgHom).symm.toLinearMap
      (IntermediateField.equivMap (D.restrictScalars K) τ.symm.toAlgHom).symm.injective
  have hE'K : FiniteDimensional K E' := hD'
  have hE' : FiniteDimensional F E' := FiniteDimensional.right K F E'
  apply (krullTopology_mem_nhds_one_iff F L _).mpr
  refine ⟨E', hE', fun σ hσ => hDS ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  have hmem : τ.symm x ∈ E' := ⟨x, hx, rfl⟩
  rw [relativeGaloisConj_apply, hσ _ hmem, AlgEquiv.apply_symm_apply]

end Utilities
