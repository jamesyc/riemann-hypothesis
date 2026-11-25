module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open scoped NumberField Pointwise
open NumberField

namespace Utilities

section Tower

variable {K E L : Type*} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [Normal K E]

/-- Restriction of an automorphism commutes with the embedding on rings of
integers. -/
theorem algebraMap_ringOfIntegers_restrictNormal_smul (σ : Gal(L/K)) (x : 𝓞 E) :
    algebraMap (𝓞 E) (𝓞 L) (σ.restrictNormal E • x) = σ • algebraMap (𝓞 E) (𝓞 L) x := by
  apply RingOfIntegers.ext
  exact σ.restrictNormal_commutes E (x : E)

/-- Restriction sends inertia into inertia even if the upper field is infinite. -/
theorem numberField_inertia_map_restrictNormal_le (P : Ideal (𝓞 L)) :
    (P.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom E) ≤
      (P.under (𝓞 E)).inertia Gal(E/K) := by
  rintro _ ⟨σ, hσ, rfl⟩
  apply Ideal.mem_inertia.mpr
  intro x
  change algebraMap (𝓞 E) (𝓞 L) ((σ.restrictNormal E) • x - x) ∈ P
  rw [map_sub, algebraMap_ringOfIntegers_restrictNormal_smul]
  exact (Ideal.mem_inertia.mp hσ) (algebraMap (𝓞 E) (𝓞 L) x)

/-- Inertia in a finite Galois extension maps onto inertia of a normal
intermediate field. This form uses a tower of fields and their actual ring
of integers maps. -/
theorem numberField_inertia_map_restrictNormal_tower
    [NumberField E] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (Q : Ideal (𝓞 E)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver Q] :
    (P.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom E) = Q.inertia Gal(E/K) := by
  let f : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  let j := IsScalarTower.toAlgHom K E L
  let H := j.fieldRange.fixingSubgroup
  let _ : Algebra.IsInvariant (𝓞 E) (𝓞 L) H := by
    constructor
    intro z hz
    have hfix : (z : L) ∈ IntermediateField.fixedField H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      exact congrArg (fun x : 𝓞 L => (x : L)) (hz ⟨σ, hσ⟩)
    change (z : L) ∈ IntermediateField.fixedField j.fieldRange.fixingSubgroup at hfix
    rw [IsGalois.fixedField_fixingSubgroup] at hfix
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hfix
    have hy' : algebraMap E L y = (z : L) := hy
    have hyInt : IsIntegral ℤ y := (isIntegral_algebraMap_iff (B := L)).mp
      (hy' ▸ RingOfIntegers.isIntegral_coe z)
    exact ⟨⟨y, hyInt⟩, RingOfIntegers.ext hy'⟩
  apply Ideal.map_inertia_of_surjective f H Q P
  · exact AlgEquiv.restrictNormalHom_surjective L
  · change j.fieldRange.fixingSubgroup ≤ (AlgEquiv.restrictNormalHom E).ker
    rw [AlgEquiv.ker_restrictNormalHom]
  · exact algebraMap_ringOfIntegers_restrictNormal_smul

end Tower

/-- The Krull action on an individual algebraic integer is locally constant. -/
theorem isLocallyConstant_galois_smul_integer {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] (x : 𝓞 L) :
    IsLocallyConstant fun σ : Gal(L/K) => σ • x := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro σ
  let H := MulAction.stabilizer Gal(L/K) (x : L)
  have hH : IsOpen (H : Set Gal(L/K)) := stabilizer_isOpen_of_isIntegral (x : L)
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' H, hH.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change σ⁻¹ * σ ∈ H
    rw [inv_mul_cancel]
    exact H.one_mem
  · intro τ hτ
    have hfix : (σ⁻¹ * τ) • (x : L) = (x : L) := hτ
    apply RingOfIntegers.ext
    change τ (x : L) = σ (x : L)
    calc
      _ = σ • ((σ⁻¹ * τ) • (x : L)) := by rw [← mul_smul, mul_inv_cancel_left]; rfl
      _ = _ := by rw [hfix]; rfl

/-- Every finite inertia element lifts to inertia in an algebraic Galois
extension. Compactness combines lifts satisfying finitely many congruences. -/
theorem numberField_inertia_map_restrictNormal_of_isGalois
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) (P : Ideal (𝓞 L)) [P.IsPrime] :
    (P.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom E.toIntermediateField) =
      (P.under (𝓞 E.toIntermediateField)).inertia Gal(E.toIntermediateField/K) := by
  classical
  let A := E.toIntermediateField
  let _ : NumberField A := NumberField.of_module_finite K A
  let Q := P.under (𝓞 A)
  apply le_antisymm (numberField_inertia_map_restrictNormal_le P)
  intro τ hτ
  let C : Set Gal(L/K) := {σ | σ.restrictNormal A = τ}
  let D (s : Finset (𝓞 L)) : Set Gal(L/K) :=
    C ∩ ⋂ x ∈ (s : Set (𝓞 L)), {σ | σ • x - x ∈ P}
  have hC : IsClosed C :=
    (isClosed_singleton (x := τ)).preimage (InfiniteGalois.restrictNormalHom_continuous A)
  have hclosed (s : Finset (𝓞 L)) : IsClosed (D s) := by
    refine hC.inter (isClosed_biInter fun x _ => ?_)
    apply isOpen_compl_iff.mp
    exact isLocallyConstant_galois_smul_integer (K := K) x {y | y - x ∉ P}
  have hdir : Directed (· ⊇ ·) D := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · exact Set.inter_subset_inter_right _ (Set.biInter_subset_biInter_left Finset.subset_union_left)
    · exact Set.inter_subset_inter_right _ (Set.biInter_subset_biInter_left Finset.subset_union_right)
  have hnonempty (s : Finset (𝓞 L)) : (D s).Nonempty := by
    let t : Set L := (fun x : 𝓞 L => (x : L)) '' (s : Set (𝓞 L))
    let _ : Finite t := ((s.finite_toSet).image _).to_subtype
    let T := E ⊔ FiniteGaloisIntermediateField.adjoin K t
    let B := T.toIntermediateField
    let _ : NumberField B := NumberField.of_module_finite K B
    have hAB : A ≤ B := show E ≤ T from le_sup_left
    let _ : Algebra A B := (IntermediateField.inclusion hAB).toRingHom.toAlgebra
    let _ : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
    let R := P.under (𝓞 B)
    let _ : R.IsPrime := inferInstanceAs (P.under (𝓞 B)).IsPrime
    let _ : R.LiesOver Q := ⟨(Ideal.under_under P).symm⟩
    have hmap := numberField_inertia_map_restrictNormal_tower (K := K) Q R
    obtain ⟨ρ, hρ, hρA⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hτ)
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective L ρ
    have hσA : σ.restrictNormal A = τ := by
      change AlgEquiv.restrictNormalHom A σ = τ
      rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply A B, hσ]
      exact hρA
    refine ⟨σ, hσA, ?_⟩
    apply Set.mem_iInter.mpr
    intro x
    apply Set.mem_iInter.mpr
    intro hx
    have hxB : (x : L) ∈ B := by
      have hxt : (x : L) ∈ t := Set.mem_image_of_mem _ hx
      exact (show (FiniteGaloisIntermediateField.adjoin K t).toIntermediateField ≤ B from le_sup_right)
        (FiniteGaloisIntermediateField.subset_adjoin K t hxt)
    let y : B := ⟨x, hxB⟩
    have hy : IsIntegral ℤ y := (isIntegral_algebraMap_iff (B := L)).mp x.isIntegral_coe
    let z : 𝓞 B := ⟨y, hy⟩
    have hz : algebraMap (𝓞 B) (𝓞 L) z = x := RingOfIntegers.ext rfl
    have hh := (Ideal.mem_inertia.mp hρ) z
    change algebraMap (𝓞 B) (𝓞 L) (ρ • z - z) ∈ P at hh
    rw [map_sub, ← hσ] at hh
    change algebraMap (𝓞 B) (𝓞 L) (σ.restrictNormal B • z) - algebraMap (𝓞 B) (𝓞 L) z ∈ P at hh
    rw [algebraMap_ringOfIntegers_restrictNormal_smul, hz] at hh
    exact hh
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed D hdir
    hnonempty (fun s => (hclosed s).isCompact) hclosed
  have hσall := Set.mem_iInter.mp hσ
  refine Subgroup.mem_map.mpr ⟨σ, Ideal.mem_inertia.mpr ?_, (hσall ∅).1⟩
  intro x
  exact Set.mem_iInter.mp (Set.mem_iInter.mp (hσall {x}).2 x) (by simp)

/-- The Galois group of an algebraic extension acts transitively on prime
ideals above the same prime of the base number field. -/
theorem exists_galois_smul_prime_eq_of_under_eq
    {K L : Type*} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    (P Q : Ideal (𝓞 L)) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under (𝓞 K) = Q.under (𝓞 K)) :
    ∃ σ : Gal(L/K), σ • P = Q := by
  classical
  let D (s : Finset (𝓞 L)) : Set Gal(L/K) :=
    ⋂ x ∈ (s : Set (𝓞 L)), {σ | σ • x ∈ Q ↔ x ∈ P}
  have hclosed (s : Finset (𝓞 L)) : IsClosed (D s) := by
    refine isClosed_biInter fun x _ => isOpen_compl_iff.mp ?_
    exact isLocallyConstant_galois_smul_integer (K := K) x {y | ¬ (y ∈ Q ↔ x ∈ P)}
  have hdir : Directed (· ⊇ ·) D := fun s t =>
    ⟨s ∪ t, Set.biInter_subset_biInter_left Finset.subset_union_left,
      Set.biInter_subset_biInter_left Finset.subset_union_right⟩
  have hnonempty (s : Finset (𝓞 L)) : (D s).Nonempty := by
    let t : Set L := (fun x : 𝓞 L => (x : L)) '' (s : Set (𝓞 L))
    let _ : Finite t := (s.finite_toSet.image _).to_subtype
    let E := (FiniteGaloisIntermediateField.adjoin K t).toIntermediateField
    let _ : NumberField E := NumberField.of_module_finite K E
    let p := P.under (𝓞 K)
    let PE := P.under (𝓞 E)
    let QE := Q.under (𝓞 E)
    let _ : PE.IsPrime := inferInstanceAs (P.under (𝓞 E)).IsPrime
    let _ : QE.IsPrime := inferInstanceAs (Q.under (𝓞 E)).IsPrime
    let _ : PE.LiesOver p := ⟨(Ideal.under_under P).symm⟩
    let _ : QE.LiesOver p := ⟨hPQ.trans (Ideal.under_under Q).symm⟩
    obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p PE QE Gal(E/K)
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective L τ
    refine ⟨σ, Set.mem_iInter.mpr fun x => Set.mem_iInter.mpr fun hx => ?_⟩
    have hxE : (x : L) ∈ E :=
      FiniteGaloisIntermediateField.subset_adjoin K t (Set.mem_image_of_mem _ hx)
    let y : E := ⟨x, hxE⟩
    let z : 𝓞 E := ⟨y, (isIntegral_algebraMap_iff (B := L)).mp x.isIntegral_coe⟩
    have hz : algebraMap (𝓞 E) (𝓞 L) z = x := RingOfIntegers.ext rfl
    change σ • x ∈ Q ↔ x ∈ P
    rw [← hz, ← algebraMap_ringOfIntegers_restrictNormal_smul]
    change (AlgEquiv.restrictNormalHom E σ) • z ∈ QE ↔ z ∈ PE
    rw [hσ]
    rw [← hτ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed D hdir
    hnonempty (fun s => (hclosed s).isCompact) hclosed
  refine ⟨σ, Ideal.ext fun x => ?_⟩
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hx := Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hσ {σ⁻¹ • x})
    (σ⁻¹ • x)) (by simp)
  change σ • (σ⁻¹ • x) ∈ Q ↔ σ⁻¹ • x ∈ P at hx
  rw [smul_inv_smul] at hx
  exact hx.symm

/-- Contraction of a prime commutes with restriction of the automorphism. -/
theorem under_galois_smul_eq_restrictNormal_smul
    {K E L : Type*} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [Normal K E]
    (σ : Gal(L/K)) (P : Ideal (𝓞 L)) :
    (σ • P : Ideal (𝓞 L)).under (𝓞 E) = σ.restrictNormal E • P.under (𝓞 E) := by
  ext x
  change algebraMap (𝓞 E) (𝓞 L) x ∈ σ • P ↔ x ∈ σ.restrictNormal E • P.under (𝓞 E)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have h := algebraMap_ringOfIntegers_restrictNormal_smul (E := E) σ⁻¹ x
  change algebraMap (𝓞 E) (𝓞 L) ((AlgEquiv.restrictNormalHom E) σ⁻¹ • x) =
    σ⁻¹ • algebraMap (𝓞 E) (𝓞 L) x at h
  rw [map_inv] at h
  change σ⁻¹ • algebraMap (𝓞 E) (𝓞 L) x ∈ P ↔
    algebraMap (𝓞 E) (𝓞 L) (((AlgEquiv.restrictNormalHom E) σ)⁻¹ • x) ∈ P
  rw [h]

/-- The absolute decomposition subgroup maps onto the decomposition subgroup
of a finite Galois intermediate field. -/
theorem numberField_stabilizer_map_restrictNormal_of_isGalois
    {K L : Type*} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) (P : Ideal (𝓞 L)) [P.IsPrime] :
    (MulAction.stabilizer Gal(L/K) P).map (AlgEquiv.restrictNormalHom E) =
      MulAction.stabilizer Gal(E/K) (P.under (𝓞 E)) := by
  let f : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    change σ.restrictNormal E • P.under (𝓞 E) = _
    rw [← under_galois_smul_eq_restrictNormal_smul, MulAction.mem_stabilizer_iff.mp hσ]
  · intro τ hτ
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective L τ
    let Q := σ • P
    have hQP : Q.under (𝓞 E) = P.under (𝓞 E) := by
      change (σ • P : Ideal (𝓞 L)).under (𝓞 E) = _
      rw [under_galois_smul_eq_restrictNormal_smul]
      change f σ • P.under (𝓞 E) = _
      rw [show f σ = τ from hσ]
      exact MulAction.mem_stabilizer_iff.mp hτ
    let _ : NumberField E := NumberField.of_module_finite K E
    let _ : Q.IsPrime := inferInstanceAs (σ • P : Ideal (𝓞 L)).IsPrime
    obtain ⟨η, hη⟩ := exists_galois_smul_prime_eq_of_under_eq Q P hQP
    let γ : Gal(L/K) := η.restrictScalars K
    have hγ : f γ = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap E L).injective
      change algebraMap E L (γ.restrictNormal E x) = algebraMap E L x
      rw [γ.restrictNormal_commutes]
      exact η.commutes x
    refine ⟨γ * σ, MulAction.mem_stabilizer_iff.mpr ?_, ?_⟩
    · rw [mul_smul]
      exact hη
    · change f (γ * σ) = τ
      rw [map_mul, hγ, one_mul]
      exact hσ

end Utilities
