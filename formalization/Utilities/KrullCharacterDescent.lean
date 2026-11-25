module

public import Utilities.KrullConjugation
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Group.Pi.Hom
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

open scoped Topology

namespace Utilities

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- A locally constant character on the fixing subgroup of a finite
intermediate field descends to the finite abelian extension fixed by its kernel. -/
theorem exists_finiteAbelian_descendant_of_locallyConstant_fixingSubgroup
    (E : IntermediateField K L) [FiniteDimensional K E]
    {M : Type*} [AddCommGroup M] (ψ : Additive E.fixingSubgroup →+ M)
    (hψ : IsLocallyConstant (fun σ : E.fixingSubgroup => ψ (Additive.ofMul σ))) :
    ∃ T : FiniteGaloisIntermediateField E L, IsAbelianGalois E T ∧
      ∃ φ : Additive Gal(T/E) →+ M, Function.Injective φ ∧
        ∀ σ : Gal(L/E), φ (Additive.ofMul (σ.restrictNormal T)) =
          ψ (Additive.ofMul (E.fixingSubgroupEquiv.symm σ)) := by
  let U : Set E.fixingSubgroup := {σ | ψ (Additive.ofMul σ) = 0}
  let V : Set Gal(L/K) := Subtype.val '' U
  have hV : IsOpen V := E.fixingSubgroup_isOpen.isOpenMap_subtype_val _ (hψ {0})
  have h1 : (1 : Gal(L/K)) ∈ V := ⟨1, map_zero ψ, rfl⟩
  obtain ⟨S, hfin, hS⟩ := (krullTopology_mem_nhds_one_iff K L V).mp (hV.mem_nhds h1)
  have hsub : S.fixingSubgroup ≤ E.fixingSubgroup := by
    intro g hg
    obtain ⟨s, _, rfl⟩ := hS hg
    exact s.property
  have hES : E ≤ S := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup S,
      IntermediateField.le_fixedField_iff_le_fixingSubgroup]
    exact hsub
  let B := IntermediateField.extendScalars hES
  let _ : FiniteDimensional K B := hfin
  let _ : FiniteDimensional E B := FiniteDimensional.right K E B
  let χ : Gal(L/E) →* Multiplicative M :=
    AddMonoidHom.toMultiplicativeRight (ψ.comp E.fixingSubgroupEquiv.symm.toMonoidHom.toAdditive)
  have hBker : B.fixingSubgroup ≤ χ.ker := by
    intro σ hσ
    have hfix : (E.fixingSubgroupEquiv.symm σ).val ∈ S.fixingSubgroup := by
      apply (IntermediateField.mem_fixingSubgroup_iff S _).mpr
      intro x hx
      exact (IntermediateField.mem_fixingSubgroup_iff B σ).mp hσ _ hx
    obtain ⟨g, hg, he⟩ := hS hfix
    have he' : g = E.fixingSubgroupEquiv.symm σ := Subtype.ext he
    change ψ (Additive.ofMul (E.fixingSubgroupEquiv.symm σ)) = 0
    change ψ (Additive.ofMul g) = 0 at hg
    rwa [he'] at hg
  have hopen : IsOpen (χ.ker : Set Gal(L/E)) := Subgroup.isOpen_mono hBker B.fixingSubgroup_isOpen
  let N : ClosedSubgroup Gal(L/E) := ⟨χ.ker, (⟨χ.ker, hopen⟩ : OpenSubgroup Gal(L/E)).isClosed⟩
  let C := IntermediateField.fixedField χ.ker
  have hC : C.fixingSubgroup = χ.ker := InfiniteGalois.fixingSubgroup_fixedField N
  let _ : FiniteDimensional E C :=
    (InfiniteGalois.isOpen_iff_finite C).mp (hC.symm ▸ hopen)
  let _ : IsGalois E C :=
    (InfiniteGalois.normal_iff_isGalois C).mp (hC.symm ▸ inferInstanceAs χ.ker.Normal)
  let T : FiniteGaloisIntermediateField E L := ⟨C⟩
  let f : Gal(L/E) →* Gal(T/E) := AlgEquiv.restrictNormalHom T
  have hker : f.ker = χ.ker := C.restrictNormalHom_ker.trans hC
  have hf : Function.Surjective f := AlgEquiv.restrictNormalHom_surjective L
  let χT := f.liftOfSurjective hf ⟨χ, hker.le⟩
  have hχT (σ : Gal(L/E)) : χT (f σ) = χ σ :=
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf) (Function.rightInverse_surjInv hf) _ _
  have hχTinj : Function.Injective χT := by
    intro a b hab
    obtain ⟨σ, rfl⟩ := hf a
    obtain ⟨τ, rfl⟩ := hf b
    have hστ : σ * τ⁻¹ ∈ χ.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
      simpa only [hχT] using hab
    have he := MonoidHom.mem_ker.mp (hker.symm ▸ hστ)
    rwa [map_mul, map_inv, mul_inv_eq_one] at he
  have habelian : IsAbelianGalois E T :=
    { is_comm.comm := fun a b => hχTinj (by rw [map_mul, map_mul, mul_comm]) }
  let φ := AddMonoidHom.toMultiplicativeRight.symm χT
  exact ⟨T, habelian, φ, fun _ _ h => hχTinj (congrArg Multiplicative.ofAdd h),
    fun σ => congrArg Multiplicative.toAdd (hχT σ)⟩

/-- The character and all its conjugates by automorphisms over the base. -/
def relativeGaloisConjugateCharacters (E : IntermediateField K L) [Normal K E]
    {M : Type*} [AddCommGroup M] (ψ : Additive Gal(L/E) →+ M) :
    Additive Gal(L/E) →+ (Gal(L/K) → M) :=
  AddMonoidHom.pi fun s => ψ.comp (relativeGaloisConj K E L s).toAdditive

omit [IsGalois K L] in
@[simp]
theorem relativeGaloisConjugateCharacters_apply (E : IntermediateField K L) [Normal K E]
    {M : Type*} [AddCommGroup M] (ψ : Additive Gal(L/E) →+ M) (σ : Gal(L/E)) (s : Gal(L/K)) :
    relativeGaloisConjugateCharacters E ψ (Additive.ofMul σ) s =
      ψ (Additive.ofMul (relativeGaloisConj K E L s σ)) := rfl

/-- All ambient conjugates of a locally constant character descend together
to a finite abelian extension that is Galois over the original base. -/
theorem exists_finiteAbelian_normal_descendant_of_locallyConstant
    (E : IntermediateField K L) [FiniteDimensional K E] [IsGalois K E]
    {M : Type*} [AddCommGroup M] (ψ : Additive Gal(L/E) →+ M)
    (hψ : IsLocallyConstant (fun σ : Gal(L/E) => ψ (Additive.ofMul σ))) :
    ∃ T : FiniteGaloisIntermediateField E L, IsGalois K T ∧ IsAbelianGalois E T ∧
      ∃ φ : Additive Gal(T/E) →+ (Gal(L/K) → M), Function.Injective φ ∧
        ∀ (σ : Gal(L/E)) (s : Gal(L/K)), φ (Additive.ofMul (σ.restrictNormal T)) s =
          ψ (Additive.ofMul (relativeGaloisConj K E L s σ)) := by
  let H := E.fixingSubgroup
  let e := E.fixingSubgroupEquiv
  let Ψ := (relativeGaloisConjugateCharacters E ψ).comp e.toMonoidHom.toAdditive
  let V : Set Gal(L/K) := Subtype.val '' {σ : H | ψ (Additive.ofMul (e σ)) = 0}
  have hV : IsOpen V := E.fixingSubgroup_isOpen.isOpenMap_subtype_val _
    ((hψ.comp_continuous (fixingSubgroupContinuousMulEquiv E).continuous_toFun).isOpen_fiber 0)
  have h1 : (1 : Gal(L/K)) ∈ V := ⟨1, by simp [e], rfl⟩
  have hVzero (σ : Gal(L/E)) : σ.restrictScalars K ∈ V ↔ ψ (Additive.ofMul σ) = 0 := by
    constructor
    · rintro ⟨τ, hτ, he⟩
      have he' : τ = e.symm σ := Subtype.ext he
      change ψ (Additive.ofMul (e τ)) = 0 at hτ
      simpa [he'] using hτ
    · intro hz
      exact ⟨e.symm σ, by simpa using hz, rfl⟩
  obtain ⟨B, hBfin, hBnorm, hBV⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K L V).mp (hV.mem_nhds h1)
  let _ : FiniteDimensional K B := hBfin
  let _ : IsGalois K B := (isGalois_iff).mpr ⟨Algebra.isSeparable_tower_bot_of_isSeparable K B L, hBnorm⟩
  have hΨ : IsLocallyConstant (fun σ : H => Ψ (Additive.ofMul σ)) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro τ
    let U : Set H := (fun ν : H => (τ : Gal(L/K))⁻¹ * (ν : Gal(L/K))) ⁻¹' B.fixingSubgroup
    refine ⟨U, B.fixingSubgroup_isOpen.preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
    · change (τ : Gal(L/K))⁻¹ * (τ : Gal(L/K)) ∈ B.fixingSubgroup
      rw [inv_mul_cancel]
      exact B.fixingSubgroup.one_mem
    · intro ν hν
      have hzero : Ψ (Additive.ofMul (τ⁻¹ * ν)) = 0 := by
        funext s
        apply (hVzero _).mp
        rw [relativeGaloisConj_restrictScalars]
        exact hBV ((inferInstance : B.fixingSubgroup.Normal).conj_mem _ hν s)
      calc
        Ψ (Additive.ofMul ν) = Ψ (Additive.ofMul (τ * (τ⁻¹ * ν))) := by rw [mul_inv_cancel_left]
        _ = Ψ (Additive.ofMul τ) := by
          change Ψ (Additive.ofMul τ + Additive.ofMul (τ⁻¹ * ν)) = _
          rw [map_add, hzero, add_zero]
  obtain ⟨T, hAb, φ, hφinj, hφ⟩ := exists_finiteAbelian_descendant_of_locallyConstant_fixingSubgroup E Ψ hΨ
  have heval (σ : Gal(L/E)) (s : Gal(L/K)) :
      φ (Additive.ofMul (σ.restrictNormal T)) s =
        ψ (Additive.ofMul (relativeGaloisConj K E L s σ)) := by
    have he : e (E.fixingSubgroupEquiv.symm σ) = σ := e.apply_symm_apply σ
    exact (congrFun (hφ σ) s).trans
      (congrArg (fun ρ => ψ (Additive.ofMul (relativeGaloisConj K E L s ρ))) he)
  let C := T.toIntermediateField.restrictScalars K
  have hfix (σ : Gal(L/E)) : σ.restrictScalars K ∈ C.fixingSubgroup ↔
      ∀ s : Gal(L/K), ψ (Additive.ofMul (relativeGaloisConj K E L s σ)) = 0 := by
    have hker : σ.restrictScalars K ∈ C.fixingSubgroup ↔ σ.restrictNormal T = 1 := by
      change σ.restrictScalars K ∈ C.fixingSubgroup ↔ σ ∈ (AlgEquiv.restrictNormalHom T).ker
      rw [show (AlgEquiv.restrictNormalHom T).ker = T.toIntermediateField.fixingSubgroup from
        T.toIntermediateField.restrictNormalHom_ker]
      rfl
    rw [hker]
    constructor
    · intro he s
      rw [← heval, he]
      exact congrFun (map_zero φ) s
    · intro hz
      have he : φ (Additive.ofMul (σ.restrictNormal T)) = 0 := by
        funext s
        exact (heval σ s).trans (hz s)
      exact congrArg Additive.toMul (hφinj (he.trans (map_zero φ).symm))
  have hEC : E ≤ C := fun _ hx => T.toIntermediateField.algebraMap_mem ⟨_, hx⟩
  have hCnorm : C.fixingSubgroup.Normal := by
    constructor
    intro σ hσ s
    let σE := e ⟨σ, E.fixingSubgroup_antitone hEC hσ⟩
    have hσE := (hfix σE).mp hσ
    rw [← show σE.restrictScalars K = σ from rfl, ← relativeGaloisConj_restrictScalars]
    apply (hfix _).mpr
    intro t
    rw [← relativeGaloisConj_mul]
    exact hσE (t * s)
  exact ⟨T, (InfiniteGalois.normal_iff_isGalois C).mp hCnorm, hAb, φ, hφinj, heval⟩

end Utilities
