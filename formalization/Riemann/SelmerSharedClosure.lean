module

public import Riemann.SelmerBaseChangeAction
public import Riemann.SelmerRestrictionFamilies
public import Utilities.KrullRestrictionKernel
public import Utilities.SelmerGroupEquiv

@[expose] public section

open Utilities DiscreteGaloisModule
open scoped IsMulCommutative TensorProduct

namespace Riemann

variable (F : Type) [Field F] [NumberField F] [IsAbelianGalois ℚ F]
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S]

local notation "Ω" => AlgebraicClosure F
local notation "H" => MonoidHom.ker (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) F)
local notation "e" => restrictNormalKernelContinuousMulEquiv ℚ F Ω
local notation "A" => DiscreteGaloisModule.baseChange (padicTateTwist F ℓ i) S
local notation "T" => DiscreteGaloisModule.baseChange (padicTateTwistIn ℚ Ω ℓ i) S
local notation "B" => DiscreteGaloisModule.restrictToSubgroup T H
local notation "D" => numberFieldSelmerRestrictions F ℓ
local notation "D₀" => numberFieldSelmerRestrictionsIn ℚ Ω ℓ
local notation "D'" => DiscreteGaloisModule.subgroupSelmerFamily H D₀
local notation "V" => S ⊗[ℤ_[ℓ]] PadicTateQuotient ℓ
local notation "u" => LinearEquiv.refl S V

local instance : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω

omit [Fact ℓ.Prime] in
/-- The field-local family transported from the fixing subgroup agrees with
the original local family on the host Galois group. -/
theorem numberFieldSelmerSharedClosure_family :
    (fun J : Subgroup H => J.map ((ContinuousMulEquiv.toMulEquiv e).toMonoidHom)) '' D' = D := by
  have hcomp : (Subgroup.subtype H).comp (ContinuousMulEquiv.toMulEquiv (ContinuousMulEquiv.symm e)).toMonoidHom =
      (AlgEquiv.restrictScalarsHom ℚ : Gal(Ω/F) →* Gal(Ω/ℚ)) :=
    MonoidHom.ext (restrictNormalKernelContinuousMulEquiv_symm_coe ℚ F Ω)
  have h (J : Subgroup Gal(Ω/ℚ)) :
      (J.comap (Subgroup.subtype H)).map ((ContinuousMulEquiv.toMulEquiv e).toMonoidHom) =
        J.comap (AlgEquiv.restrictScalarsHom ℚ : Gal(Ω/F) →* Gal(Ω/ℚ)) := by
    let j := Subgroup.subtype H
    let e₀ := ContinuousMulEquiv.toMulEquiv e
    calc
      _ = (J.comap j).comap e₀.symm.toMonoidHom :=
        Subgroup.map_equiv_eq_comap_symm e₀ (J.comap j)
      _ = J.comap (j.comp e₀.symm.toMonoidHom) := Subgroup.comap_comap J j _
      _ = _ := congrArg (Subgroup.comap · J) hcomp
  rw [subgroupSelmerFamily, Set.image_image, numberFieldSelmerRestrictions_eq_restrictionsIn]
  calc
    _ = (fun J : Subgroup Gal(Ω/ℚ) => J.comap
        (AlgEquiv.restrictScalarsHom ℚ : Gal(Ω/F) →* Gal(Ω/ℚ))) '' D₀ :=
      congrArg (fun f => f '' D₀) (funext h)
    _ = _ := numberFieldSelmerRestrictionsIn_comap_restrictScalars ℚ F Ω ℓ

/-- On the fixing subgroup the host and ambient Tate coefficient actions
agree on the common coefficient module. -/
theorem numberFieldSelmerSharedClosure_coefficients (g : H) (x : (A).rep) :
    u ((A).rep.ρ (e g) x) = (B).rep.ρ g (u x) := by
  let a : V := x
  let gF : Field.absoluteGaloisGroup F := e g
  change (A).rep.ρ gF a = (T).rep.ρ g.val a
  have he : (e g).toRingEquiv = g.val.toRingEquiv :=
    RingEquiv.ext (restrictNormalKernelContinuousMulEquiv_apply ℚ F Ω g)
  have hscalar : padicTateScalar F ℓ i gF = padicTateScalarIn ℚ Ω ℓ i g.val :=
    congrArg (padicTateScalarOnAut Ω ℓ i) he
  have hρ : (padicTateTwist F ℓ i).rep.ρ gF = (padicTateTwistIn ℚ Ω ℓ i).rep.ρ g.val := by
    apply LinearMap.ext
    intro b
    change padicTateScalar F ℓ i gF • b = padicTateScalarIn ℚ Ω ℓ i g.val • b
    rw [hscalar]
  exact DFunLike.congr_fun (congrArg (LinearMap.baseChange S) hρ) a

/-- Identify the host Selmer kernel with the kernel on the fixing subgroup
of the common closure, with coefficients and local conditions both matched. -/
noncomputable def numberFieldSelmerSharedClosureEquiv :
    (A).selmerKernel D ≃ₗ[S] (B).selmerKernel D' :=
  selmerKernelGroupEquiv A B D D' e u
    (numberFieldSelmerSharedClosure_coefficients F ℓ i S)
    (numberFieldSelmerSharedClosure_family F ℓ)

/-- The shared-closure identification intertwines the lifted host action
and the ambient conjugation used in Selmer descent. -/
theorem numberFieldSelmerSharedClosureEquiv_ambientPullback (τ : Gal(Ω/ℚ)) (x : (A).selmerKernel D) :
    numberFieldSelmerSharedClosureEquiv F ℓ i S
        (numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ x) =
      normalSubgroupSelmerConjugation T H D' τ
        (numberFieldSelmerIntersection_stable ℚ F Ω ℓ τ)
        (numberFieldSelmerSharedClosureEquiv F ℓ i S x) := by
  let φ : Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup F :=
    relativeGaloisConj ℚ F Ω τ.symm
  let φ' := normalSubgroupConjugateHom H τ⁻¹
  let v₀ : Module.End ℤ_[ℓ] (padicTateTwist F ℓ i).rep :=
    padicTateScalarOnAut Ω ℓ i τ.toRingEquiv • LinearMap.id
  let v : Module.End S (A).rep := v₀.baseChange S
  let v' : Module.End S (B).rep := (T).rep.ρ τ
  have he (g : H) : φ (e g) = e (φ' g) := by
    apply AlgEquiv.ext
    intro a
    change relativeGaloisConj ℚ F Ω τ.symm (e g) a = e (φ' g) a
    rw [relativeGaloisConj_apply, restrictNormalKernelContinuousMulEquiv_apply,
      restrictNormalKernelContinuousMulEquiv_apply]
    rfl
  have hv (a : (A).rep) : u (v a) = v' (u a) := by
    let b : V := a
    change v₀.baseChange S b = (T).rep.ρ τ b
    have h : v₀ = (padicTateTwistIn ℚ Ω ℓ i).rep.ρ τ := by
      apply LinearMap.ext
      intro m
      rfl
    exact DFunLike.congr_fun (congrArg (LinearMap.baseChange S) h) b
  unfold numberFieldSelmerScalarExtendedAmbientPullback baseChangeSelmerPullback
  rw [normalSubgroupSelmerConjugation_eq_pullback]
  exact selmerKernelGroupEquiv_pullback A B D D' e u
    (numberFieldSelmerSharedClosure_coefficients F ℓ i S) (numberFieldSelmerSharedClosure_family F ℓ)
    φ φ' (relativeGaloisConj_continuous ℚ F Ω τ.symm) (continuous_normalSubgroupConjugateHom H _)
    v v'
    (baseChangeSelmerPullback_intertwines (padicTateTwist F ℓ i) S φ v₀
      (numberFieldSelmerAmbientCoefficient_intertwines F ℓ i τ))
    (normalSubgroupConjugation_intertwines T H τ)
    (numberFieldSelmerRestrictions_map_conj F ℓ τ.symm) (numberFieldSelmerIntersection_stable ℚ F Ω ℓ τ)
    he hv x

/-- The inverse host character twist of the extended Tate module on the
common closure over the rational numbers. -/
noncomputable def numberFieldSelmerSharedInverseTwist (ψ : Gal(F/ℚ) →* Sˣ) :
    DiscreteGaloisModule S Gal(Ω/ℚ) :=
  let ψq := ψ.comp (numberFieldSelmerGaloisQuotientEquiv ℚ F Ω).toMonoidHom
  (T).characterTwist (ψq⁻¹.comp (QuotientGroup.mk' H))
    (locallyConstant_quotientCharacter H (isOpen_numberFieldSelmerGaloisKernel ℚ F Ω) ψq⁻¹)

/-- The inverse host character and negative Tate power give the scalar on
the shared coefficient module. -/
theorem numberFieldSelmerSharedInverseTwist_ρ (ψ : Gal(F/ℚ) →* Sˣ) (g : Gal(Ω/ℚ)) :
    (numberFieldSelmerSharedInverseTwist F ℓ i S ψ).rep.ρ g =
      ((((ψ (g.restrictNormal F))⁻¹ : Sˣ) : S) *
        algebraMap ℤ_[ℓ] S (padicTateScalarIn ℚ Ω ℓ i g)) •
        (1 : Module.End S (numberFieldSelmerSharedInverseTwist F ℓ i S ψ).rep) := by
  let ψq := ψ.comp (numberFieldSelmerGaloisQuotientEquiv ℚ F Ω).toMonoidHom
  have hχ : ((ψq⁻¹.comp (QuotientGroup.mk' H)) g : S) =
      (((ψ (g.restrictNormal F))⁻¹ : Sˣ) : S) :=
    congrArg (fun σ : Gal(F/ℚ) => (((ψ σ)⁻¹ : Sˣ) : S))
      (numberFieldSelmerGaloisQuotientEquiv_mk ℚ F Ω g)
  let a := padicTateScalarIn ℚ Ω ℓ i g
  have hA : (padicTateTwistIn ℚ Ω ℓ i).rep.ρ g =
      a • (1 : Module.End ℤ_[ℓ] (PadicTateQuotient ℓ)) :=
    LinearMap.ext fun _ => rfl
  have hT : (T).rep.ρ g = (algebraMap ℤ_[ℓ] S a) • (1 : Module.End S V) := by
    change (Module.End.baseChangeHom ℤ_[ℓ] S (PadicTateQuotient ℓ))
      ((padicTateTwistIn ℚ Ω ℓ i).rep.ρ g) = _
    rw [hA, map_smul, map_one, IsScalarTower.algebraMap_smul]
  change ((ψq⁻¹.comp (QuotientGroup.mk' H)) g : S) • (T).rep.ρ g = _
  rw [hχ, hT]
  exact smul_smul ((((ψ (g.restrictNormal F))⁻¹ : Sˣ) : S))
    (algebraMap ℤ_[ℓ] S a) (1 : Module.End S V)

/-- The full host Tate character eigenspace is the Selmer kernel of the
inverse host twist on the common closure, when the host degree is invertible. -/
noncomputable def numberFieldSelmerExtendedCharacterSharedEquiv
    (hunit : IsUnit (Module.finrank ℚ F : S)) (ψ : Gal(F/ℚ) →* Sˣ) :
    numberFieldSelmerScalarExtendedCharacterEigenspace F ℓ i S ψ ≃ₗ[S]
      (numberFieldSelmerSharedInverseTwist F ℓ i S ψ).selmerKernel D₀ := by
  let E := numberFieldSelmerSharedClosureEquiv F ℓ i S
  let Y := numberFieldSelmerScalarExtendedCharacterEigenspace F ℓ i S ψ
  let Z : Submodule S ((B).selmerKernel D') :=
    ⨅ τ : Gal(Ω/ℚ), LinearMap.ker
      (normalSubgroupSelmerConjugation T H D' τ
        (numberFieldSelmerIntersection_stable ℚ F Ω ℓ τ) -
        (ψ (τ.restrictNormal F) : S) • LinearMap.id)
  have hmem (x : (A).selmerKernel D) : E x ∈ Z ↔ x ∈ Y := by
    simp only [Z, Y, numberFieldSelmerScalarExtendedCharacterEigenspace,
      Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    apply forall_congr'
    intro τ
    have he := numberFieldSelmerSharedClosureEquiv_ambientPullback F ℓ i S τ x
    change E (numberFieldSelmerScalarExtendedAmbientPullback F ℓ i S τ x) = _ at he
    rw [← he, ← map_smul E]
    exact E.injective.eq_iff
  have hmap : Y.map E.toLinearMap = Z := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).mpr hx
    · intro hz
      have hx : E (E.symm z) ∈ Z := (E.apply_symm_apply z).symm ▸ hz
      exact ⟨E.symm z, (hmem _).mp hx, E.apply_symm_apply z⟩
  exact (E.ofSubmodules Y Z hmap).trans
    (numberFieldSelmerCharacterDescent ℚ F Ω T ℓ hunit ψ).symm

/-- The per-character length on either sign part is bounded
by the length of the actual inverse-character Tate twist over the rational base. -/
theorem numberFieldSelmerSignCharacterLength_le_sharedTwist
    [Module.Free ℤ_[ℓ] S] [Module.Finite ℤ_[ℓ] S]
    (positive : Bool) (hdegree : ¬ ℓ ∣ Module.finrank ℚ F) (ψ : Gal(F/ℚ) →* Sˣ) :
    Module.length S (characterEigenspace (numberFieldSelmerSignBaseChangeAction F ℓ i S positive) ψ) ≤
      Module.length S ((numberFieldSelmerSharedInverseTwist F ℓ i S ψ).selmerKernel D₀) := by
  have hp : IsUnit (Module.finrank ℚ F : ℤ_[ℓ]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Fact.out : ℓ.Prime).coprime_iff_not_dvd.mpr hdegree))
  have hS : IsUnit (Module.finrank ℚ F : S) := by
    simpa only [map_natCast] using hp.map (algebraMap ℤ_[ℓ] S)
  exact (numberFieldSelmerSignCharacterLength_le F ℓ i S positive ψ).trans_eq
    (numberFieldSelmerExtendedCharacterSharedEquiv F ℓ i S hS ψ).length_eq

/-- The per-character length entering the minus Bernoulli bound is bounded
by the length of the actual inverse-character Tate twist over the rational base. -/
theorem numberFieldSelmerMinusCharacterLength_le_sharedTwist
    [Module.Free ℤ_[ℓ] S] [Module.Finite ℤ_[ℓ] S]
    (hdegree : ¬ ℓ ∣ Module.finrank ℚ F) (ψ : Gal(F/ℚ) →* Sˣ) :
    Module.length S (characterEigenspace (numberFieldSelmerMinusBaseChangeAction F ℓ i S) ψ) ≤
      Module.length S ((numberFieldSelmerSharedInverseTwist F ℓ i S ψ).selmerKernel D₀) :=
  numberFieldSelmerSignCharacterLength_le_sharedTwist F ℓ i S false hdegree ψ

end Riemann
