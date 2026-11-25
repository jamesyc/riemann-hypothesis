module

public import Utilities.SelmerCoefficientMap
public import Utilities.SelmerCohomologyRestriction
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.GroupWithZero.Action.Units

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
  (A : DiscreteGaloisModule k G)

/-- Multiply the coefficient action by a locally constant character. -/
def characterTwist (χ : G →* kˣ) (hχ : IsLocallyConstant χ) : DiscreteGaloisModule k G where
  rep := Rep.of
    { toFun := fun g => (χ g : k) • A.rep.ρ g
      map_one' := by rw [map_one, Units.val_one, one_smul, map_one]
      map_mul' g h := by
        apply LinearMap.ext
        intro a
        change (χ (g * h) : k) • A.rep.ρ (g * h) a =
          (χ g : k) • A.rep.ρ g ((χ h : k) • A.rep.ρ h a)
        rw [map_mul χ, Units.val_mul, mul_smul, map_mul A.rep.ρ, mul_apply_eq_comp, map_smul] }
  discreteOrbit a := hχ.comp₂ (A.discreteOrbit a) (fun u b => (u : k) • b)

@[simp]
theorem characterTwist_ρ_apply (χ : G →* kˣ) (hχ : IsLocallyConstant χ) (g : G) (a : A.rep) :
    (A.characterTwist χ hχ).rep.ρ g a = (χ g : k) • A.rep.ρ g a := rfl

variable (H : Subgroup G)

/-- A character trivial on the subgroup leaves its Selmer kernel unchanged.
The equivalence acts as the identity on the underlying cocycles. -/
def characterTwistRestrictionEquiv (χ : G →* kˣ) (hχ : IsLocallyConstant χ)
    (hH : ∀ h : H, χ h.val = 1) (D : Set (Subgroup H)) :
    ((A.characterTwist χ hχ).restrictToSubgroup H).selmerKernel D ≃ₗ[k]
      (A.restrictToSubgroup H).selmerKernel D := by
  refine selmerCoefficientEquiv D (LinearEquiv.refl k A.rep) ?_
  intro g a
  change (χ g.val : k) • A.rep.ρ g.val a = A.rep.ρ g.val a
  rw [hH, Units.val_one, one_smul]

variable [H.Normal] [IsTopologicalGroup G]

/-- The coefficient twist multiplies the conjugation action by the
character value under the natural equivalence on the subgroup. -/
theorem characterTwistRestrictionEquiv_conjugation (χ : G →* kˣ) (hχ : IsLocallyConstant χ)
    (hH : ∀ h : H, χ h.val = 1) (D : Set (Subgroup H)) (g : G)
    (hgroups : ∀ J ∈ D, J.map (normalSubgroupConjugateHom H g⁻¹) ∈ D)
    (x : ((A.characterTwist χ hχ).restrictToSubgroup H).selmerKernel D) :
    characterTwistRestrictionEquiv A H χ hχ hH D
        (normalSubgroupSelmerConjugation (A.characterTwist χ hχ) H D g hgroups x) =
      (χ g : k) • normalSubgroupSelmerConjugation A H D g hgroups
        (characterTwistRestrictionEquiv A H χ hχ hH D x) := by
  let T := (A.characterTwist χ hχ).restrictToSubgroup H
  let B := (coboundaries₁ T.rep).comap (T.locallyTrivialCocycles₁ D).subtype
  obtain ⟨f, rfl⟩ := B.mkQ_surjective x
  let U := A.restrictToSubgroup H
  let B' := (coboundaries₁ U.rep).comap (U.locallyTrivialCocycles₁ D).subtype
  let u : T.rep →ₗ[k] U.rep := LinearMap.id
  have hu (h : H) (a : T.rep) : u (T.rep.ρ h a) = U.rep.ρ h (u a) := by
    change (χ h.val : k) • A.rep.ρ h.val a = A.rep.ρ h.val a
    rw [hH, Units.val_one, one_smul]
  let L := mapLocallyTrivialCocycles₁ D u hu
  let f' := normalSubgroupConjugateCocycle (A.characterTwist χ hχ) H D g hgroups f
  have hc : normalSubgroupSelmerConjugation (A.characterTwist χ hχ) H D g hgroups (B.mkQ f) =
      B.mkQ f' := normalSubgroupSelmerConjugation_mk _ H D g hgroups f
  have he (z : T.locallyTrivialCocycles₁ D) :
      characterTwistRestrictionEquiv A H χ hχ hH D (B.mkQ z) = B'.mkQ (L z) := rfl
  have hc' : normalSubgroupSelmerConjugation A H D g hgroups (B'.mkQ (L f)) =
      B'.mkQ (normalSubgroupConjugateCocycle A H D g hgroups (L f)) :=
    normalSubgroupSelmerConjugation_mk A H D g hgroups (L f)
  rw [hc, he f', he f, hc', ← map_smul]
  congr 1
  apply Subtype.ext
  funext h
  let v : A.rep := f'.val h
  let w : A.rep := (normalSubgroupConjugateCocycle A H D g hgroups (L f)).val h
  let b : A.rep := f.val (normalSubgroupConjugate H g⁻¹ h)
  change v = (χ g : k) • w
  have hv : v = (χ g : k) • A.rep.ρ g b :=
    normalSubgroupConjugateCocycle_apply (A.characterTwist χ hχ) H D g hgroups f h
  have hw : w = A.rep.ρ g b := normalSubgroupConjugateCocycle_apply A H D g hgroups (L f) h
  rw [hv, hw]

/-- A character pulled back along an open quotient is locally constant. -/
theorem locallyConstant_quotientCharacter (hopen : IsOpen (H : Set G)) (ψ : (G ⧸ H) →* kˣ) :
    IsLocallyConstant (ψ.comp (QuotientGroup.mk' H)) := by
  let _ : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hopen
  exact (IsLocallyConstant.of_discrete ψ).comp_continuous
    (show Continuous (QuotientGroup.mk' H : G → G ⧸ H) from QuotientGroup.continuous_mk)

/-- At invertible index the Selmer kernel of the inverse-character twist
over the ambient group is the character eigenspace over the subgroup. -/
noncomputable def selmerRestrictionEquivCharacterEigenspace [Finite (G ⧸ H)]
    (hopen : IsOpen (H : Set G)) (hunit : IsUnit (Nat.card (G ⧸ H) : k))
    (D : Set (Subgroup G))
    (hgroups : ∀ (g : G) (J : Subgroup H), J ∈ subgroupSelmerFamily H D →
      J.map (normalSubgroupConjugateHom H g⁻¹) ∈ subgroupSelmerFamily H D)
    (ψ : (G ⧸ H) →* kˣ) :
    (A.characterTwist (ψ⁻¹.comp (QuotientGroup.mk' H))
        (locallyConstant_quotientCharacter H hopen ψ⁻¹)).selmerKernel D ≃ₗ[k]
      ↥(⨅ g : G, LinearMap.ker (normalSubgroupSelmerConjugation A H _ g (hgroups g) -
        (ψ (QuotientGroup.mk' H g) : k) • LinearMap.id)) := by
  let p : G →* G ⧸ H := QuotientGroup.mk' H
  let χ := ψ⁻¹.comp p
  let hχ := locallyConstant_quotientCharacter H hopen ψ⁻¹
  let T := A.characterTwist χ hχ
  let D' := subgroupSelmerFamily H D
  let X := (A.restrictToSubgroup H).selmerKernel D'
  let X' := (T.restrictToSubgroup H).selmerKernel D'
  have hχH (h : H) : χ h.val = 1 := by
    have hp : p h.val = 1 := (QuotientGroup.eq_one_iff h.val).mpr h.property
    change (ψ⁻¹ : (G ⧸ H) →* kˣ) (p h.val) = 1
    rw [hp, map_one]
  let E : X' ≃ₗ[k] X := characterTwistRestrictionEquiv A H χ hχ hχH D'
  let C (g : G) : Module.End k X := normalSubgroupSelmerConjugation A H D' g (hgroups g)
  let C' (g : G) : Module.End k X' := normalSubgroupSelmerConjugation T H D' g (hgroups g)
  let u (g : G) : kˣ := ψ (p g)
  let U : Submodule k X' := ⨅ g : G, LinearMap.ker (C' g - LinearMap.id)
  let V : Submodule k X := ⨅ g : G, LinearMap.ker (C g - (u g : k) • LinearMap.id)
  have hC (g : G) (x : X') : E (C' g x) = (↑(u g)⁻¹ : k) • C g (E x) :=
    characterTwistRestrictionEquiv_conjugation A H χ hχ hχH D' g (hgroups g) x
  have hfixed (g : G) (x : X') : C' g x = x ↔ C g (E x) = (u g : k) • E x := by
    constructor
    · intro hx
      have he : (↑(u g)⁻¹ : k) • C g (E x) = E x := (hC g x).symm.trans (congrArg E hx)
      calc
        C g (E x) = (u g : k) • ((↑(u g)⁻¹ : k) • C g (E x)) := by
          rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
        _ = _ := by rw [he]
    · intro hx
      apply E.injective
      rw [hC, hx, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hmem (x : X') : E x ∈ V ↔ x ∈ U := by
    simp only [V, U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    exact forall_congr' (fun g => (hfixed g x).symm)
  have he : U.map E.toLinearMap = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mpr hy
    · intro hx
      have hy : E (E.symm x) ∈ V := (E.apply_symm_apply x).symm ▸ hx
      exact ⟨E.symm x, (hmem _).mp hy, E.apply_symm_apply x⟩
  exact (selmerRestrictionEquivInvariants T H hopen hunit D hgroups).trans (E.ofSubmodules U V he)

end Utilities.DiscreteGaloisModule
