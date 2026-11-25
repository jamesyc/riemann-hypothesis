module

public import Riemann.SelmerCohomology
public import Utilities.SelmerCharacterTwist
public import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open NumberField Utilities
open scoped NumberField Pointwise

namespace Riemann

/-- The Selmer local family on a shared closure, indexed by the nonzero
prime of the closure. This form does not require a separate finite-place witness. -/
def numberFieldSelmerRestrictionsIn (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω]
    (ℓ : ℕ) : Set (Subgroup Gal(Ω/F)) :=
  { J | ∃ P : Ideal (𝓞 Ω), P.IsPrime ∧ P ≠ ⊥ ∧
    (J = P.inertia Gal(Ω/F) ∨ (ℓ : 𝓞 Ω) ∈ P ∧ J = MulAction.stabilizer Gal(Ω/F) P) }

theorem numberFieldSelmerRestrictions_eq_restrictionsIn (F : Type) [Field F] [NumberField F] (ℓ : ℕ) :
    numberFieldSelmerRestrictions F ℓ = numberFieldSelmerRestrictionsIn F (AlgebraicClosure F) ℓ := by
  let Ω := AlgebraicClosure F
  ext J
  constructor
  · rintro ⟨v, P, hP, hv, hJ⟩
    let _ : P.IsPrime := hP
    let _ : P.LiesOver v.maximalIdeal.asIdeal := ⟨hv.symm⟩
    refine ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.maximalIdeal.ne_bot P, ?_⟩
    rcases hJ with hI | ⟨hℓ, hD⟩
    · exact Or.inl hI
    · refine Or.inr ⟨?_, hD⟩
      rw [← hv] at hℓ
      change algebraMap (𝓞 F) (𝓞 Ω) (ℓ : 𝓞 F) ∈ P at hℓ
      rwa [map_natCast] at hℓ
  · rintro ⟨P, hP, hPne, hJ⟩
    let _ : P.IsPrime := hP
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
      ⟨P.under (𝓞 F), inferInstance, Ideal.under_ne_bot _ hPne⟩
    let v := NumberField.FinitePlace.mk w
    have hv : P.comap (RingOfIntegers.mapRingHom (algebraMap F Ω)) = v.maximalIdeal.asIdeal := by
      rw [NumberField.FinitePlace.maximalIdeal_mk]
      rfl
    refine ⟨v, P, hP, hv, ?_⟩
    rcases hJ with hI | ⟨hℓ, hD⟩
    · exact Or.inl hI
    · refine Or.inr ⟨?_, hD⟩
      rw [← hv]
      change algebraMap (𝓞 F) (𝓞 Ω) (ℓ : 𝓞 F) ∈ P
      rwa [map_natCast]

/-- Passing from the ambient Galois group to a subgroup fixing an intermediate
base field gives the local family for that field in the same closure. -/
theorem numberFieldSelmerRestrictionsIn_comap_restrictScalars (F E Ω : Type)
    [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
    [IsScalarTower F E Ω] (ℓ : ℕ) :
    (fun J : Subgroup Gal(Ω/F) => J.comap
      (AlgEquiv.restrictScalarsHom F : Gal(Ω/E) →* Gal(Ω/F))) ''
      numberFieldSelmerRestrictionsIn F Ω ℓ = numberFieldSelmerRestrictionsIn E Ω ℓ := by
  let r : Gal(Ω/E) →* Gal(Ω/F) := AlgEquiv.restrictScalarsHom F
  have hI (P : Ideal (𝓞 Ω)) : (P.inertia Gal(Ω/F)).comap r = P.inertia Gal(Ω/E) := by
    ext s
    rw [Subgroup.mem_comap, Ideal.mem_inertia, Ideal.mem_inertia]
    rfl
  have hD (P : Ideal (𝓞 Ω)) :
      (MulAction.stabilizer Gal(Ω/F) P).comap r = MulAction.stabilizer Gal(Ω/E) P := by
    ext s
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    rfl
  ext J
  constructor
  · rintro ⟨K, ⟨P, hP, hne, hK⟩, rfl⟩
    refine ⟨P, hP, hne, ?_⟩
    rcases hK with h | ⟨hℓ, h⟩
    · exact Or.inl (h ▸ hI P)
    · exact Or.inr ⟨hℓ, h ▸ hD P⟩
  · rintro ⟨P, hP, hne, hJ⟩
    rcases hJ with h | ⟨hℓ, h⟩
    · exact ⟨P.inertia Gal(Ω/F), ⟨P, hP, hne, Or.inl rfl⟩, (hI P).trans h.symm⟩
    · exact ⟨MulAction.stabilizer Gal(Ω/F) P, ⟨P, hP, hne, Or.inr ⟨hℓ, rfl⟩⟩,
        (hD P).trans h.symm⟩

/-- Ambient conjugation permutes the local conditions on the shared closure. -/
theorem numberFieldSelmerRestrictionsIn_stable (F Ω : Type)
    [Field F] [Field Ω] [Algebra F Ω] (ℓ : ℕ) (g : Gal(Ω/F))
    {J : Subgroup Gal(Ω/F)} (hJ : J ∈ numberFieldSelmerRestrictionsIn F Ω ℓ) :
    J.map (MulAut.conj g).toMonoidHom ∈ numberFieldSelmerRestrictionsIn F Ω ℓ := by
  obtain ⟨P, hP, hne, hJ⟩ := hJ
  have hprime : (g • P : Ideal (𝓞 Ω)).IsPrime := (Ideal.IsPrime.smul_iff g).2 hP
  have hne' : (g • P : Ideal (𝓞 Ω)) ≠ ⊥ := by
    intro h
    apply hne
    simpa only [inv_smul_smul, smul_bot] using congrArg (fun Q : Ideal (𝓞 Ω) => g⁻¹ • Q) h
  refine ⟨g • P, hprime, hne', ?_⟩
  rcases hJ with rfl | ⟨hℓ, rfl⟩
  · exact Or.inl (Ideal.inertia_smul g P).symm
  · refine Or.inr ⟨?_, (MulAction.stabilizer_smul_eq_stabilizer_map_conj g P).symm⟩
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulSemiringAction.toRingAut Gal(Ω/F) (𝓞 Ω) g⁻¹) (ℓ : 𝓞 Ω) ∈ P
    rwa [map_natCast]

section Quotient

variable (F E Ω : Type) [Field F] [Field E] [Field Ω]
  [Algebra F E] [Algebra E Ω] [Algebra F Ω] [IsScalarTower F E Ω]
  [IsGalois F E] [Normal F Ω] [FiniteDimensional F E]

local notation "r" => (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
local notation "H" => MonoidHom.ker (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
local notation "Q" => Gal(Ω/F) ⧸ H

/-- The quotient of the ambient Galois group by the host fixing group. -/
noncomputable def numberFieldSelmerGaloisQuotientEquiv : Q ≃* Gal(E/F) :=
  QuotientGroup.quotientKerEquivOfSurjective r (AlgEquiv.restrictNormalHom_surjective Ω)

omit [Normal F Ω] in
theorem isOpen_numberFieldSelmerGaloisKernel : IsOpen (H : Set Gal(Ω/F)) := by
  rw [AlgEquiv.ker_restrictNormalHom]
  let j := IsScalarTower.toAlgHom F E Ω
  let _ : FiniteDimensional F j.fieldRange := j.equivFieldRange.toLinearEquiv.finiteDimensional
  exact j.fieldRange.fixingSubgroup_isOpen

theorem numberFieldSelmerGaloisQuotient_card : Nat.card Q = Module.finrank F E :=
  (Nat.card_congr (numberFieldSelmerGaloisQuotientEquiv F E Ω).toEquiv).trans
    (IsGalois.card_aut_eq_finrank F E)

theorem isUnit_numberFieldSelmerGaloisQuotient_card (ℓ : ℕ) [Fact ℓ.Prime]
    (hdegree : ¬ ℓ ∣ Module.finrank F E) : IsUnit (Nat.card Q : ℤ_[ℓ]) := by
  rw [numberFieldSelmerGaloisQuotient_card F E Ω]
  exact PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
    ((Fact.out : ℓ.Prime).coprime_iff_not_dvd.mpr hdegree))

omit [FiniteDimensional F E] in
theorem numberFieldSelmerGaloisQuotientEquiv_mk (g : Gal(Ω/F)) :
    numberFieldSelmerGaloisQuotientEquiv F E Ω (QuotientGroup.mk' H g) = r g := by
  unfold numberFieldSelmerGaloisQuotientEquiv
  rfl

omit [Normal F Ω] [FiniteDimensional F E] in
/-- The intersections with the host fixing subgroup are stable under ambient
conjugation of the shared-closure local conditions. -/
theorem numberFieldSelmerIntersection_stable (ℓ : ℕ) (g : Gal(Ω/F))
    (J : Subgroup H) (hJ : J ∈ DiscreteGaloisModule.subgroupSelmerFamily H
      (numberFieldSelmerRestrictionsIn F Ω ℓ)) :
    J.map (DiscreteGaloisModule.normalSubgroupConjugateHom H g⁻¹) ∈
      DiscreteGaloisModule.subgroupSelmerFamily H (numberFieldSelmerRestrictionsIn F Ω ℓ) :=
  DiscreteGaloisModule.subgroupSelmerFamily_stable_under_conjugation H _
    (fun a _ hK => numberFieldSelmerRestrictionsIn_stable F Ω ℓ a hK) g⁻¹ hJ

/-- For an invertible host degree, the field-level character descends the
corresponding Selmer eigenspace to a twist of the ambient representation. -/
noncomputable def numberFieldSelmerCharacterDescent {k : Type} [CommRing k]
    (A : DiscreteGaloisModule k Gal(Ω/F)) (ℓ : ℕ)
    (hunit : IsUnit (Module.finrank F E : k)) (ψ : Gal(E/F) →* kˣ) :
    let D := numberFieldSelmerRestrictionsIn F Ω ℓ
    let ψq := ψ.comp (numberFieldSelmerGaloisQuotientEquiv F E Ω).toMonoidHom
    let hχ := DiscreteGaloisModule.locallyConstant_quotientCharacter H
      (isOpen_numberFieldSelmerGaloisKernel F E Ω) ψq⁻¹
    (A.characterTwist (ψq⁻¹.comp (QuotientGroup.mk' H)) hχ).selmerKernel D ≃ₗ[k]
      ↥(⨅ g : Gal(Ω/F), LinearMap.ker
        (DiscreteGaloisModule.normalSubgroupSelmerConjugation A H _ g
          (numberFieldSelmerIntersection_stable F E Ω ℓ g) -
          (ψ (r g) : k) • LinearMap.id)) := by
  let e := numberFieldSelmerGaloisQuotientEquiv F E Ω
  let _ : Finite Q := Finite.of_injective e e.injective
  have hindex : IsUnit (Nat.card Q : k) := by rwa [numberFieldSelmerGaloisQuotient_card F E Ω]
  let c (g : Gal(Ω/F)) := DiscreteGaloisModule.normalSubgroupSelmerConjugation A H _ g
    (numberFieldSelmerIntersection_stable F E Ω ℓ g)
  have hres (g : Gal(Ω/F)) : e (QuotientGroup.mk' H g) = r g :=
    numberFieldSelmerGaloisQuotientEquiv_mk F E Ω g
  have heq : (⨅ g : Gal(Ω/F), LinearMap.ker
      (c g - (ψ (e (QuotientGroup.mk' H g)) : k) • LinearMap.id)) =
      ⨅ g : Gal(Ω/F), LinearMap.ker (c g - (ψ (r g) : k) • LinearMap.id) := by
    apply iInf_congr
    intro g
    exact congrArg (fun w : Gal(E/F) => LinearMap.ker
      (c g - (ψ w : k) • LinearMap.id)) (hres g)
  let τ := DiscreteGaloisModule.selmerRestrictionEquivCharacterEigenspace A H
    (isOpen_numberFieldSelmerGaloisKernel F E Ω) hindex (numberFieldSelmerRestrictionsIn F Ω ℓ)
    (numberFieldSelmerIntersection_stable F E Ω ℓ) (ψ.comp e.toMonoidHom)
  exact τ.trans (LinearEquiv.ofEq _ _ heq)

end Quotient

end Riemann
