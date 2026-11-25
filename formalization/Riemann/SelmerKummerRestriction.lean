module

public import Riemann.SelmerKummerRank
public import Utilities.AbsoluteCyclotomicInertia
public import Utilities.KrullConjugation
public import Utilities.PadicTateTorsion
public import Utilities.SelmerResidualRestriction
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Utilities.KummerRadical
public import Utilities.KummerClassGroup
public import Utilities.KummerValuation
import Utilities.PadicTateFiniteRestriction

@[expose] public section

open Utilities
open scoped NumberField

namespace Riemann

variable (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Ω" => AlgebraicClosure F
local notation "Galg" => (Ω ≃ₐ[F] Ω)
local notation "G" => Field.absoluteGaloisGroup F

noncomputable def numberFieldResidualCyclotomicMap : G →* (ZMod (ℓ ^ (1 : ℕ)))ˣ := by
  change Galg →* (ZMod (ℓ ^ (1 : ℕ)))ˣ
  exact (modularCyclotomicCharacter Ω
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (ℓ ^ (1 : ℕ)))).comp
      (MulSemiringAction.toRingAut Galg Ω)

noncomputable abbrev numberFieldResidualCyclotomicKernel : Subgroup G :=
  (numberFieldResidualCyclotomicMap F ℓ).ker

local notation "H" => numberFieldResidualCyclotomicKernel F ℓ

theorem numberFieldResidualCyclotomicKernel_eq_fixingSubgroup
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ) :
    H = ((IntermediateField.adjoin F ({ζ} : Set Ω)).fixingSubgroup : Subgroup G) := by
  let m := ℓ ^ (1 : ℕ)
  let A := IntermediateField.adjoin F ({ζ} : Set Ω)
  have hζ' : IsPrimitiveRoot ζ m := by simpa only [m, pow_one] using hζ
  let _ : Fact (1 < m) := ⟨by simpa only [m, pow_one] using (Fact.out : ℓ.Prime).one_lt⟩
  let ncard := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω m
  apply Subgroup.ext
  intro g
  let σ : Galg := g
  change modularCyclotomicCharacter Ω ncard σ.toRingEquiv = 1 ↔ σ ∈ A.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg
    let t : rootsOfUnity m Ω := hζ'.toRootsOfUnity
    have hfix := modularCyclotomicCharacter.spec Ω ncard σ.toRingEquiv t.property
    rw [hg, Units.val_one, ZMod.val_one, pow_one] at hfix
    have hfixζ : σ ζ = ζ := hfix
    have heq : σ.toAlgHom.comp A.val = A.val := by
      apply IntermediateField.adjoin_algHom_ext F
      intro x hx
      obtain rfl : x = ζ := Set.mem_singleton_iff.mp hx
      exact hfixζ
    exact fun x hx => DFunLike.congr_fun heq ⟨x, hx⟩
  · intro hg
    have hfixζ : σ ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
    apply Units.ext
    symm
    apply modularCyclotomicCharacter.unique
    intro t ht
    obtain ⟨j, _, hj⟩ := hζ'.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' _ _).mp ht)
    rw [Units.val_one, ZMod.val_one, pow_one, ← hj, map_pow]
    exact congrArg (· ^ j) hfixζ

/-- The residual cyclotomic kernel has the Krull topology of the Galois
group over the field obtained by adjoining the chosen root of unity. -/
noncomputable def numberFieldResidualCyclotomicKernelEquiv
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ) :
    H ≃ₜ* (Ω ≃ₐ[IntermediateField.adjoin F ({ζ} : Set Ω)] Ω) := by
  let E := IntermediateField.adjoin F ({ζ} : Set Ω)
  let _ : FiniteDimensional F E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  let S : Subgroup Galg := H
  have hS : S = E.fixingSubgroup := numberFieldResidualCyclotomicKernel_eq_fixingSubgroup F ℓ ζ hζ
  change S ≃ₜ* (Ω ≃ₐ[E] Ω)
  let e : S ≃ₜ* E.fixingSubgroup := subgroupContinuousMulEquivOfEq hS
  exact e.trans (fixingSubgroupContinuousMulEquiv E)

@[simp]
theorem numberFieldResidualCyclotomicKernelEquiv_apply
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ) (σ : H) (x : Ω) :
    numberFieldResidualCyclotomicKernelEquiv F ℓ ζ hζ σ x = (show Galg from σ.val) x := rfl

theorem numberFieldResidualCyclotomicKernel_index_dvd :
    Subgroup.index H ∣ ℓ - 1 := by
  have hcard : Nat.card (ZMod (ℓ ^ (1 : ℕ)))ˣ = ℓ - 1 := by
    rw [pow_one, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ℓ.Prime)]
  rw [← hcard, Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card _

theorem numberFieldResidualCyclotomicKernel_index_isUnit :
    IsUnit (Subgroup.index H : ℤ_[ℓ]) := by
  let _ : Subgroup.FiniteIndex H := Subgroup.finiteIndex_ker _
  have hℓ : ℓ.Prime := Fact.out
  have hidxpos : 0 < Subgroup.index H := Nat.pos_of_ne_zero Subgroup.index_ne_zero
  have hidxle : Subgroup.index H ≤ ℓ - 1 :=
    Nat.le_of_dvd (by have := hℓ.two_le; omega) (numberFieldResidualCyclotomicKernel_index_dvd F ℓ)
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff, hℓ.coprime_iff_not_dvd]
  exact Nat.not_dvd_of_pos_of_lt hidxpos (by omega)

theorem padicTateTwist_ρ_apply_eq_self_on_firstTorsion (i : ℕ) {g : G} (hg : g ∈ H)
    (x : (padicTateTwist F ℓ i).rep) (hx : (ℓ : ℤ_[ℓ]) • x = 0) :
    (padicTateTwist F ℓ i).rep.ρ g x = x := by
  let γ : Galg := g
  have hu : g ∈ (padicCyclotomicReduction F ℓ 1).ker := by
    change padicCyclotomicReduction F ℓ 1 g = 1
    apply Units.ext
    change (cyclotomicCharacter Ω ℓ γ.toRingEquiv).val.toZModPow 1 = 1
    rw [cyclotomicCharacter.toZModPow]
    exact congrArg (fun z : (ZMod (ℓ ^ (1 : ℕ)))ˣ => z.val) hg
  exact padicTateTwist_ρ_apply_eq_self_on_powTorsion F ℓ i 1 hu x (by simpa only [pow_one] using hx)

/-- Unramified local conditions on the kernel of the residual cyclotomic
character, expressed in the same algebraic closure as the original host. -/
noncomputable def numberFieldResidualInertiaAway : Set (Subgroup H) :=
  {D | ∃ P : Ideal (𝓞 Ω), P.IsPrime ∧ (ℓ : 𝓞 Ω) ∉ P ∧
    P.comap (NumberField.RingOfIntegers.mapRingHom (algebraMap F Ω)) ≠ ⊥ ∧
    D = (P.inertia Galg : Subgroup G).comap (Subgroup.subtype H)}

/-- Inertia at all nonzero primes away from ℓ in the common algebraic
closure, for an intermediate base field. -/
noncomputable def numberFieldInertiaAwayInClosure (E : IntermediateField F Ω) :
    Set (Subgroup (Ω ≃ₐ[E] Ω)) :=
  {D | ∃ P : Ideal (𝓞 Ω), P.IsPrime ∧ (ℓ : 𝓞 Ω) ∉ P ∧ P ≠ ⊥ ∧ D = P.inertia _}

omit [NumberField F] [Fact ℓ.Prime] in
/-- The prime-ideal presentation of the local subgroups imposes the
conditions at every prolongation of every finite place away from ℓ. -/
theorem mem_numberFieldInertiaAwayInClosure_iff (E : IntermediateField F Ω) [NumberField E]
    (D : Subgroup (Ω ≃ₐ[E] Ω)) :
    D ∈ numberFieldInertiaAwayInClosure F ℓ E ↔
      ∃ (v : NumberField.FinitePlace E) (P : Ideal (𝓞 Ω)),
        (ℓ : 𝓞 E) ∉ v.maximalIdeal.asIdeal ∧ P.IsPrime ∧
          P.under (𝓞 E) = v.maximalIdeal.asIdeal ∧ D = P.inertia _ := by
  constructor
  · rintro ⟨P, hP, hp, hnonzero, rfl⟩
    let Q := P.under (𝓞 E)
    let v := NumberField.FinitePlace.mk
      (⟨Q, hP.comap _, Ideal.under_ne_bot (𝓞 E) hnonzero⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    have hv : v.maximalIdeal.asIdeal = Q := by simp [v, NumberField.FinitePlace.maximalIdeal_mk]
    refine ⟨v, P, ?_, hP, hv.symm, rfl⟩
    rw [hv]
    intro h
    change (algebraMap (𝓞 E) (𝓞 Ω)) (ℓ : 𝓞 E) ∈ P at h
    exact hp (by simpa only [map_natCast] using h)
  · rintro ⟨v, P, hv, hP, hPv, rfl⟩
    refine ⟨P, hP, ?_, ?_, rfl⟩
    · intro h
      apply hv
      rw [← hPv]
      change (algebraMap (𝓞 E) (𝓞 Ω)) (ℓ : 𝓞 E) ∈ P
      rwa [map_natCast]
    · intro h
      rw [h, Ideal.under, Ideal.comap_bot_of_injective _
        (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 Ω))] at hPv
      exact v.maximalIdeal.ne_bot hPv.symm

private theorem map_residualInertia_eq (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ)
    (P : Ideal (𝓞 Ω)) :
    ((P.inertia Galg : Subgroup G).comap (Subgroup.subtype H)).map
      (numberFieldResidualCyclotomicKernelEquiv F ℓ ζ hζ).toMonoidHom =
        P.inertia (Ω ≃ₐ[IntermediateField.adjoin F ({ζ} : Set Ω)] Ω) := by
  let e := numberFieldResidualCyclotomicKernelEquiv F ℓ ζ hζ
  have hmem (σ : H) : (show Galg from σ.val) ∈ P.inertia Galg ↔ e σ ∈ P.inertia _ := by
    rw [Ideal.mem_inertia, Ideal.mem_inertia]
    have hs (x : 𝓞 Ω) : e σ • x = (show Galg from σ.val) • x := by
      apply NumberField.RingOfIntegers.ext
      exact numberFieldResidualCyclotomicKernelEquiv_apply F ℓ ζ hζ σ (x : Ω)
    simp only [hs]
  ext τ
  obtain ⟨σ, rfl⟩ := e.surjective τ
  constructor
  · rintro ⟨σ', hσ', hh⟩
    have heq : σ' = σ := e.injective hh
    subst σ'
    exact (hmem σ).mp hσ'
  · intro hσ
    exact Subgroup.mem_map.mpr ⟨σ, (hmem σ).mpr hσ, rfl⟩

/-- In the common algebraic closure the residual restriction groups become
exactly the inertia groups away from ℓ over the cyclotomic extension. -/
theorem image_numberFieldResidualInertiaAway (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ) :
    (fun D => D.map (numberFieldResidualCyclotomicKernelEquiv F ℓ ζ hζ).toMonoidHom) ''
      numberFieldResidualInertiaAway F ℓ =
        numberFieldInertiaAwayInClosure F ℓ (IntermediateField.adjoin F ({ζ} : Set Ω)) := by
  have hnonzero (P : Ideal (𝓞 Ω)) : P.under (𝓞 F) ≠ ⊥ ↔ P ≠ ⊥ := by
    constructor
    · intro h heq
      exact h (heq ▸ Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 Ω)))
    · exact Ideal.under_ne_bot (𝓞 F)
  ext D
  constructor
  · rintro ⟨I, ⟨P, hP, hℓ, hF, rfl⟩, rfl⟩
    exact ⟨P, hP, hℓ, (hnonzero P).mp hF, map_residualInertia_eq F ℓ ζ hζ P⟩
  · rintro ⟨P, hP, hℓ, hne, rfl⟩
    exact ⟨_, ⟨P, hP, hℓ, (hnonzero P).mpr hne, rfl⟩, map_residualInertia_eq F ℓ ζ hζ P⟩

/-- The unramified characters counted in the relaxed Selmer estimate
are the unramified characters over the field containing the chosen root. -/
noncomputable def numberFieldResidualUnramifiedHomEquiv (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ) :
    locallyTrivialContinuousHom H (ZMod ℓ) (numberFieldResidualInertiaAway F ℓ) ≃
      locallyTrivialContinuousHom (Ω ≃ₐ[IntermediateField.adjoin F ({ζ} : Set Ω)] Ω) (ZMod ℓ)
        (numberFieldInertiaAwayInClosure F ℓ (IntermediateField.adjoin F ({ζ} : Set Ω))) :=
  locallyTrivialContinuousHomCongr (numberFieldResidualCyclotomicKernelEquiv F ℓ ζ hζ)
    (image_numberFieldResidualInertiaAway F ℓ ζ hζ)

/-- A radical is unramified away from ℓ if it is fixed by inertia at every
nonzero prime away from ℓ in the common algebraic closure. -/
def isKummerRadicalUnramifiedAway (E : IntermediateField F Ω) (β : Ω) : Prop :=
  ∀ (P : Ideal (𝓞 Ω)), P.IsPrime → (ℓ : 𝓞 Ω) ∉ P → P ≠ ⊥ →
    ∀ τ ∈ P.inertia (Ω ≃ₐ[E] Ω), τ β = β

/-- Every character counted on the residual kernel admits a Kummer
radical fixed by the inertia groups of the adjoining field away from ℓ. -/
theorem numberFieldResidualUnramifiedHom_exists_radical (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ)
    (χ : locallyTrivialContinuousHom H (ZMod ℓ) (numberFieldResidualInertiaAway F ℓ)) :
    let E := IntermediateField.adjoin F ({ζ} : Set Ω)
    let ψ := numberFieldResidualUnramifiedHomEquiv F ℓ ζ hζ χ
    ∃ (β : Ωˣ) (a : Eˣ), (β : Ω) ^ ℓ = algebraMap E Ω a ∧
      (∀ τ : Ω ≃ₐ[E] Ω, τ (β : Ω) = ζ ^ (Multiplicative.toAdd (ψ.val τ)).val * (β : Ω)) ∧
        isKummerRadicalUnramifiedAway F ℓ E (β : Ω) := by
  let E := IntermediateField.adjoin F ({ζ} : Set Ω)
  let ψ := numberFieldResidualUnramifiedHomEquiv F ℓ ζ hζ χ
  let _ : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let z : E := ⟨ζ, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩
  have hz : IsPrimitiveRoot z ℓ :=
    IsPrimitiveRoot.of_map_of_injective (show IsPrimitiveRoot (E.val z) ℓ from hζ) E.val.injective
  obtain ⟨β, a, ha, hβ⟩ := exists_kummerRadical_of_zmodCharacter hz ψ.val ψ.property.1
  have hact (τ : Ω ≃ₐ[E] Ω) : τ (β : Ω) = ζ ^ (Multiplicative.toAdd (ψ.val τ)).val * (β : Ω) := hβ τ
  refine ⟨β, a, ha, hact, fun P hp hℓ hne τ hτ => ?_⟩
  have hψ := ψ.property.2 _ ⟨P, hp, hℓ, hne, rfl⟩ τ hτ
  rw [hact, hψ]
  change ζ ^ (0 : ZMod ℓ).val * (β : Ω) = (β : Ω)
  rw [ZMod.val_zero, pow_zero, one_mul]

/-- Power classes admitting a radical fixed by inertia away from ℓ in the
common algebraic closure. -/
def numberFieldUnramifiedPowerClasses (E : IntermediateField F Ω) : Set (KummerPowerClass E ℓ) :=
  {x | ∃ (β : Ωˣ) (a : Eˣ), QuotientGroup.mk a = x ∧
    (β : Ω) ^ ℓ = algebraMap E Ω a ∧ isKummerRadicalUnramifiedAway F ℓ E (β : Ω)}

/-- The relaxed unramified characters inject into power classes with
unramified radical representatives. -/
theorem exists_injective_numberFieldResidualUnramifiedHom_to_powerClasses
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ) :
    let E := IntermediateField.adjoin F ({ζ} : Set Ω)
    ∃ f : locallyTrivialContinuousHom H (ZMod ℓ) (numberFieldResidualInertiaAway F ℓ) →
      numberFieldUnramifiedPowerClasses F ℓ E, Function.Injective f := by
  classical
  let E := IntermediateField.adjoin F ({ζ} : Set Ω)
  let e := numberFieldResidualUnramifiedHomEquiv F ℓ ζ hζ
  let _ : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let z : E := ⟨ζ, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩
  have hz : IsPrimitiveRoot z ℓ :=
    IsPrimitiveRoot.of_map_of_injective (show IsPrimitiveRoot (E.val z) ℓ from hζ) E.val.injective
  choose β a ha hact hfix using numberFieldResidualUnramifiedHom_exists_radical F ℓ ζ hζ
  refine ⟨fun χ => ⟨QuotientGroup.mk (a χ), β χ, a χ, rfl, ha χ, hfix χ⟩, ?_⟩
  intro χ ψ heq
  have hclass : (QuotientGroup.mk (a χ) : KummerPowerClass E ℓ) = QuotientGroup.mk (a ψ) :=
    congrArg (fun x : numberFieldUnramifiedPowerClasses F ℓ E => x.val) heq
  apply e.injective
  apply Subtype.ext
  exact zmodCharacter_eq_of_kummerPowerClass_eq hz (e χ).val (e ψ).val
    (β χ) (β ψ) (a χ) (a ψ) (ha χ) (ha ψ) (hact χ) (hact ψ) hclass

/-- Restriction to the residual cyclotomic kernel embeds the relaxed first
torsion layer into continuous unramified homomorphisms with values in ZMod ℓ. -/
theorem exists_injective_relaxedSelmerFirstTorsion_to_unramifiedHom (i : ℕ) :
    let V := numberFieldRelaxedSelmerKernel F ℓ i
    ∃ f : Submodule.torsionBy ℤ_[ℓ] V (ℓ : ℤ_[ℓ]) →
      locallyTrivialContinuousHom H (ZMod ℓ) (numberFieldResidualInertiaAway F ℓ),
      Function.Injective f := by
  let A := padicTateTwist F ℓ i
  let S := numberFieldRelaxedSelmerRestrictions F ℓ
  let T := numberFieldResidualInertiaAway F ℓ
  let _ : Subgroup.FiniteIndex H := Subgroup.finiteIndex_ker _
  have hdiv : Function.Surjective (fun x : A.rep => (ℓ : ℤ_[ℓ]) • x) :=
    padicTateQuotient_smul_surjective _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  have hlocal : ∀ D ∈ T, ∃ I ∈ S,
      D.map (Subgroup.subtype H) ≤ I ∧ ∀ σ ∈ D, A.rep.ρ (σ : G) = 1 := by
    intro D hD
    obtain ⟨P, hp, hpℓ, hv, rfl⟩ := hD
    let _ : P.IsPrime := hp
    let Q := P.comap (NumberField.RingOfIntegers.mapRingHom (algebraMap F Ω))
    have hQ : Q.IsPrime := hp.comap _
    have hQℓ : (ℓ : 𝓞 F) ∉ Q := by
      intro h
      change (NumberField.RingOfIntegers.mapRingHom (algebraMap F Ω)) (ℓ : 𝓞 F) ∈ P at h
      rw [map_natCast] at h
      exact hpℓ h
    let v := NumberField.FinitePlace.mk (⟨Q, hQ, hv⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    have hvQ : v.maximalIdeal.asIdeal = Q := by simp [v, NumberField.FinitePlace.maximalIdeal_mk]
    refine ⟨(P.inertia Galg : Subgroup G), ⟨v, P, ?_, hp, hvQ.symm, rfl⟩, ?_, ?_⟩
    · rw [hvQ]
      exact hQℓ
    · intro g hg
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
      exact hs
    · intro σ hσ
      apply LinearMap.ext
      intro x
      change (padicTateTwist F ℓ i).rep.ρ (σ : G) x = x
      have hg : (show Galg from σ.val) ∈ P.inertia Galg := hσ
      have hscalar : padicTateScalar F ℓ i (σ : G) = 1 :=
        padicTateScalar_eq_one_of_mem_absoluteInertia F ℓ i hpℓ hg
      rw [padicTateTwist_ρ_apply, hscalar, one_smul]
  obtain ⟨j, hj⟩ := A.exists_injective_torsionBy_to_locallyTrivialContinuousHom S H T
    (ℓ : ℤ_[ℓ]) hdiv (numberFieldResidualCyclotomicKernel_index_isUnit F ℓ)
    (fun g hg x hx => padicTateTwist_ρ_apply_eq_self_on_firstTorsion F ℓ i hg x hx) hlocal
  let M := Submodule.torsionBy ℤ_[ℓ] A.rep (ℓ : ℤ_[ℓ])
  let e : Multiplicative M ≃* Multiplicative (ZMod ℓ) :=
    (padicTateFirstTorsionAddEquivZMod ℓ).toMultiplicative
  let u (φ : locallyTrivialContinuousHom H M T) :
      locallyTrivialContinuousHom H (ZMod ℓ) T :=
    ⟨e.toMonoidHom.comp φ.val, φ.property.1.comp e,
      fun D hD σ hσ => by
        change e (φ.val σ) = 1
        rw [φ.property.2 D hD σ hσ, map_one]⟩
  have hu : Function.Injective u := by
    intro φ ψ h
    apply Subtype.ext
    apply MonoidHom.ext
    intro g
    apply e.injective
    exact congrArg (fun a : locallyTrivialContinuousHom H (ZMod ℓ) T => a.val g) h
  exact ⟨u ∘ j, hu.comp hj⟩

/-- The remaining Kummer count for the unramified homomorphisms. Its field
is the extension obtained by adjoining a primitive root of unity. -/
def HasKummerUnramifiedHomCardBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime],
    let K' := CyclotomicField p K
    letI := CyclotomicField.isCyclotomicExtension p K
    letI := IsCyclotomicExtension.numberField {p} K K'
    let T := locallyTrivialContinuousHom (numberFieldResidualCyclotomicKernel K p)
      (ZMod p) (numberFieldResidualInertiaAway K p)
    Finite T ∧ Nat.card T ≤ p ^ (2 * Module.finrank ℚ K') * NumberField.classNumber K'

/-- The residual-kernel count follows from the unramified character count
on the field containing the root. The degree and class number agree with
those of the chosen `CyclotomicField` model. -/
theorem kummerUnramifiedHomCardBound_of_adjoinRoot
    (h : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
      (ζ : AlgebraicClosure K) (hζ : IsPrimitiveRoot ζ p),
      let E := IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K))
      letI := hζ.intermediateField_adjoin_isCyclotomicExtension K
      letI := IsCyclotomicExtension.numberField {p} K E
      let T := locallyTrivialContinuousHom (AlgebraicClosure K ≃ₐ[E] AlgebraicClosure K)
        (ZMod p) (numberFieldInertiaAwayInClosure K p E)
      Finite T ∧ Nat.card T ≤ p ^ (2 * Module.finrank ℚ E) * NumberField.classNumber E) :
    HasKummerUnramifiedHomCardBound := by
  intro K _ _ p hp
  let _ : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure K) p
  let E := IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K))
  let _ := hζ.intermediateField_adjoin_isCyclotomicExtension K
  let _ : NumberField E := IsCyclotomicExtension.numberField {p} K E
  let K' := CyclotomicField p K
  let _ : IsCyclotomicExtension {p} K K' := CyclotomicField.isCyclotomicExtension p K
  let _ : NumberField K' := IsCyclotomicExtension.numberField {p} K K'
  let j := IsCyclotomicExtension.algEquiv {p} K E K'
  have hdegree : Module.finrank ℚ E = Module.finrank ℚ K' :=
    (j.restrictScalars ℚ).toLinearEquiv.finrank_eq
  have hclass : NumberField.classNumber E = NumberField.classNumber K' :=
    Fintype.card_congr (ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv j.toRingEquiv)).toEquiv
  let T := locallyTrivialContinuousHom (AlgebraicClosure K ≃ₐ[E] AlgebraicClosure K)
    (ZMod p) (numberFieldInertiaAwayInClosure K p E)
  have hbound : Finite T ∧ Nat.card T ≤ p ^ (2 * Module.finrank ℚ E) * NumberField.classNumber E :=
    h K p ζ hζ
  let _ : Finite T := hbound.1
  let e := numberFieldResidualUnramifiedHomEquiv K p ζ hζ
  exact ⟨Finite.of_equiv T e.symm, (Nat.card_congr e).le.trans (by simpa only [hdegree, hclass] using hbound.2)⟩

/-- A bound for power classes with unramified radicals suffices for the
Kummer count in the relaxed Selmer estimate. -/
theorem kummerUnramifiedHomCardBound_of_unramifiedPowerClasses
    (h : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
      (ζ : AlgebraicClosure K) (hζ : IsPrimitiveRoot ζ p),
      let E := IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K))
      letI := hζ.intermediateField_adjoin_isCyclotomicExtension K
      letI := IsCyclotomicExtension.numberField {p} K E
      let T := numberFieldUnramifiedPowerClasses K p E
      Finite T ∧ Nat.card T ≤ p ^ (2 * Module.finrank ℚ E) * NumberField.classNumber E) :
    HasKummerUnramifiedHomCardBound := by
  apply kummerUnramifiedHomCardBound_of_adjoinRoot
  intro K _ _ p _ ζ hζ
  dsimp only
  let e := numberFieldResidualUnramifiedHomEquiv K p ζ hζ
  obtain ⟨f, hf⟩ := exists_injective_numberFieldResidualUnramifiedHom_to_powerClasses K p ζ hζ
  obtain ⟨hfinite, hcard⟩ := h K p ζ hζ
  let _ := hfinite
  have hi := hf.comp e.symm.injective
  exact ⟨Finite.of_injective _ hi, (Nat.card_le_card_of_injective _ hi).trans hcard⟩

/-- Once an unramified radical gives divisible prime exponents away from ℓ,
the class group and unit count bounds the relaxed Selmer characters. -/
theorem kummerUnramifiedHomCardBound_of_primeExponentDivisibility
    (h : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
      (ζ : AlgebraicClosure K) (hζ : IsPrimitiveRoot ζ p),
      let E := IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K))
      letI := hζ.intermediateField_adjoin_isCyclotomicExtension K
      letI := IsCyclotomicExtension.numberField {p} K E
      ∀ (β : AlgebraicClosure K) (a : Eˣ), β ^ p = algebraMap E (AlgebraicClosure K) a →
        isKummerRadicalUnramifiedAway K p E β →
        ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∉ v.asIdeal →
          (p : ℤ) ∣ FractionalIdeal.count E v (toPrincipalIdeal (𝓞 E) E a).val) :
    HasKummerUnramifiedHomCardBound := by
  apply kummerUnramifiedHomCardBound_of_unramifiedPowerClasses
  intro K _ _ p _ ζ hζ
  let E := IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K))
  let _ := hζ.intermediateField_adjoin_isCyclotomicExtension K
  let _ : NumberField E := IsCyclotomicExtension.numberField {p} K E
  let f : numberFieldUnramifiedPowerClasses K p E → numberFieldValuationRestrictedPowerClasses E p :=
    fun x => ⟨x.val, by
      obtain ⟨β, a, ha, hpow, hfix⟩ := x.property
      apply Subgroup.mem_iInf.mpr
      intro v
      rw [← ha, MonoidHom.mem_ker, numberFieldPrincipalValuationResidue_mk]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h K p ζ hζ β a hpow hfix v.val v.property)⟩
  have hf : Function.Injective f := by
    intro x y hx
    apply Subtype.ext
    exact congrArg (fun z : numberFieldValuationRestrictedPowerClasses E p => z.val) hx
  obtain ⟨hfinite, hcard⟩ := finite_card_numberFieldValuationRestrictedPowerClasses_le E p
  let _ := hfinite
  exact ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans hcard⟩

/-- The unramified Kummer character count. -/
theorem kummerUnramifiedHomCardBound : HasKummerUnramifiedHomCardBound := by
  apply kummerUnramifiedHomCardBound_of_primeExponentDivisibility
  intro K _ _ p _ ζ hζ
  let E := IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K))
  let _ := hζ.intermediateField_adjoin_isCyclotomicExtension K
  let _ : NumberField E := IsCyclotomicExtension.numberField {p} K E
  dsimp only
  intro β a hβ hfix v hv
  let _ : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.asIdeal
    (S := 𝓞 (AlgebraicClosure K))
  let _ : P.IsPrime := hP.isPrime
  let _ : P.LiesOver v.asIdeal := hPv
  have hPaway : (p : 𝓞 (AlgebraicClosure K)) ∉ P := by
    intro hp
    apply hv
    rw [Ideal.over_def P v.asIdeal]
    change algebraMap (𝓞 E) (𝓞 (AlgebraicClosure K)) (p : 𝓞 E) ∈ P
    rwa [map_natCast]
  exact dvd_principalPrimeExponent_of_inertia_fixed v P p β a hβ
    (hfix P hP.isPrime hPaway (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P))

/-- The cardinal bound on unramified homomorphisms gives the exact first
torsion count for the actual relaxed restriction kernel. -/
theorem selmerKummerTorsionCardBound_of_unramifiedHomCard
    (h : HasKummerUnramifiedHomCardBound) : HasSelmerKummerTorsionCardBound := by
  intro target hprimitive e q d he hpair i hi
  dsimp only
  intro p _ hodd hdiv
  let K := selmerHostField target e q d
  obtain ⟨j, hj⟩ := exists_injective_relaxedSelmerFirstTorsion_to_unramifiedHom K p i
  obtain ⟨hfinite, hcard⟩ := h K p
  let _ := hfinite
  exact ⟨Finite.of_injective j hj, (Nat.card_le_card_of_injective j hj).trans hcard⟩

/-- The Kummer bound for the first torsion layer of the relaxed Selmer kernel. -/
theorem selmerKummerTorsionCardBound : HasSelmerKummerTorsionCardBound :=
  selmerKummerTorsionCardBound_of_unramifiedHomCard kummerUnramifiedHomCardBound

/-- The minus estimate follows from the Bernoulli comparison and the
Stickelberger annihilator. The exceptional-prime torsion count is proved. -/
theorem numberField_selmer_minus_estimate_of_comparison_exponent
    (hBernoulli : HasSelmerBernoulliValuationComparison)
    (hExp : HasSelmerStickelbergerExponentEstimate) : HasSelmerMinusEstimate :=
  numberField_selmer_minus_estimate_of_comparison_exponent_kummer hBernoulli hExp
    selmerKummerTorsionCardBound

end Riemann
