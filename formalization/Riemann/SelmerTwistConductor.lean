module

public import Riemann.SelmerTwistLocalWitness
public import Utilities.CyclotomicCharacter
import Riemann.SelmerStickelbergerReciprocity
import Utilities.InertiaRestriction
import Utilities.RationalPrime

@[expose] public section

open NumberField Utilities DiscreteGaloisModule IsCyclotomicExtension
open scoped NumberField Pointwise

namespace Riemann

section Host

variable (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
  (ℓ : ℕ) [Fact ℓ.Prime] (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))

local notation "F" => selmerHostField target e q d
local notation "Ω" => AlgebraicClosure F
local notation "f" => selmerHostConductor target e q d
local instance : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
local instance : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω

private theorem exists_selmerHostCyclotomicLayer_characterValue [NeZero f] (ψ : Gal(F/ℚ) →* Oˣ) :
    ∃ E : IntermediateField F Ω, ∃ _ : IsCyclotomicExtension {f} ℚ E,
      let _ : NumberField E := IsCyclotomicExtension.numberField {f} ℚ E
      let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {f} ℚ E
      ∀ τ : Gal(E/ℚ),
        (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ) (Rat.galEquivZMod f E τ) =
          O.val (ψ (τ.restrictNormal F) : O) := by
  obtain ⟨E, hE, hres⟩ := exists_selmerHostCyclotomicLayer target e q d f (dvd_refl f)
  let _ : NumberField E := IsCyclotomicExtension.numberField {f} ℚ E
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {f} ℚ E
  refine ⟨E, hE, fun τ => ?_⟩
  have hr := hres τ
  simp only [ZMod.unitsMap_self, MonoidHom.id_apply] at hr
  rw [hr]
  simp [selmerDirichletOfCharacter]

/-- An absolute automorphism fixing the roots of the primitive conductor
acts trivially through the finite host character. -/
theorem selmerHostCharacter_eq_one_of_fixes_conductor_roots (ψ : Gal(F/ℚ) →* Oˣ)
    (s : Gal(Ω/ℚ))
    (hfix : ∀ z : Ω,
      z ^ (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ).conductor = 1 → s z = z) :
    ψ (s.restrictNormal F) = 1 := by
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  obtain ⟨E, hE, hχ⟩ := exists_selmerHostCyclotomicLayer_characterValue target e q d ℓ O ψ
  let _ : NumberField E := IsCyclotomicExtension.numberField {f} ℚ E
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {f} ℚ E
  let χ := selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ
  have h := cyclotomic_character_eq_one_of_fixes_conductor_roots E χ (s.restrictNormal E) (by
    intro z hz
    apply (algebraMap E Ω).injective
    rw [s.restrictNormal_commutes E]
    exact hfix _ (by rw [← map_pow, hz, map_one]))
  have hr : s.restrictNormal F = (s.restrictNormal E).restrictNormal F :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F E s
  rw [hχ, ← hr] at h
  apply Units.ext
  apply (show Function.Injective (O.val : O →ₐ[ℤ_[ℓ]] PadicAlgCl ℓ) from Subtype.val_injective)
  simpa only [Units.val_one, map_one] using h

/-- The Dirichlet conductor detects triviality of the actual host
character on absolute inertia over each rational prime. -/
theorem selmerHostCharacter_trivialOnInertia_iff_conductor
    (ψ : Gal(F/ℚ) →* Oˣ) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 Ω)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (∀ s ∈ P.inertia Gal(Ω/ℚ), ψ (s.restrictNormal F) = 1) ↔
      ¬ p ∣ (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ).conductor := by
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  obtain ⟨E, hE, hχ⟩ := exists_selmerHostCyclotomicLayer_characterValue target e q d ℓ O ψ
  let _ : IsCyclotomicExtension {f} ℚ E := hE
  let _ : NumberField E := IsCyclotomicExtension.numberField {f} ℚ E
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {f} ℚ E
  let E₀ := E.restrictScalars ℚ
  let _ : FiniteDimensional ℚ E₀ := inferInstanceAs (FiniteDimensional ℚ E)
  let _ : IsGalois ℚ E₀ := inferInstanceAs (IsGalois ℚ E)
  let C : FiniteGaloisIntermediateField ℚ Ω := ⟨E₀⟩
  let Q := P.under (𝓞 E)
  let _ : Q.IsPrime := inferInstanceAs (P.under (𝓞 E)).IsPrime
  let _ : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨(Ideal.over_def P (Ideal.span {(p : ℤ)})).trans (Ideal.under_under P).symm⟩
  have hmap : (P.inertia Gal(Ω/ℚ)).map (AlgEquiv.restrictNormalHom E) = Q.inertia Gal(E/ℚ) :=
    numberField_inertia_map_restrictNormal_of_isGalois C P
  let χ := selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ
  have hr (s : Gal(Ω/ℚ)) :
      s.restrictNormal F = (s.restrictNormal E).restrictNormal F :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F E s
  change _ ↔ ¬ p ∣ χ.conductor
  rw [← cyclotomic_character_trivialOnInertia_iff (p := p) E Q χ]
  constructor
  · intro hi τ hτ
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hτ)
    have hrt : s.restrictNormal F = τ.restrictNormal F :=
      (hr s).trans (congrArg (AlgEquiv.restrictNormalHom F) hst)
    rw [hχ τ, ← hrt, hi s hs, Units.val_one, map_one]
  · intro hi s hs
    have hs' : s.restrictNormal E ∈ Q.inertia Gal(E/ℚ) :=
      hmap ▸ Subgroup.mem_map_of_mem (AlgEquiv.restrictNormalHom E) hs
    have hz := hi _ hs'
    rw [hχ, ← hr] at hz
    apply Units.ext
    apply (show Function.Injective (O.val : O →ₐ[ℤ_[ℓ]] PadicAlgCl ℓ) from Subtype.val_injective)
    simpa only [Units.val_one, map_one] using hz

/-- Divisors of the primitive conductor admit a nontrivial inertia element. -/
theorem selmerHostCharacter_nontrivialOnInertia_iff_conductor
    (ψ : Gal(F/ℚ) →* Oˣ) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 Ω)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (∃ s ∈ P.inertia Gal(Ω/ℚ), ψ (s.restrictNormal F) ≠ 1) ↔
      p ∣ (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ).conductor := by
  classical
  simpa only [not_forall, not_imp, exists_prop, not_not] using
    not_congr (selmerHostCharacter_trivialOnInertia_iff_conductor target e q d ℓ O ψ p P)

/-- At a tame conductor prime, an inertia element acts with invertible
difference from the identity when the host degree is prime to ℓ. -/
theorem sharedTwist_exists_inertia_subOne_bijective_of_dvd_conductor [IsLocalRing O]
    (i : ℕ) (ψ : Gal(F/ℚ) →* Oˣ) (hdegree : ¬ ℓ ∣ Module.finrank ℚ F)
    (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (hpχ : p ∣ (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ).conductor)
    (P : Ideal (𝓞 Ω)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ s ∈ P.inertia Gal(Ω/ℚ),
      Function.Bijective
        ((numberFieldSelmerSharedInverseTwist F ℓ i O ψ).rep.ρ s - 1 :
          Module.End O (numberFieldSelmerSharedInverseTwist F ℓ i O ψ).rep) := by
  obtain ⟨s, hs, hψ⟩ :=
    (selmerHostCharacter_nontrivialOnInertia_iff_conductor target e q d ℓ O ψ p P).mpr hpχ
  have hℓ : (ℓ : 𝓞 Ω) ∉ P := by
    rw [natCast_mem_iff_dvd_of_liesOver_rationalPrime P p ℓ]
    intro h
    exact hpℓ (((Nat.dvd_prime (Fact.out : ℓ.Prime)).mp h).resolve_left (Fact.out : p.Prime).ne_one)
  exact ⟨s, hs, sharedTwist_inertia_subOne_bijective_of_nontrivial F ℓ i O ψ hdegree hℓ hs hψ⟩

/-- The decomposition family needing bounded witnesses is supported
exactly at the primitive conductor times the Tate prime. -/
theorem selmerSharedTwistBadDecompositions_eq_primitiveConductorPrime
    (ψ : Gal(F/ℚ) →* Oˣ) :
    let χ := selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ
    numberFieldSelmerSharedTwistBadDecompositions F ℓ O ψ =
      {J | ∃ P : Ideal (𝓞 Ω), P.IsPrime ∧ P ≠ ⊥ ∧
        ((χ.conductor * ℓ : ℕ) : 𝓞 Ω) ∈ P ∧ J = MulAction.stabilizer Gal(Ω/ℚ) P} := by
  dsimp only
  let χ := selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ
  have h (P : Ideal (𝓞 Ω)) [P.IsPrime] (hne : P ≠ ⊥) :
      ((ℓ : 𝓞 Ω) ∈ P ∨ ∃ s ∈ P.inertia Gal(Ω/ℚ), ψ (s.restrictNormal F) ≠ 1) ↔
        ((χ.conductor * ℓ : ℕ) : 𝓞 Ω) ∈ P := by
    obtain ⟨p, hp, hover⟩ := exists_rationalPrime_below P hne
    let _ : Fact p.Prime := ⟨hp⟩
    let _ : P.LiesOver (Ideal.span {(p : ℤ)}) := hover
    have hram := selmerHostCharacter_nontrivialOnInertia_iff_conductor target e q d ℓ O ψ p P
    rw [natCast_mem_iff_dvd_of_liesOver_rationalPrime P p ℓ, hram,
      natCast_mem_iff_dvd_of_liesOver_rationalPrime P p (χ.conductor * ℓ), hp.dvd_mul, or_comm]
  ext J
  constructor
  · rintro ⟨P, hp, hne, hbad, he⟩
    let _ : P.IsPrime := hp
    exact ⟨P, hp, hne, (h P hne).mp hbad, he⟩
  · rintro ⟨P, hp, hne, hbad, he⟩
    let _ : P.IsPrime := hp
    exact ⟨P, hp, hne, (h P hne).mpr hbad, he⟩

/-- The normalized cocycle vanishes on inertia outside the primitive
conductor times the Tate prime. -/
theorem sharedTwistCocycle_eq_zero_away_primitiveConductorPrime (i : ℕ)
    (ψ : Gal(F/ℚ) →* Oˣ)
    (c : DiscreteGaloisModule.normalizedSelmerCocycles (numberFieldSelmerSharedInverseTwist F ℓ i O ψ)
      (numberFieldSelmerRestrictionsIn ℚ Ω ℓ) (numberFieldTwistNormalizationElement F))
    (P : Ideal (𝓞 Ω)) [P.IsPrime] (hne : P ≠ ⊥)
    (haway : (((selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ).conductor * ℓ : ℕ)
      : 𝓞 Ω) ∉ P) {s : Gal(Ω/ℚ)} (hs : s ∈ P.inertia Gal(Ω/ℚ)) :
    c.val s = 0 := by
  let χ := selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ
  obtain ⟨p, hp, hover⟩ := exists_rationalPrime_below P hne
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : P.LiesOver (Ideal.span {(p : ℤ)}) := hover
  have hdvd : ¬ p ∣ χ.conductor * ℓ :=
    fun h => haway ((natCast_mem_iff_dvd_of_liesOver_rationalPrime P p _).mpr h)
  have hℓ : (ℓ : 𝓞 Ω) ∉ P :=
    fun h => hdvd (dvd_mul_of_dvd_right ((natCast_mem_iff_dvd_of_liesOver_rationalPrime P p ℓ).mp h) _)
  have hχ : ¬ p ∣ χ.conductor := fun h => hdvd (dvd_mul_of_dvd_left h ℓ)
  exact sharedTwistCocycle_eq_zero_on_unramified_inertia F ℓ i O ψ c hne hℓ
    ((selmerHostCharacter_trivialOnInertia_iff_conductor target e q d ℓ O ψ p P).mpr hχ) hs

/-- At a primitive conductor prime or the Tate prime, the exponent bounding
the cocycle also bounds a coboundary witness on the decomposition group. -/
theorem sharedTwistArithmeticLayer_bounded_at_primitiveConductorPrime (i r : ℕ)
    (ψ : Gal(F/ℚ) →* Oˣ) (c : numberFieldSelmerSharedTwistArithmeticLayer F ℓ i O ψ r)
    (P : Ideal (𝓞 Ω)) [P.IsPrime] (hne : P ≠ ⊥)
    (hP : (((selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ).conductor * ℓ : ℕ)
      : 𝓞 Ω) ∈ P) :
    ∃ b : (numberFieldSelmerSharedInverseTwist F ℓ i O ψ).rep, (ℓ : O) ^ r • b = 0 ∧
      ∀ g ∈ MulAction.stabilizer Gal(Ω/ℚ) P,
        c.val.val g = (numberFieldSelmerSharedInverseTwist F ℓ i O ψ).rep.ρ g b - b := by
  have h : MulAction.stabilizer Gal(Ω/ℚ) P ∈ numberFieldSelmerSharedTwistBadDecompositions F ℓ O ψ := by
    rw [selmerSharedTwistBadDecompositions_eq_primitiveConductorPrime target e q d ℓ O ψ]
    exact ⟨P, inferInstance, hne, hP, rfl⟩
  exact c.property.2 _ h

end Host
end Riemann
