module

public import Riemann.SelmerCohomology
public import Utilities.PadicTateFiniteRestriction
import Utilities.AbsoluteCyclotomicInertia
import Utilities.InertiaRestriction
import Utilities.PadicTateTorsion
import Utilities.SelmerKernelAction
import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open Utilities NumberField groupCohomology
open scoped NumberField Pointwise

namespace Riemann

variable (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime]

private theorem finite_places_above_prime :
    {v : NumberField.FinitePlace F | (ℓ : 𝓞 F) ∈ v.maximalIdeal.asIdeal}.Finite := by
  have hℓ : (ℓ : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  refine (NumberField.FinitePlace.hasFiniteMulSupport_int (K := F) hℓ).subset ?_
  intro v hv
  change v (ℓ : 𝓞 F) ≠ 1
  rw [← NumberField.FinitePlace.norm_embedding_eq]
  exact ne_of_lt ((NumberField.FinitePlace.norm_lt_one_iff_mem F v.maximalIdeal _).mpr hv)

variable (i : ℕ)

local notation "Ω" => AlgebraicClosure F
local notation "G" => Field.absoluteGaloisGroup F
local notation "Galg" => Gal(Ω/F)
local notation "A" => padicTateTwist F ℓ i
local notation "D" => numberFieldSelmerRestrictions F ℓ

/-- At a sufficiently large finite cyclotomic level, the restricted
cocycle kills all finite inertia and the decomposition groups above the prime. -/
theorem exists_bound_for_tateSelmer_local_vanishing
    (c : (A).locallyTrivialCocycles₁ D) (r₀ : ℕ) (hc : (ℓ : ℤ_[ℓ]) ^ r₀ • c = 0) :
    ∃ r ≥ r₀, (ℓ : ℤ_[ℓ]) ^ r • c = 0 ∧
      ∀ (P : Ideal (𝓞 Ω)) [P.IsPrime], P ≠ ⊥ →
        ∀ σ : (padicCyclotomicReduction F ℓ r).ker,
          ((show Galg from σ.val) ∈ P.inertia Galg ∨
            ((ℓ : 𝓞 Ω) ∈ P ∧ (show Galg from σ.val) ∈ MulAction.stabilizer Galg P)) →
          c.val σ.val = 0 := by
  classical
  let V := {v : NumberField.FinitePlace F // (ℓ : 𝓞 F) ∈ v.maximalIdeal.asIdeal}
  let _ : Finite V := (finite_places_above_prime F ℓ).to_subtype
  have hlocal (v : V) : ∃ Q : Ideal (𝓞 Ω), Q.IsPrime ∧
      Q.under (𝓞 F) = v.val.maximalIdeal.asIdeal ∧ ∃ a : (A).rep,
        ∀ σ ∈ MulAction.stabilizer Galg Q, c.val σ = (A).rep.ρ σ a - a := by
    let _ : v.val.maximalIdeal.asIdeal.IsMaximal := v.val.maximalIdeal.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.val.maximalIdeal.asIdeal
      (S := 𝓞 Ω)
    let _ : Q.LiesOver v.val.maximalIdeal.asIdeal := hQv
    have hover := (Ideal.over_def Q v.val.maximalIdeal.asIdeal).symm
    refine ⟨Q, hQ.isPrime, hover, ?_⟩
    exact c.property.2 (MulAction.stabilizer Galg Q)
      ⟨v.val, Q, hQ.isPrime, hover, Or.inr ⟨v.property, rfl⟩⟩
  choose Q hQ hQv a ha using hlocal
  choose n hn using fun v : V => exists_pow_smul_eq_zero_padicTateQuotient ℓ (a v)
  obtain ⟨r₁, hr₁⟩ := (Set.finite_range n).bddAbove
  let r := max r₀ r₁
  have hr : r₀ ≤ r := le_max_left _ _
  have hrc : (ℓ : ℤ_[ℓ]) ^ r • c = 0 := pow_smul_eq_zero_of_le hr hc
  refine ⟨r, hr, hrc, ?_⟩
  intro P hP hPne σ hσ
  let _ : P.IsPrime := hP
  let v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨P.under (𝓞 F), inferInstance, Ideal.under_ne_bot _ hPne⟩
  let v := NumberField.FinitePlace.mk v₀
  have hv : P.under (𝓞 F) = v.maximalIdeal.asIdeal := by
    rw [NumberField.FinitePlace.maximalIdeal_mk]
  let g : Galg := σ.val
  by_cases hℓv : (ℓ : 𝓞 F) ∈ v.maximalIdeal.asIdeal
  · let w : V := ⟨v, hℓv⟩
    let _ : (Q w).IsPrime := hQ w
    obtain ⟨s, hs⟩ := exists_galois_smul_prime_eq_of_under_eq (Q w) P ((hQv w).trans hv.symm)
    let τ : Galg := s⁻¹ * g * s
    have hstab : g ∈ MulAction.stabilizer Galg P :=
      hσ.elim (fun hI => Ideal.inertia_le_stabilizer P hI) And.right
    have hg : g • P = P := MulAction.mem_stabilizer_iff.mp hstab
    have hτ : τ ∈ MulAction.stabilizer Galg (Q w) := by
      apply MulAction.mem_stabilizer_iff.mpr
      change (s⁻¹ * g * s) • Q w = Q w
      rw [mul_smul, mul_smul, hs, hg, ← hs, inv_smul_smul]
    have hnormal : (padicCyclotomicReduction F ℓ r).ker.Normal := inferInstance
    have hτker : (show G from τ) ∈ (padicCyclotomicReduction F ℓ r).ker :=
      hnormal.conj_mem' σ.val σ.property (show G from s)
    have hna : n w ≤ r := (hr₁ (Set.mem_range_self w)).trans (le_max_right _ _)
    have hra : (ℓ : ℤ_[ℓ]) ^ r • a w = 0 := pow_smul_eq_zero_of_le hna (hn w)
    have hzero : c.val τ = 0 := by
      rw [ha w τ hτ, padicTateTwist_ρ_apply_eq_self_on_powTorsion F ℓ i r hτker _ hra, sub_self]
    have hrs : (ℓ : ℤ_[ℓ]) ^ r • c.val s = 0 :=
      congrFun (congrArg Subtype.val hrc) (show G from s)
    have hfix := padicTateTwist_ρ_apply_eq_self_on_powTorsion F ℓ i r σ.property _ hrs
    have hconj := (A).inner_pullback_sub_eq_coboundary
      (⟨c.val, c.property.1.1⟩ : cocycles₁ (A).rep) (show G from s) σ.val
    change (A).rep.ρ s (c.val τ) - c.val σ.val = (A).rep.ρ σ.val (c.val s) - c.val s at hconj
    rwa [hzero, map_zero, hfix, sub_self, zero_sub, neg_eq_zero] at hconj
  · have haway : (ℓ : 𝓞 Ω) ∉ P := by
      intro h
      apply hℓv
      rw [← hv]
      change algebraMap (𝓞 F) (𝓞 Ω) (ℓ : 𝓞 F) ∈ P
      simpa only [map_natCast] using h
    have hI : (P.inertia Galg : Subgroup G) ∈ D := ⟨v, P, hP, hv, Or.inl rfl⟩
    obtain ⟨b, hb⟩ := c.property.2 _ hI
    have hσI := hσ.resolve_right fun h => haway h.1
    exact (hb σ.val hσI).trans (by
      rw [padicTateTwist_ρ_apply, padicTateScalar_eq_one_of_mem_absoluteInertia F ℓ i haway hσI,
        one_smul, sub_self])

/-- Every host Selmer class has a bounded representative whose restriction
at the corresponding finite cyclotomic level is unramified and kills decomposition above ℓ. -/
theorem exists_unramified_finite_tateSelmerRestriction (x : (A).selmerKernel D) :
    ∃ (r : ℕ) (c : (A).locallyTrivialCocycles₁ D) (hc : (ℓ : ℤ_[ℓ]) ^ r • c = 0),
      (Submodule.Quotient.mk c : (A).selmerKernel D) = x ∧
        IsLocallyConstant (fun σ => padicTateFiniteCocycleRestriction F ℓ i r D c hc (Additive.ofMul σ)) ∧
        ∀ (P : Ideal (𝓞 Ω)) [P.IsPrime], P ≠ ⊥ →
          ∀ σ : (padicCyclotomicReduction F ℓ r).ker,
            ((show Galg from σ.val) ∈ P.inertia Galg ∨
              ((ℓ : 𝓞 Ω) ∈ P ∧ (show Galg from σ.val) ∈ MulAction.stabilizer Galg P)) →
            padicTateFiniteCocycleRestriction F ℓ i r D c hc (Additive.ofMul σ) = 0 := by
  let _ : CompactSpace G := inferInstanceAs (CompactSpace Galg)
  obtain ⟨r₀, hx⟩ := exists_pow_smul_eq_zero_padicTateSelmerKernel F ℓ i D x
  obtain ⟨c, hcx, hc⟩ := exists_powTorsion_tateSelmerRepresentative F ℓ i r₀ D x hx
  obtain ⟨r, _, hcr, hz⟩ := exists_bound_for_tateSelmer_local_vanishing F ℓ i c r₀ hc
  exact ⟨r, c, hcr, hcx, isLocallyConstant_padicTateFiniteCocycleRestriction F ℓ i r D c hcr, hz⟩

/-- On any intermediate field containing the required roots, the same
representative gives a locally constant unramified homomorphism that kills
decomposition groups above ℓ. -/
theorem exists_unramified_tateSelmerRestriction_on_fixingSubgroup (x : (A).selmerKernel D) :
    ∃ (r : ℕ) (c : (A).locallyTrivialCocycles₁ D), (Submodule.Quotient.mk c : (A).selmerKernel D) = x ∧
      (ℓ : ℤ_[ℓ]) ^ r • c = 0 ∧
      ∀ E : IntermediateField F Ω, (∀ ζ : Ω, ζ ^ (ℓ ^ r) = 1 → ζ ∈ E) →
        ∃ ψ : Additive E.fixingSubgroup →+ (A).rep,
          (∀ σ : E.fixingSubgroup, ψ (Additive.ofMul σ) = c.val σ.val) ∧
          IsLocallyConstant (fun σ : E.fixingSubgroup => ψ (Additive.ofMul σ)) ∧
          ∀ (P : Ideal (𝓞 Ω)) [P.IsPrime], P ≠ ⊥ →
            ∀ σ : E.fixingSubgroup,
              (σ.val ∈ P.inertia Galg ∨ ((ℓ : 𝓞 Ω) ∈ P ∧ σ.val ∈ MulAction.stabilizer Galg P)) →
              ψ (Additive.ofMul σ) = 0 := by
  obtain ⟨r, c, hc, hcx, hconst, hz⟩ := exists_unramified_finite_tateSelmerRestriction F ℓ i x
  refine ⟨r, c, hcx, hc, fun E hE => ?_⟩
  let H : Subgroup G := E.fixingSubgroup
  have hle : H ≤ (padicCyclotomicReduction F ℓ r).ker := by
    intro σ hσ
    apply (mem_ker_padicCyclotomicReduction_iff F ℓ r σ).mpr
    intro ζ hζ
    exact (IntermediateField.mem_fixingSubgroup_iff E (show Galg from σ)).mp hσ ζ (hE ζ hζ)
  let j := Subgroup.inclusion hle
  let ψ := (padicTateFiniteCocycleRestriction F ℓ i r D c hc).comp j.toAdditive
  have hj : Continuous j :=
    (continuous_subtype_val : Continuous fun σ : H => σ.val).subtype_mk fun σ => hle σ.property
  refine ⟨ψ, fun _ => rfl, hconst.comp_continuous hj, ?_⟩
  intro P _ hP σ hσ
  exact hz P hP (j σ) hσ

end Riemann
