module

public import Riemann.SelmerWindowBound
import Riemann.SelmerHostConductorLower
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Utilities.CyclotomicInertia
import Utilities.CyclotomicRamificationSupport
import Utilities.NumberFieldTorsion
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.Ideal.Int
import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

@[expose] public section

open Utilities
open scoped NumberField

namespace Riemann

/-- The fixed prime for the rank-three auxiliary field can be chosen outside
the target level, independently of the two primes of a window. -/
theorem exists_selmerAuxiliaryQuadraticPrime (target : BundledDirichletCharacter) :
    ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p % 4 = 3 ∧ p.Coprime target.modulus := by
  obtain ⟨p, hp, hprime, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max 6 (target.modulus : ℕ))
      (q := 4) (a := 3) (by decide) (by decide)
  refine ⟨p, hprime, by omega, ?_, ?_⟩
  · exact hmod
  · refine hprime.coprime_iff_not_dvd.mpr fun h => ?_
    exact ((le_max_right _ _).trans_lt hp).not_ge (Nat.le_of_dvd target.modulus.pos h)

noncomputable def auxiliaryCyclotomicUnitsEquiv (p : ℕ) [Fact p.Prime] :
    (CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ) ≃* (ZMod p)ˣ := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : NeZero (p : ℚ) := ⟨by exact_mod_cast NeZero.ne p⟩
  let : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  exact IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)

private theorem auxiliaryCyclotomic_isAbelianGalois (p : ℕ) [Fact p.Prime] :
    IsAbelianGalois ℚ (CyclotomicField p ℚ) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : NeZero (p : ℚ) := ⟨by exact_mod_cast NeZero.ne p⟩
  let : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  exact IsCyclotomicExtension.isAbelianGalois {p} ℚ (CyclotomicField p ℚ)

/-- The quadratic subfield of the prime cyclotomic field fixed by squares. -/
noncomputable def selmerAuxiliaryQuadraticField (p : ℕ) [Fact p.Prime] :
    IntermediateField ℚ (CyclotomicField p ℚ) :=
  IntermediateField.fixedField
    ((selmerSquareUnits p).comap (auxiliaryCyclotomicUnitsEquiv p).toMonoidHom)

private theorem selmerAuxiliaryQuadraticField_isAbelianGalois (p : ℕ) [Fact p.Prime] :
    IsAbelianGalois ℚ (selmerAuxiliaryQuadraticField p) := by
  let := auxiliaryCyclotomic_isAbelianGalois p
  infer_instance

private noncomputable def auxiliaryGalQuotient (p : ℕ) [Fact p.Prime] :
    ((ZMod p)ˣ ⧸ selmerSquareUnits p) ≃*
      (selmerAuxiliaryQuadraticField p ≃ₐ[ℚ] selmerAuxiliaryQuadraticField p) := by
  let γ := auxiliaryCyclotomicUnitsEquiv p
  let U := selmerSquareUnits p
  let V := U.comap γ.toMonoidHom
  let := auxiliaryCyclotomic_isAbelianGalois p
  have hmap : U.map γ.symm.toMonoidHom = V := Subgroup.map_equiv_eq_comap_symm γ.symm U
  exact (QuotientGroup.congr U V γ.symm hmap).trans (IsGalois.normalAutEquivQuotient V)

private theorem auxiliaryGalQuotient_mk (p : ℕ) [Fact p.Prime] (u : (ZMod p)ˣ) :
    let _ := selmerAuxiliaryQuadraticField_isAbelianGalois p
    auxiliaryGalQuotient p (QuotientGroup.mk u) =
      ((auxiliaryCyclotomicUnitsEquiv p).symm u).restrictNormal (selmerAuxiliaryQuadraticField p) := by
  rfl

theorem finrank_selmerAuxiliaryQuadraticField (p : ℕ) [Fact p.Prime] (hp₄ : p % 4 = 3) :
    Module.finrank ℚ (selmerAuxiliaryQuadraticField p) = 2 := by
  let := selmerAuxiliaryQuadraticField_isAbelianGalois p
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (auxiliaryGalQuotient p).symm.toEquiv]
  exact selmerSquareClass_card hp₄

private theorem auxiliaryMinusOne_nontrivial (p : ℕ) [Fact p.Prime] (hp₄ : p % 4 = 3) :
    auxiliaryGalQuotient p (QuotientGroup.mk (-1 : (ZMod p)ˣ)) ≠ 1 := by
  intro h
  exact selmerSquareClass_neg_one_ne_one hp₄ ((auxiliaryGalQuotient p).map_eq_one_iff.mp h)

theorem selmerAuxiliaryQuadraticField_isTotallyComplex (p : ℕ) [Fact p.Prime]
    (hp₄ : p % 4 = 3) : NumberField.IsTotallyComplex (selmerAuxiliaryQuadraticField p) := by
  let K := CyclotomicField p ℚ
  let E := selmerAuxiliaryQuadraticField p
  let := auxiliaryCyclotomic_isAbelianGalois p
  let := selmerAuxiliaryQuadraticField_isAbelianGalois p
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : NeZero (p : ℚ) := ⟨by exact_mod_cast NeZero.ne p⟩
  let : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  constructor
  intro v
  rw [NumberField.InfinitePlace.isComplex_iff]
  intro hreal
  let ι : E →ₐ[ℚ] ℂ := v.embedding.toRatAlgHom
  let : Algebra E ℂ := ι.toRingHom.toAlgebra
  let : IsScalarTower ℚ E ℂ := IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  let j : K →ₐ[ℚ] ℂ := (IsAlgClosed.lift : K →ₐ[E] ℂ).restrictScalars ℚ
  let τ := algEquiv_complexConjugation K j
  have hτ (x : K) : j (τ x) = star (j x) := algEquiv_complexConjugation_apply K j x
  have heq : auxiliaryCyclotomicUnitsEquiv p τ = -1 :=
    cyclotomicGalEquivZMod_eq_neg_one_of_embedding_conj p K j τ hτ
  have hτ₁ : τ.restrictNormal E = 1 := by
    ext x
    apply j.injective
    rw [show ((τ.restrictNormal E x : E) : K) = τ (x : K) from AlgEquiv.restrictNormal_commutes τ E x]
    change j (τ (x : K)) = j (x : K)
    have hj : j (x : K) = v.embedding x :=
      (IsAlgClosed.lift : K →ₐ[E] ℂ).commutes x
    rw [hτ, hj]
    exact congrArg (fun f : E →+* ℂ => f x) (NumberField.ComplexEmbedding.isReal_iff.mp hreal)
  exact auxiliaryMinusOne_nontrivial p hp₄ (by
    rw [← heq, auxiliaryGalQuotient_mk, MulEquiv.symm_apply_apply]
    exact hτ₁)

/-- The fixed quadratic field retains the ramification at the auxiliary prime. -/
theorem selmerAuxiliaryQuadraticField_ramifies (p : ℕ) [Fact p.Prime]
    (hp₄ : p % 4 = 3) :
    ∃ Q : Ideal (𝓞 (selmerAuxiliaryQuadraticField p)),
      Q.IsPrime ∧ Q.LiesOver (Ideal.span {(p : ℤ)}) ∧ 1 < Q.ramificationIdx ℤ := by
  let K := CyclotomicField p ℚ
  let E := selmerAuxiliaryQuadraticField p
  let := auxiliaryCyclotomic_isAbelianGalois p
  let := selmerAuxiliaryQuadraticField_isAbelianGalois p
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : NeZero (p : ℚ) := ⟨by exact_mod_cast NeZero.ne p⟩
  let : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let M : Ideal ℤ := Ideal.span {(p : ℤ)}
  obtain ⟨P, hP, hPM⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral M (S := 𝓞 K)
  let : P.IsPrime := hP.isPrime
  let Q := P.under (𝓞 E)
  let : Q.IsPrime := hP.isPrime.comap (algebraMap (𝓞 E) (𝓞 K))
  let : P.LiesOver Q := Ideal.over_under P
  let : Q.LiesOver M := by
    constructor
    change M = (P.under (𝓞 E)).under ℤ
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over
  have htop : P.inertia (K ≃ₐ[ℚ] K) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← numberField_ramificationIdx_eq_inertia_card K p Fact.out P,
      IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p K P,
      IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.Rat.finrank p K, Nat.totient_prime Fact.out]
  let τ := (auxiliaryCyclotomicUnitsEquiv p).symm (-1)
  have hτK : τ ∈ P.inertia (K ≃ₐ[ℚ] K) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hτ : τ.restrictNormal E ∈ Q.inertia (E ≃ₐ[ℚ] E) := by
    rw [← numberField_inertia_map_restrictNormal E Q P]
    exact Subgroup.mem_map_of_mem _ hτK
  have hτ₁ : τ.restrictNormal E ≠ 1 := by
    rw [← auxiliaryGalQuotient_mk]
    exact auxiliaryMinusOne_nontrivial p hp₄
  refine ⟨Q, inferInstance, inferInstance, ?_⟩
  rw [numberField_ramificationIdx_eq_inertia_card E p Fact.out Q]
  apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
  refine ⟨Nat.card_pos.ne', fun heq => ?_⟩
  have hbot := (Q.inertia (E ≃ₐ[ℚ] E)).eq_bot_of_card_eq heq
  exact hτ₁ (by simpa [hbot] using hτ)

/-- The auxiliary quadratic field cannot lie in a cyclotomic field of
modulus prime to its ramifying prime. This is the field-level independence
input for Definition 17.17(d). -/
theorem not_selmerAuxiliaryQuadraticField_embeds_cyclotomic
    (p : ℕ) [Fact p.Prime] (hp₄ : p % 4 = 3) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) :
    ¬ Nonempty (selmerAuxiliaryQuadraticField p →ₐ[ℚ] CyclotomicField N ℚ) := by
  rintro ⟨j⟩
  let : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  obtain ⟨Q, hQ, hover, hram⟩ := selmerAuxiliaryQuadraticField_ramifies p hp₄
  exact hpN (prime_dvd_cyclotomicModulus_of_ramification (N := N) j Q hram)

/-- A ramified auxiliary quadratic field has no discriminant prime
other than its chosen prime. -/
theorem not_dvd_discr_selmerAuxiliaryQuadraticField
    (p : ℕ) [Fact p.Prime] {ℓ : ℕ} (hℓ : ℓ.Prime) (hne : ℓ ≠ p) :
    ¬ (ℓ : ℤ) ∣ NumberField.discr (selmerAuxiliaryQuadraticField p) := by
  let K := CyclotomicField p ℚ
  let E := selmerAuxiliaryQuadraticField p
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let : Fact ℓ.Prime := ⟨hℓ⟩
  apply (NumberField.not_dvd_discr_iff_forall_liesOver E (𝓞 E)
    (Nat.prime_iff_prime_int.mp hℓ)).mpr
  intro Q hQ hover
  let : Q.IsPrime := hQ.isPrime
  apply (Ideal.ramificationIdx_eq_one_iff (q := Q) (R := ℤ)).mp
  have hnot : ¬ 1 < Q.ramificationIdx ℤ := fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp
      (prime_dvd_cyclotomicModulus_of_ramification (N := p) E.val Q h))
  exact le_antisymm (Nat.le_of_not_gt hnot) (Q.ramificationIdx_pos ℤ)

/-- The auxiliary discriminant is coprime to every level not containing
the chosen auxiliary prime. -/
theorem discr_selmerAuxiliaryQuadraticField_coprime
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hpN : ¬p ∣ N) :
    (NumberField.discr (selmerAuxiliaryQuadraticField p)).natAbs.Coprime N := by
  apply Nat.coprime_of_dvd
  intro ℓ hℓ hdisc hN
  by_cases h : ℓ = p
  · exact hpN (h ▸ hN)
  · have hi : (ℓ : ℤ) ∣ NumberField.discr (selmerAuxiliaryQuadraticField p) :=
      Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdisc)
    exact not_dvd_discr_selmerAuxiliaryQuadraticField p hℓ h hi

/-- Definition 17.17(d) for any two characters whose actions factor through
the chosen cyclotomic compositum. The fixing subgroups are the actual
subgroups in the common algebraic closure. -/
theorem ker_inf_not_le_fixing_selmerAuxiliaryQuadraticField
    (p : ℕ) [Fact p.Prime] (hp₄ : p % 4 = 3) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (ι : selmerAuxiliaryQuadraticField p →ₐ[ℚ] AlgebraicClosure ℚ)
    (j : CyclotomicField N ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
    {A B : Type*} [Monoid A] [Monoid B]
    (ω : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* A)
    (ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* B)
    (hω : j.fieldRange.fixingSubgroup ≤ ω.ker)
    (hψ : j.fieldRange.fixingSubgroup ≤ ψ.ker) :
    ¬ ω.ker ⊓ ψ.ker ≤ ι.fieldRange.fixingSubgroup := by
  intro h
  have hsub : j.fieldRange.fixingSubgroup ≤ ι.fieldRange.fixingSubgroup :=
    (le_inf hω hψ).trans h
  have hfields : ι.fieldRange ≤ j.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup j.fieldRange,
      IntermediateField.le_fixedField_iff_le_fixingSubgroup]
    exact hsub
  let emb := j.equivFieldRange.symm.toAlgHom.comp
    ((IntermediateField.inclusion hfields).comp ι.equivFieldRange.toAlgHom)
  exact not_selmerAuxiliaryQuadraticField_embeds_cyclotomic p hp₄ N hpN ⟨emb⟩

/-- The same two rank-three test primes work for all auxiliary pairs
beyond a fixed threshold. They avoid the full level and auxiliary
quadratic discriminant, as required by Proposition 17.14. -/
theorem exists_selmerAuxiliaryQuadratic_testPrimes (target : BundledDirichletCharacter)
    (p : ℕ) [Fact p.Prime] :
    ∃ r₁ r₂ : ℕ, r₁.Prime ∧ r₂.Prime ∧ 7 ≤ r₁ ∧ r₁ < r₂ ∧
      ∀ e : ℕ, ∀ q d : ℕ+, SelmerEstimatePrimePair target q d →
        r₂ < (q : ℕ) → r₂ < (d : ℕ) →
        let N := selmerHostModulus target e q d
        let Δ := (NumberField.discr (selmerAuxiliaryQuadraticField p)).natAbs
        (¬ r₁ ∣ 30 * N * Δ) ∧ (¬ r₂ ∣ 30 * N * Δ) := by
  obtain ⟨r₁, hr₁, hprime₁⟩ := Nat.exists_infinite_primes (31 + (target.modulus : ℕ) + p)
  obtain ⟨r₂, hr₂, hprime₂⟩ := Nat.exists_infinite_primes (r₁ + 1)
  have hlt : r₁ < r₂ := by omega
  refine ⟨r₁, r₂, hprime₁, hprime₂, by omega, hlt, fun e q d hpair hq hd => ?_⟩
  let N := selmerHostModulus target e q d
  let Δ := (NumberField.discr (selmerAuxiliaryQuadraticField p)).natAbs
  have htest (r : ℕ) (hprime : r.Prime) (hr : 31 + (target.modulus : ℕ) + p ≤ r) (hr' : r ≤ r₂) :
      ¬r ∣ 30 * N * Δ := by
    have h30 : ¬r ∣ 30 := fun h => by
      have := Nat.le_of_dvd (by decide : 0 < 30) h
      omega
    have htarget : ¬ r ∣ (target.modulus : ℕ) := fun h => by
      have := Nat.le_of_dvd target.modulus.pos h
      omega
    have hnotN : ¬r ∣ N := hprime.coprime_iff_not_dvd.mp
      (selmerHostModulus_coprime_of_prime_lt_auxiliary target e q d hpair hprime (by omega) htarget
        (hr'.trans_lt hq) (hr'.trans_lt hd))
    have hnotΔ : ¬r ∣ Δ := fun h =>
      not_dvd_discr_selmerAuxiliaryQuadraticField p hprime (by omega)
        (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
    exact hprime.not_dvd_mul (hprime.not_dvd_mul h30 hnotN) hnotΔ
  exact ⟨htest r₁ hprime₁ hr₁ hlt.le, htest r₂ hprime₂ (by omega) le_rfl⟩

end Riemann
