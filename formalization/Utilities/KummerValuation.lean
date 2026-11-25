module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Utilities.InertiaRestriction

@[expose] public section

open scoped NumberField nonZeroDivisors WithZero
open NumberField FractionalIdeal IsDedekindDomain

namespace Utilities

/-- The additive form of Mathlib's multiplicative adic valuation is the
negative of the exponent of the prime in the principal fractional ideal. -/
theorem numberField_valuationOfNeZero_toAdd_eq_neg_count (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    (v.valuationOfNeZero a).toAdd = -count K v (toPrincipalIdeal (𝓞 K) K a).val := by
  let t := IsLocalization.sec (𝓞 K)⁰ (a : K)
  let I := (toPrincipalIdeal (𝓞 K) K a).val
  have hrepr : I = spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K t.2)⁻¹ *
      (Ideal.span {t.1} : Ideal (𝓞 K)) := by
    dsimp only [I]
    rw [coe_toPrincipalIdeal, coeIdeal_span_singleton, ← map_mul]
    congr 1
    have hsec := IsLocalization.sec_spec (𝓞 K)⁰ (a : K)
    change (a : K) * algebraMap (𝓞 K) K t.2 = algebraMap (𝓞 K) K t.1 at hsec
    have hne : algebraMap (𝓞 K) K t.2 ≠ 0 :=
      (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (nonZeroDivisors.coe_ne_zero t.2)
    rw [← hsec, mul_comm (a : K), inv_mul_cancel_left₀ hne]
  rw [show count K v I = _ from count_well_defined K v (toPrincipalIdeal (𝓞 K) K a).ne_zero hrepr]
  change -(↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {t.1})).factors) : ℤ) -
      -(↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(t.2 : 𝓞 K)})).factors) : ℤ) = _
  ring

/-- A radical lying in a finite extension of ramification index one has
prime exponent divisible by the power at the prime downstairs. -/
theorem dvd_principalPrimeExponent_of_radical_ramificationIdx_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (hw : w.asIdeal.ramificationIdx (𝓞 K) = 1) (n : ℕ) (β : L) (a : Kˣ)
    (hβ : β ^ n = algebraMap K L a) :
    (n : ℤ) ∣ count K v (toPrincipalIdeal (𝓞 K) K a).val := by
  by_cases hn : n = 0
  · subst n
    rw [pow_zero, eq_comm, ← map_one (algebraMap K L)] at hβ
    have ha : a = 1 := Units.ext ((algebraMap K L).injective hβ)
    simp [ha, count_one]
  have hβ₀ : β ≠ 0 := by
    intro hz
    apply Units.ne_zero a
    apply (algebraMap K L).injective
    rw [map_zero, ← hβ, hz, zero_pow hn]
  let b : Lˣ := Units.mk0 β hβ₀
  have hval := HeightOneSpectrum.valuation_liesOver L v w (a : K)
  rw [hw, pow_one, ← hβ, map_pow] at hval
  have heq : v.valuationOfNeZero a = (w.valuationOfNeZero b) ^ n := by
    apply WithZero.coe_inj.mp
    rw [WithZero.coe_pow, HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq]
    exact hval
  have h := congrArg Multiplicative.toAdd heq
  rw [Int.toAdd_pow, numberField_valuationOfNeZero_toAdd_eq_neg_count] at h
  refine ⟨-(w.valuationOfNeZero b).toAdd, ?_⟩
  linarith only [h]

/-- The ramification index at a nonzero prime of a number field equals
its inertia order in any finite Galois group for the extension. -/
theorem numberField_ramificationIdx_eq_card_inertia {K L G : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    P.ramificationIdx (𝓞 K) = Nat.card (P.inertia G) := by
  let _ : v.asIdeal.IsPrime := v.isPrime
  let _ : v.asIdeal.IsMaximal := v.isMaximal
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P G]
  exact (Ideal.card_inertia_eq_ramificationIdxIn (G := G) v.asIdeal P).symm

/-- An inertia-fixed radical in a finite Galois extension lies in the inertia
field. The prime on that field has ramification index one over the base. -/
theorem dvd_principalPrimeExponent_of_finite_inertia_fixed
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (n : ℕ) (β : L) (a : Kˣ) (hβ : β ^ n = algebraMap K L a)
    (hfix : ∀ τ ∈ P.inertia Gal(L/K), τ β = β) :
    (n : ℤ) ∣ count K v (toPrincipalIdeal (𝓞 K) K a).val := by
  let H := P.inertia Gal(L/K)
  let T := IntermediateField.fixedField H
  let _ : NumberField T := NumberField.of_module_finite K T
  let Q := P.under (𝓞 T)
  let _ : Q.IsPrime := inferInstanceAs (P.under (𝓞 T)).IsPrime
  let _ : P.LiesOver Q := Ideal.over_under P
  let _ : Q.LiesOver v.asIdeal := ⟨by
    change v.asIdeal = (P.under (𝓞 T)).under (𝓞 K)
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over⟩
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let w : HeightOneSpectrum (𝓞 T) := ⟨Q, inferInstance, hQ⟩
  let _ : IsGaloisGroup H T L :=
    .of_mulEquiv_algEquiv (IntermediateField.subgroupEquivAlgEquiv H) fun _ _ => rfl
  have htop : P.ramificationIdx (𝓞 K) = Nat.card H :=
    numberField_ramificationIdx_eq_card_inertia (G := Gal(L/K)) v P
  have hrel := numberField_ramificationIdx_eq_card_inertia (G := H) w P
  have hI : Nat.card (P.inertia H) = Nat.card H := by
    rw [← Subgroup.card_subtype, AddSubgroup.inertia_map_subtype]
    change Nat.card ↥(H ⊓ H) = Nat.card H
    rw [inf_idem]
  have hrel' : P.ramificationIdx (𝓞 T) = Nat.card H := hrel.trans hI
  have htower : Nat.card H = Q.ramificationIdx (𝓞 K) * Nat.card H :=
    htop.symm.trans ((Ideal.ramificationIdx_tower (R := 𝓞 K) Q P).trans
      (congrArg (Q.ramificationIdx (𝓞 K) * ·) hrel'))
  have hram : Q.ramificationIdx (𝓞 K) = 1 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (htower.symm.trans (one_mul _).symm)
  let b : T := ⟨β, (IntermediateField.mem_fixedField_iff _ _).mpr hfix⟩
  have hpow : b ^ n = algebraMap K T a := Subtype.ext hβ
  exact dvd_principalPrimeExponent_of_radical_ramificationIdx_one v w hram n b a hpow

/-- Pass from a radical fixed by inertia in an algebraic extension to the
finite Galois subextension generated by the radical. -/
theorem dvd_principalPrimeExponent_of_inertia_fixed
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (n : ℕ) (β : L) (a : Kˣ) (hβ : β ^ n = algebraMap K L a)
    (hfix : ∀ τ ∈ P.inertia Gal(L/K), τ β = β) :
    (n : ℤ) ∣ count K v (toPrincipalIdeal (𝓞 K) K a).val := by
  let T := FiniteGaloisIntermediateField.adjoin K ({β} : Set L)
  let E := T.toIntermediateField
  let _ : NumberField E := NumberField.of_module_finite K E
  let b : E := ⟨β, FiniteGaloisIntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
  let Q := P.under (𝓞 E)
  let _ : Q.IsPrime := inferInstanceAs (P.under (𝓞 E)).IsPrime
  let _ : Q.LiesOver v.asIdeal := ⟨by
    change v.asIdeal = (P.under (𝓞 E)).under (𝓞 K)
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over⟩
  have hb : b ^ n = algebraMap K E a := Subtype.ext hβ
  apply dvd_principalPrimeExponent_of_finite_inertia_fixed v Q n b a hb
  intro τ hτ
  have hproj := numberField_inertia_map_restrictNormal_of_isGalois T P
  obtain ⟨σ, hσ, heq⟩ := Subgroup.mem_map.mp (hproj.symm ▸ hτ)
  apply Subtype.ext
  change ((τ b : E) : L) = β
  rw [← heq]
  change algebraMap E L (σ.restrictNormal E b) = β
  rw [AlgEquiv.restrictNormal_commutes]
  exact hfix σ hσ

end Utilities
