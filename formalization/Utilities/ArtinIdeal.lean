module

public import Utilities.ClassGroupPrimeValues
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Frobenius
import Utilities.InertiaRestriction
import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open IsDedekindDomain NumberField
open scoped NumberField IsMulCommutative nonZeroDivisors Pointwise

namespace Utilities

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField L] in
theorem numberField_primesOver_nonempty (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (v.asIdeal.primesOver (𝓞 L)) := by
  let _ : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.asIdeal (S := 𝓞 L)
  exact ⟨⟨Q, hQ.isPrime, hQv⟩⟩

omit [NumberField K] in
theorem numberField_finite_residue_above (v : HeightOneSpectrum (𝓞 K))
    (Q : v.asIdeal.primesOver (𝓞 L)) : Finite (𝓞 L ⧸ Q.val) := by
  let _ : Q.val.LiesOver v.asIdeal := Q.property.2
  exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.val)

variable [FiniteDimensional K L] [IsAbelianGalois K L]

/-- An arithmetic Frobenius at a prime above the chosen base prime. -/
noncomputable def numberFieldArithFrobAbove (v : HeightOneSpectrum (𝓞 K))
    (Q : v.asIdeal.primesOver (𝓞 L)) : Gal(L/K) := by
  let _ : Q.val.IsPrime := Q.property.1
  let _ : Finite (𝓞 L ⧸ Q.val) := numberField_finite_residue_above K L v Q
  exact arithFrobAt (𝓞 K) Gal(L/K) Q.val

theorem numberFieldArithFrobAbove_spec (v : HeightOneSpectrum (𝓞 K))
    (Q : v.asIdeal.primesOver (𝓞 L)) :
    IsArithFrobAt (𝓞 K) (numberFieldArithFrobAbove K L v Q) Q.val := by
  let _ : Q.val.IsPrime := Q.property.1
  let _ : Finite (𝓞 L ⧸ Q.val) := numberField_finite_residue_above K L v Q
  exact IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) Q.val

/-- Arithmetic Frobenius in an abelian extension is independent of the prime above. -/
theorem numberFieldArithFrobAbove_eq (v : HeightOneSpectrum (𝓞 K))
    (P Q : v.asIdeal.primesOver (𝓞 L)) :
    numberFieldArithFrobAbove K L v P = numberFieldArithFrobAbove K L v Q := by
  let _ : P.val.IsPrime := P.property.1
  let _ : Q.val.IsPrime := Q.property.1
  let _ : Finite (𝓞 L ⧸ P.val) := numberField_finite_residue_above K L v P
  let _ : Finite (𝓞 L ⧸ Q.val) := numberField_finite_residue_above K L v Q
  change arithFrobAt (𝓞 K) Gal(L/K) P.val = arithFrobAt (𝓞 K) Gal(L/K) Q.val
  exact isConj_iff_eq.mp (isConj_arithFrobAt (𝓞 K) Gal(L/K) P.val Q.val
    (P.property.2.over.symm.trans Q.property.2.over))

/-- The prime symbol obtained from arithmetic Frobenius. At unramified
primes the symbol is uniquely characterized by the Frobenius congruence. -/
noncomputable def numberFieldPrimeArtin (v : HeightOneSpectrum (𝓞 K)) : Gal(L/K) :=
  numberFieldArithFrobAbove K L v (Classical.choice (numberField_primesOver_nonempty K L v))

theorem numberFieldPrimeArtin_spec (v : HeightOneSpectrum (𝓞 K))
    (Q : v.asIdeal.primesOver (𝓞 L)) :
    IsArithFrobAt (𝓞 K) (numberFieldPrimeArtin K L v) Q.val := by
  rw [numberFieldPrimeArtin, numberFieldArithFrobAbove_eq K L v _ Q]
  exact numberFieldArithFrobAbove_spec K L v Q

theorem eq_numberFieldPrimeArtin_of_isArithFrobAt (v : HeightOneSpectrum (𝓞 K))
    (Q : v.asIdeal.primesOver (𝓞 L)) {σ : Gal(L/K)} (hσ : IsArithFrobAt (𝓞 K) σ Q.val)
    (hI : ∀ τ ∈ Q.val.inertia Gal(L/K), τ = 1) :
    σ = numberFieldPrimeArtin K L v :=
  mul_inv_eq_one.mp (hI _ (hσ.mul_inv_mem_inertia (numberFieldPrimeArtin_spec K L v Q)))

theorem numberFieldPrimeArtin_eq_one_of_trivial_decomposition (v : HeightOneSpectrum (𝓞 K))
    (Q : v.asIdeal.primesOver (𝓞 L)) (hD : ∀ τ ∈ MulAction.stabilizer Gal(L/K) Q.val, τ = 1) :
    numberFieldPrimeArtin K L v = 1 := by
  let _ : Q.val.IsPrime := Q.property.1
  exact hD _ (numberFieldPrimeArtin_spec K L v Q).mem_stabilizer

/-- Extend the arithmetic Frobenius values multiplicatively to fractional ideals. -/
noncomputable def numberFieldIdealArtin : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* Gal(L/K) :=
  fractionalIdealHomOfPrimeValues (numberFieldPrimeArtin K L)

@[simp]
theorem numberFieldIdealArtin_mk0_prime (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldIdealArtin K L
      (FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩) =
      numberFieldPrimeArtin K L v :=
  fractionalIdealHomOfPrimeValues_mk0 (numberFieldPrimeArtin K L) v

/-- The class-group Artin map, given principal-ideal reciprocity. -/
noncomputable def numberFieldClassGroupArtinOfPrincipal
    (hprincipal : ∀ x : Kˣ, numberFieldIdealArtin K L (toPrincipalIdeal (𝓞 K) K x) = 1) :
    ClassGroup (𝓞 K) →* Gal(L/K) :=
  classGroupHomOfTrivialPrincipal (numberFieldIdealArtin K L) hprincipal

@[simp]
theorem numberFieldClassGroupArtinOfPrincipal_mk0_prime
    (hprincipal : ∀ x : Kˣ, numberFieldIdealArtin K L (toPrincipalIdeal (𝓞 K) K x) = 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    numberFieldClassGroupArtinOfPrincipal K L hprincipal
      (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩) =
      numberFieldPrimeArtin K L v := by
  rw [← ClassGroup.mk_mk0 (K := K), numberFieldClassGroupArtinOfPrincipal,
    classGroupHomOfTrivialPrincipal_mk, numberFieldIdealArtin_mk0_prime]

/-- At an unramified prime, the class-group Artin value equals every
automorphism satisfying the arithmetic Frobenius congruence. -/
theorem numberFieldClassGroupArtinOfPrincipal_eq_of_isArithFrobAt
    (hprincipal : ∀ x : Kˣ, numberFieldIdealArtin K L (toPrincipalIdeal (𝓞 K) K x) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (Q : v.asIdeal.primesOver (𝓞 L))
    {σ : Gal(L/K)} (hσ : IsArithFrobAt (𝓞 K) σ Q.val)
    (hI : ∀ τ ∈ Q.val.inertia Gal(L/K), τ = 1) :
    numberFieldClassGroupArtinOfPrincipal K L hprincipal
      (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩) = σ :=
  (numberFieldClassGroupArtinOfPrincipal_mk0_prime K L hprincipal v).trans
    (eq_numberFieldPrimeArtin_of_isArithFrobAt K L v Q hσ hI).symm

section Tower

variable (E : Type*) [Field E] [NumberField E] [Algebra K E] [Algebra E L]
  [IsScalarTower K E L] [FiniteDimensional K E] [IsAbelianGalois K E]

omit [FiniteDimensional K L] [FiniteDimensional K E] in
/-- Frobenius over a number field restricts to Frobenius at the contracted prime. -/
theorem numberFieldArithFrob_restrictNormal
    (P : Ideal (𝓞 L)) {σ : Gal(L/K)} (hσ : IsArithFrobAt (𝓞 K) σ P) :
    IsArithFrobAt (𝓞 K) (σ.restrictNormal E) (P.under (𝓞 E)) := by
  intro z
  change algebraMap (𝓞 E) (𝓞 L)
    (σ.restrictNormal E • z - z ^ Nat.card (𝓞 K ⧸ (P.under (𝓞 E)).under (𝓞 K))) ∈ P
  rw [Ideal.under_under, map_sub, map_pow, algebraMap_ringOfIntegers_restrictNormal_smul]
  exact hσ (algebraMap (𝓞 E) (𝓞 L) z)

/-- Prime Artin symbols commute with restriction to an unramified subextension. -/
theorem numberFieldPrimeArtin_restrictNormal (v : HeightOneSpectrum (𝓞 K))
    (hI : ∀ P : v.asIdeal.primesOver (𝓞 E), ∀ τ ∈ P.val.inertia Gal(E/K), τ = 1) :
    (numberFieldPrimeArtin K L v).restrictNormal E = numberFieldPrimeArtin K E v := by
  let Q : v.asIdeal.primesOver (𝓞 L) := Classical.choice (numberField_primesOver_nonempty K L v)
  let _ : Q.val.IsPrime := Q.property.1
  let _ : Q.val.LiesOver v.asIdeal := Q.property.2
  let P : v.asIdeal.primesOver (𝓞 E) :=
    ⟨Q.val.under (𝓞 E), inferInstance,
      ⟨(Ideal.over_def Q.val v.asIdeal).trans (Ideal.under_under Q.val).symm⟩⟩
  exact eq_numberFieldPrimeArtin_of_isArithFrobAt K E v P
    (numberFieldArithFrob_restrictNormal (K := K) (L := L) (E := E) Q.val (numberFieldPrimeArtin_spec K L v Q)) (hI P)

/-- Restricting Artin on fractional ideals commutes with passing to a
finite abelian subextension unramified at the finite primes. -/
theorem numberFieldIdealArtin_restrictNormal
    (hI : ∀ (v : HeightOneSpectrum (𝓞 K)) (P : v.asIdeal.primesOver (𝓞 E)),
      ∀ τ ∈ P.val.inertia Gal(E/K), τ = 1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (numberFieldIdealArtin K L I).restrictNormal E = numberFieldIdealArtin K E I := by
  let r : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  change r (∏ᶠ v, numberFieldPrimeArtin K L v ^ FractionalIdeal.count K v I.val) =
    ∏ᶠ v, numberFieldPrimeArtin K E v ^ FractionalIdeal.count K v I.val
  rw [map_finprod r (hasFiniteMulSupport_primeValues_zpow (numberFieldPrimeArtin K L) I.val)]
  apply finprod_congr
  intro v
  rw [map_zpow]
  exact congrArg (fun σ : Gal(E/K) => σ ^ FractionalIdeal.count K v I.val)
    (numberFieldPrimeArtin_restrictNormal K L E v (hI v))

end Tower

/-- The principal-ideal part of Artin reciprocity for finite abelian
extensions of totally complex number fields unramified at the finite primes. -/
def HasTotallyComplexUnramifiedPrincipalReciprocity : Prop :=
  ∀ (E T : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field T] [NumberField T]
    [Algebra E T] [FiniteDimensional E T] [IsAbelianGalois E T],
      (∀ (P : Ideal (𝓞 T)) [P.IsPrime], P ≠ ⊥ → ∀ t ∈ P.inertia Gal(T/E), t = 1) →
      ∀ x : Eˣ, numberFieldIdealArtin E T (toPrincipalIdeal (𝓞 E) E x) = 1

end Utilities
