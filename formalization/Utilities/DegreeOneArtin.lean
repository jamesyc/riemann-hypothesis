module

public import Utilities.ArtinSurjectivity
public import Utilities.RationalPrimeSieve
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField

namespace Utilities

/-- A rational prime outside the discriminant of the top field has
trivial relative inertia in an abelian extension. -/
theorem inertia_eq_one_of_rational_prime_not_dvd_discr
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (Q : v.asIdeal.primesOver (𝓞 L))
    (havoid : ¬ (rationalPrimeBelow K v).val ∣ (NumberField.discr L).natAbs)
    (σ : Gal(L/K)) (hσ : σ ∈ Q.val.inertia Gal(L/K)) : σ = 1 := by
  let q := rationalPrimeBelow K v
  let P := Ideal.span {(q.val : ℤ)}
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let _ : v.asIdeal.IsPrime := v.isPrime
  let _ : Q.val.IsPrime := Q.property.1
  let _ : Q.val.LiesOver v.asIdeal := Q.property.2
  let _ : v.asIdeal.LiesOver P := ⟨Int.ideal_span_absNorm_eq_self (v.asIdeal.under ℤ)⟩
  have hlo : Q.val.LiesOver P := Ideal.LiesOver.trans Q.val v.asIdeal P
  have hdiscr : ¬ (q.val : ℤ) ∣ NumberField.discr L := by
    intro h
    apply havoid
    exact_mod_cast (Int.dvd_natAbs.mpr h)
  have hunr : Algebra.IsUnramifiedIn (𝓞 L) P :=
    (NumberField.not_dvd_discr_iff_isUnramifiedIn L (𝓞 L) (Nat.prime_iff_prime_int.mp q.property)).mp hdiscr
  have hr := hunr.ramificationIdx_eq_one hlo
  have hmul := Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal Q.val
  rw [hr] at hmul
  have hrel : Q.val.ramificationIdx (𝓞 K) = 1 :=
    Nat.dvd_one.mp (hmul.symm ▸ dvd_mul_left _ _)
  have hcard : Nat.card (Q.val.inertia Gal(L/K)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal Q.val,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q.val Gal(L/K), hrel]
  let _ : Subsingleton (Q.val.inertia Gal(L/K)) := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact congrArg Subtype.val (Subsingleton.elim ⟨σ, hσ⟩ (1 : Q.val.inertia Gal(L/K)))

/-- In a nontrivial abelian extension some degree-one base prime outside
any given modulus has nontrivial arithmetic Frobenius. -/
theorem exists_degreeOne_primeArtin_ne_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] (N : ℕ) (hN : N ≠ 0)
    (hdegree : 1 < Nat.card Gal(L/K)) :
    ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.inertiaDeg ℤ = 1 ∧
      ¬ (rationalPrimeBelow K v).val ∣ N ∧ numberFieldPrimeArtin K L v ≠ 1 := by
  classical
  let M := N * (NumberField.discr L).natAbs
  let _ : NeZero M := ⟨mul_ne_zero hN (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L))⟩
  let s : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | (rationalPrimeBelow K v).val ∣ M ∨ v.asIdeal.inertiaDeg ℤ ≠ 1}
  have hI (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ s)
      (Q : v.asIdeal.primesOver (𝓞 L)) (σ : Gal(L/K)) (hσ : σ ∈ Q.val.inertia Gal(L/K)) : σ = 1 :=
    inertia_eq_one_of_rational_prime_not_dvd_discr K L v Q
      (fun h => hv (Or.inl (h.trans (dvd_mul_left _ _)))) σ hσ
  obtain ⟨v, hv, hF⟩ := exists_primeArtin_ne_one_off_summable K L s
    (summable_inverse_norm_not_degreeOne_or_dvd K M) hI hdegree
  exact ⟨v, not_not.mp (fun h => hv (Or.inr h)), fun h => hv (Or.inl (h.trans (dvd_mul_right _ _))), hF⟩

/-- In a prime-degree abelian extension the degree-one prime can be
chosen with Frobenius generating the full Galois group. -/
theorem exists_degreeOne_primeArtin_generates_of_prime_card
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] (N : ℕ) (hN : N ≠ 0)
    (hp : (Nat.card Gal(L/K)).Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.inertiaDeg ℤ = 1 ∧
      ¬ (rationalPrimeBelow K v).val ∣ N ∧ Subgroup.zpowers (numberFieldPrimeArtin K L v) = ⊤ := by
  obtain ⟨v, hd, havoid, hF⟩ := exists_degreeOne_primeArtin_ne_one K L N hN hp.one_lt
  refine ⟨v, hd, havoid, Subgroup.eq_top_of_card_eq _ ?_⟩
  rw [Nat.card_zpowers]
  exact ((Nat.dvd_prime hp).mp (orderOf_dvd_natCard _)).resolve_left
    (fun h => hF (orderOf_eq_one_iff.mp h))

/-- At a degree-one base prime the relative Artin automorphism is also
an arithmetic Frobenius over the rationals. -/
theorem degreeOne_primeArtin_isArithFrobAt_rat
    (K L : Type*) [Field K] [Algebra ℚ K] [NumberField K] [Field L] [Algebra ℚ L] [NumberField L] [Algebra K L]
    [IsScalarTower ℚ K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal.inertiaDeg ℤ = 1)
    (Q : v.asIdeal.primesOver (𝓞 L)) :
    IsArithFrobAt ℤ ((numberFieldPrimeArtin K L v).restrictScalars ℚ) Q.val := by
  let _ : v.asIdeal.IsPrime := v.isPrime
  let _ : Q.val.LiesOver v.asIdeal := Q.property.2
  have hnorm : Ideal.absNorm v.asIdeal = Ideal.absNorm (v.asIdeal.under ℤ) := by
    have hh := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
    rwa [hv, pow_one, eq_comm] at hh
  have hunder : Q.val.under ℤ = v.asIdeal.under ℤ := by
    calc
      _ = (Q.val.under (𝓞 K)).under ℤ := (Ideal.under_under Q.val).symm
      _ = _ := by rw [← Ideal.over_def Q.val v.asIdeal]
  intro x
  have hF := numberFieldPrimeArtin_spec K L v Q x
  change (numberFieldPrimeArtin K L v) • x - x ^ Nat.card (ℤ ⧸ Q.val.under ℤ) ∈ Q.val
  change (numberFieldPrimeArtin K L v) • x -
    x ^ Nat.card (𝓞 K ⧸ Q.val.under (𝓞 K)) ∈ Q.val at hF
  rw [hunder]
  rwa [← Ideal.over_def Q.val v.asIdeal, ← Ideal.absNorm_eq_natCard, hnorm,
    Ideal.absNorm_eq_natCard] at hF

end Utilities
