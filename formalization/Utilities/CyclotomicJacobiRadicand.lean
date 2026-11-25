module

public import Utilities.CyclotomicCarryPrincipal
public import Utilities.CyclotomicJacobiIdeal
import Utilities.CyclotomicPrimeSieve
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.DedekindDomain.Factorization
import Utilities.IdealClassPrimeSieve

@[expose] public section

open NumberField IsCyclotomicExtension IsDedekindDomain FractionalIdeal
open scoped NumberField Pointwise nonZeroDivisors

namespace Utilities

private theorem count_product_of_distinct_prime_ideals
    (E : Type*) [Field E] [NumberField E] {ι : Type*} [Fintype ι]
    (P : ι → HeightOneSpectrum (𝓞 E)) (hP : Function.Injective P) (d : ι → ℤ) (i : ι) :
    count E (P i) (∏ j, ((P j).asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ d j) = d i := by
  classical
  rw [count_prod]
  · simp only [count_zpow, count_maximal, hP.eq_iff]
    simp [Finset.sum_ite_eq']
  · intro j _
    exact zpow_ne_zero _ (coeIdeal_ne_zero.mpr (P j).ne_bot)

variable (N : ℕ) [NeZero N] (E : Type*) [Field E] [NumberField E]
  [IsCyclotomicExtension {N} ℚ E]

local notation "χ" => MulEquiv.symm (Rat.galEquivZMod N E)

private theorem cyclotomicConjugatePrime_one (v : HeightOneSpectrum (𝓞 E)) :
    cyclotomicConjugatePrime N E v 1 = v := by
  apply HeightOneSpectrum.ext
  rw [cyclotomicConjugatePrime_asIdeal, map_one, inv_one, one_smul]

/-- At a degree-one prime of a cyclotomic field away from the level, the
rational prime has principal prime exponent one. -/
theorem exists_rat_prime_unit_of_cyclotomic_degreeOne
    (p : ℕ) [Fact p.Prime]
    (red : 𝓞 E →+* ZMod p) (v : HeightOneSpectrum (𝓞 E))
    (hred : RingHom.ker red = v.asIdeal) (hpN : ¬ p ∣ N) :
    ∃ u : Eˣ, (u : E) = p ∧ count E v (toPrincipalIdeal (𝓞 E) E u).val = 1 := by
  have hp₀ : (p : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let u := Units.mk0 (p : E) hp₀
  obtain ⟨hinj, hs⟩ := cyclotomic_degreeOne_conjugates_split N E p red v hred hpN
  refine ⟨u, rfl, ?_⟩
  rw [coe_toPrincipalIdeal]
  change count E v (spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E (p : 𝓞 E))) = 1
  rw [← coeIdeal_span_singleton, hs]
  change count E v ((coeIdealHom (𝓞 E)⁰ E) (∏ b, (cyclotomicConjugatePrime N E v b).asIdeal)) = 1
  rw [map_prod]
  change count E v (∏ t, ((cyclotomicConjugatePrime N E v t).asIdeal : FractionalIdeal (𝓞 E)⁰ E)) = 1
  have hc := count_product_of_distinct_prime_ideals E
    (cyclotomicConjugatePrime N E v) hinj (fun _ => 1) 1
  rw [cyclotomicConjugatePrime_one N E v] at hc
  simpa only [zpow_one] using hc

/-- Every signed Jacobi ideal has a generator whose complex conjugate is its
inverse. The original ideal can have arbitrary residue degrees. -/
theorem exists_cyclotomicJacobiGenerator (b : ℕ) (I : (Ideal (𝓞 E))⁰) :
    ∃ X : Eˣ, X * Units.map (χ (-1)).toRingEquiv.toMonoidHom X = 1 ∧
      toPrincipalIdeal (𝓞 E) E X = cyclotomicJacobiIdeal N E b I := by
  let d (t : (ZMod N)ˣ) := b * t.val.val / N
  let F (t : (ZMod N)ˣ) := FractionalIdeal.mk0 E (cyclotomicInverseConjugateIdeal N E t I)
  let J := ∏ t : (ZMod N)ˣ, cyclotomicInverseConjugateIdeal N E t I ^ d t
  have hJ : J = ∏ j ∈ Finset.range b, cyclotomicCarryIdealProduct N E (j : ZMod N) 1 I := by
    simpa only [J, d, one_mul, mul_one] using cyclotomicFloorProduct_eq_prod_carry N E b 1 I
  have hCl : ClassGroup.mk0 J = 1 := by
    rw [hJ, map_prod]
    exact Finset.prod_eq_one fun j _ => (ClassGroup.mk0_eq_one_iff _).mpr
      (cyclotomicCarryIdealProduct_principal E N (j : ZMod N) 1 I)
  obtain ⟨u, hu⟩ := (ClassGroup.mk0_eq_one_iff J.property).mp hCl
  have hu₀ : (u : E) ≠ 0 := by
    intro h
    have h' : u = 0 := (RingOfIntegers.coe_eq_zero_iff).mp h
    exact nonZeroDivisors.coe_ne_zero J (by simpa [h'] using hu)
  let y := Units.mk0 (u : E) hu₀
  let c := Units.map (χ (-1)).toRingEquiv.toMonoidHom
  have hprod : toPrincipalIdeal (𝓞 E) E y = ∏ t : (ZMod N)ˣ, F t ^ d t := by
    have h : toPrincipalIdeal (𝓞 E) E y = FractionalIdeal.mk0 E J := by
      apply Units.ext
      rw [coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, hu, coeIdeal_span_singleton]
      rfl
    rw [h]
    simp only [J, map_prod, map_pow, F]
  have hinv : (χ (-1))⁻¹ = χ (-1) := by rw [← map_inv, inv_neg, inv_one]
  have hconj : toPrincipalIdeal (𝓞 E) E (c y) = ∏ t : (ZMod N)ˣ, F t ^ d (-t) := by
    have h := cyclotomicInverseConjugatePrincipalIdeal N E (-1) y
    rw [hinv] at h
    change toPrincipalIdeal (𝓞 E) E (Units.map (χ (-1)).toRingEquiv.toMonoidHom y) = _
    rw [← h, hprod, map_prod]
    simp only [map_pow, F, cyclotomicInverseConjugateFractionalIdeal_mk0, neg_one_mul]
    exact Fintype.prod_equiv (Equiv.neg _) _ _ (fun t => by simp)
  refine ⟨y / c y, ?_, ?_⟩
  · have hc : c (c y) = y := by
      apply Units.ext
      change χ (-1) (χ (-1) (y : E)) = (y : E)
      rw [← AlgEquiv.mul_apply, ← map_mul]
      simp
    change (y / c y) * c (y / c y) = 1
    rw [map_div, hc, div_mul_div_cancel, div_self']
  · rw [map_div, hprod, hconj]
    simp only [cyclotomicJacobiIdeal, cyclotomicSignedFloor, d, F, Units.val_neg, zpow_sub,
      zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib, div_eq_mul_inv]

/-- At a split prime, binary carry principal ideals construct the
initial Jacobi radicand with the prescribed signed prime exponents. -/
theorem exists_cyclotomicJacobiRadicand
    (p : ℕ) [Fact p.Prime]
    (red : 𝓞 E →+* ZMod p) (v : HeightOneSpectrum (𝓞 E))
    (hred : RingHom.ker red = v.asIdeal) (hpN : ¬ p ∣ N) (b : ℕ) :
    ∃ X : Eˣ, X * Units.map (χ (-1)).toRingEquiv.toMonoidHom X = 1 ∧
      ∀ t : (ZMod N)ˣ, count E v (toPrincipalIdeal (𝓞 E) E
        (Units.map (χ t).toRingEquiv.toMonoidHom X)).val = cyclotomicSignedFloor N b t.val := by
  let P := cyclotomicConjugatePrime N E v
  let I := heightOnePrimeIdeal E v
  obtain ⟨hP, -⟩ := cyclotomic_degreeOne_conjugates_split N E p red v hred hpN
  obtain ⟨X, hX, hXI⟩ := exists_cyclotomicJacobiGenerator N E b I
  refine ⟨X, hX, fun t => ?_⟩
  have hIP (j : (ZMod N)ˣ) :
      cyclotomicInverseConjugateIdeal N E j I = heightOnePrimeIdeal E (P j) := by
    apply Subtype.ext
    change v.asIdeal.map (RingOfIntegers.mapRingEquiv ((χ j)⁻¹ : Gal(E/ℚ)).toRingEquiv).toRingHom =
      (P j).asIdeal
    rw [cyclotomicConjugatePrime_asIdeal, Ideal.pointwise_smul_def]
    rfl
  have htransport := cyclotomicInverseConjugatePrincipalIdeal N E t⁻¹ X
  rw [map_inv, inv_inv, hXI, cyclotomicInverseConjugateJacobiIdeal] at htransport
  rw [← htransport]
  change count E v (Units.coeHom _ (∏ j : (ZMod N)ˣ,
    FractionalIdeal.mk0 E (cyclotomicInverseConjugateIdeal N E (t⁻¹ * j) I) ^
      cyclotomicSignedFloor N b j.val)) = _
  rw [map_prod]
  simp only [map_zpow, Units.coeHom_apply, hIP, FractionalIdeal.coe_mk0]
  let P' (j : (ZMod N)ˣ) := P (t⁻¹ * j)
  have hP' : Function.Injective P' := fun _ _ h => mul_left_cancel (hP h)
  have ht : P' t = v := by
    change P (t⁻¹ * t) = v
    rw [inv_mul_cancel]
    exact cyclotomicConjugatePrime_one N E v
  exact (congrArg (fun v' => count E v' _) ht.symm).trans
    (count_product_of_distinct_prime_ideals E P' hP'
      (fun j => cyclotomicSignedFloor N b j.val) t)

end Utilities
