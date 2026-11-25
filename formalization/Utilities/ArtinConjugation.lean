module

public import Utilities.ArtinIdeal
import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors IsMulCommutative

namespace Utilities

section Towers

variable {K K' L L' : Type*} [Field K] [Field K'] [Field L] [Field L']
  [Algebra K L] [Algebra K' L']

/-- Conjugation by a ring isomorphism of extensions compatible with the
given isomorphism of the base fields. -/
def conjugateAlgEquivOfTowerRingEquiv (a : K ≃+* K') (b : L ≃+* L')
    (h : ∀ x : K, b (algebraMap K L x) = algebraMap K' L' (a x)) (σ : Gal(L/K)) :
    Gal(L'/K') :=
  AlgEquiv.ofRingEquiv (f := b.symm.trans (σ.toRingEquiv.trans b)) (by
    intro x
    obtain ⟨y, rfl⟩ := a.surjective x
    change b (σ (b.symm (algebraMap K' L' (a y)))) = algebraMap K' L' (a y)
    rw [← h, b.symm_apply_apply, σ.commutes, h])

@[simp]
theorem conjugateAlgEquivOfTowerRingEquiv_apply (a : K ≃+* K') (b : L ≃+* L') (h) (σ : Gal(L/K)) (x : L') :
    conjugateAlgEquivOfTowerRingEquiv a b h σ x = b (σ (b.symm x)) := rfl

/-- An isomorphism of towers induces the corresponding isomorphism of Galois groups. -/
def galoisMulEquivOfTowerRingEquiv (a : K ≃+* K') (b : L ≃+* L')
    (h : ∀ x : K, b (algebraMap K L x) = algebraMap K' L' (a x)) :
    Gal(L/K) ≃* Gal(L'/K') := by
  have h' (x : K') : b.symm (algebraMap K' L' x) = algebraMap K L (a.symm x) := by
    apply b.injective
    rw [b.apply_symm_apply, h, a.apply_symm_apply]
  exact
    { toFun := conjugateAlgEquivOfTowerRingEquiv a b h
      invFun := conjugateAlgEquivOfTowerRingEquiv a.symm b.symm h'
      left_inv := fun σ => AlgEquiv.ext fun x => by simp
      right_inv := fun σ => AlgEquiv.ext fun x => by simp
      map_mul' := fun σ τ => AlgEquiv.ext fun x => by simp [AlgEquiv.mul_apply] }

@[simp]
theorem galoisMulEquivOfTowerRingEquiv_apply (a : K ≃+* K') (b : L ≃+* L') (h) (σ : Gal(L/K)) (x : L') :
    galoisMulEquivOfTowerRingEquiv a b h σ x = b (σ (b.symm x)) := rfl

/-- Transporting a prime along a tower isomorphism commutes with contraction. -/
theorem under_map_ringOfIntegers_of_towerRingEquiv
    (a : K ≃+* K') (b : L ≃+* L')
    (h : ∀ x : K, b (algebraMap K L x) = algebraMap K' L' (a x)) (Q : Ideal (𝓞 L)) :
    (Q.map (RingOfIntegers.mapRingEquiv b)).under (𝓞 K') =
      (Q.under (𝓞 K)).map (RingOfIntegers.mapRingEquiv a) := by
  let A := RingOfIntegers.mapRingEquiv a
  let B := RingOfIntegers.mapRingEquiv b
  have hInt (x : 𝓞 K) : B (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K') (𝓞 L') (A x) := RingOfIntegers.ext (h (x : K))
  ext y
  obtain ⟨x, rfl⟩ := A.surjective y
  change algebraMap (𝓞 K') (𝓞 L') (A x) ∈ Q.map B ↔ A x ∈ (Q.under (𝓞 K)).map A
  rw [← hInt, Ideal.apply_mem_of_equiv_iff, Ideal.apply_mem_of_equiv_iff]
  rfl

variable [NumberField K] [NumberField K'] [NumberField L] [NumberField L']
  [IsGalois K L] [IsGalois K' L']

/-- Arithmetic Frobenius is transported by conjugation under a tower isomorphism. -/
theorem isArithFrobAt_galoisMulEquivOfTowerRingEquiv
    (a : K ≃+* K') (b : L ≃+* L')
    (h : ∀ x : K, b (algebraMap K L x) = algebraMap K' L' (a x))
    (Q : Ideal (𝓞 L)) {σ : Gal(L/K)} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    IsArithFrobAt (𝓞 K') (galoisMulEquivOfTowerRingEquiv a b h σ)
      (Q.map (RingOfIntegers.mapRingEquiv b)) := by
  let A := RingOfIntegers.mapRingEquiv a
  let B := RingOfIntegers.mapRingEquiv b
  let Q' := Q.map B
  have hQ' : Q'.under (𝓞 K') = (Q.under (𝓞 K)).map A :=
    under_map_ringOfIntegers_of_towerRingEquiv a b h Q
  have hcard : Nat.card (𝓞 K' ⧸ Q'.under (𝓞 K')) = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) :=
    (Nat.card_congr (Ideal.quotientEquiv (Q.under (𝓞 K)) (Q'.under (𝓞 K')) A hQ').toEquiv).symm
  intro y
  obtain ⟨z, rfl⟩ := B.surjective y
  change galoisMulEquivOfTowerRingEquiv a b h σ • B z -
    (B z) ^ Nat.card (𝓞 K' ⧸ Q'.under (𝓞 K')) ∈ Q'
  have hsmul : galoisMulEquivOfTowerRingEquiv a b h σ • B z = B (σ • z) := by
    apply RingOfIntegers.ext
    change galoisMulEquivOfTowerRingEquiv a b h σ (b (z : L)) = b (σ (z : L))
    simp
  rw [hcard, hsmul, ← map_pow, ← map_sub]
  exact Ideal.apply_mem_of_equiv_iff.mpr (hσ z)

end Towers

section Artin

variable {K K' L L' : Type*} [Field K] [Field K'] [Field L] [Field L']
  [NumberField K] [NumberField K'] [NumberField L] [NumberField L']
  [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
  [IsAbelianGalois K L] [IsAbelianGalois K' L']

/-- The prime Artin symbol is natural under isomorphisms of towers at
unramified primes. -/
theorem numberFieldPrimeArtin_galoisMulEquivOfTowerRingEquiv
    (a : K ≃+* K') (b : L ≃+* L')
    (h : ∀ x : K, b (algebraMap K L x) = algebraMap K' L' (a x))
    (v : HeightOneSpectrum (𝓞 K))
    (hI : ∀ (P : Ideal (𝓞 L')) [P.IsPrime], P ≠ ⊥ → ∀ τ ∈ P.inertia Gal(L'/K'), τ = 1) :
    galoisMulEquivOfTowerRingEquiv a b h (numberFieldPrimeArtin K L v) =
      numberFieldPrimeArtin K' L' (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv a) v) := by
  let A := RingOfIntegers.mapRingEquiv a
  let B := RingOfIntegers.mapRingEquiv b
  let w := HeightOneSpectrum.equivOfRingEquiv A v
  let Q := Classical.choice (numberField_primesOver_nonempty K L v)
  let P := Q.val.map B
  have hP : P.IsPrime := by
    change (Q.val.map B).IsPrime
    rw [← Ideal.comap_symm]
    exact Q.property.1.comap B.symm
  have hPQ : P.under (𝓞 K') = w.asIdeal := by
    rw [show P = Q.val.map B from rfl, under_map_ringOfIntegers_of_towerRingEquiv a b h, ← Q.property.2.over]
    exact (Ideal.comap_symm A).symm
  let P' : w.asIdeal.primesOver (𝓞 L') := ⟨P, hP, ⟨hPQ.symm⟩⟩
  let _ : P.IsPrime := hP
  let _ : P.LiesOver w.asIdeal := P'.property.2
  exact eq_numberFieldPrimeArtin_of_isArithFrobAt K' L' w P'
    (isArithFrobAt_galoisMulEquivOfTowerRingEquiv a b h Q.val (numberFieldPrimeArtin_spec K L v Q))
    (hI P (Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot P))

/-- Artin on fractional ideals commutes with the two transports when the
target extension is unramified at the finite primes. -/
theorem numberFieldIdealArtin_equivariant
    (a : K ≃+* K') (b : L ≃+* L')
    (h : ∀ x : K, b (algebraMap K L x) = algebraMap K' L' (a x))
    (hI : ∀ (P : Ideal (𝓞 L')) [P.IsPrime], P ≠ ⊥ → ∀ τ ∈ P.inertia Gal(L'/K'), τ = 1) :
    (galoisMulEquivOfTowerRingEquiv a b h).toMonoidHom.comp (numberFieldIdealArtin K L) =
      (numberFieldIdealArtin K' L').comp
        (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K' (RingOfIntegers.mapRingEquiv a))).toMonoidHom := by
  apply fractionalIdealHom_ext_on_primes (R := 𝓞 K) (K := K)
  intro v
  let A := RingOfIntegers.mapRingEquiv a
  let w := HeightOneSpectrum.equivOfRingEquiv A v
  let m := Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K' A).toMulEquiv
  let γ := galoisMulEquivOfTowerRingEquiv a b h
  let I : (Ideal (𝓞 K))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  let J : (Ideal (𝓞 K'))⁰ := ⟨w.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr w.ne_bot⟩
  have hw : w.asIdeal = v.asIdeal.map A := Ideal.comap_symm A
  have hv : v.asIdeal.map A ∈ (Ideal (𝓞 K'))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr (hw ▸ w.ne_bot)
  have hm : m (FractionalIdeal.mk0 K I) = FractionalIdeal.mk0 K' J :=
    (fractionalIdealUnits_mapEquiv_mk0 K K' A I hv).trans
      (congrArg (FractionalIdeal.mk0 K') (Subtype.ext hw.symm))
  have hleft : numberFieldIdealArtin K L (FractionalIdeal.mk0 K I) = numberFieldPrimeArtin K L v :=
    numberFieldIdealArtin_mk0_prime K L v
  have hright : numberFieldIdealArtin K' L' (m (FractionalIdeal.mk0 K I)) =
      numberFieldPrimeArtin K' L' w :=
    (congrArg (numberFieldIdealArtin K' L') hm).trans (numberFieldIdealArtin_mk0_prime K' L' w)
  exact (congrArg γ hleft).trans
    ((numberFieldPrimeArtin_galoisMulEquivOfTowerRingEquiv a b h v hI).trans hright.symm)

/-- Principal-ideal triviality transfers to a conjugate unramified extension. -/
theorem numberFieldIdealArtin_principal_eq_one_of_towerRingEquiv
    (a : K ≃+* K') (b : L ≃+* L')
    (h : ∀ x : K, b (algebraMap K L x) = algebraMap K' L' (a x))
    (hp : ∀ x : Kˣ, numberFieldIdealArtin K L (toPrincipalIdeal (𝓞 K) K x) = 1)
    (hI : ∀ (P : Ideal (𝓞 L')) [P.IsPrime], P ≠ ⊥ → ∀ τ ∈ P.inertia Gal(L'/K'), τ = 1)
    (y : K'ˣ) : numberFieldIdealArtin K' L' (toPrincipalIdeal (𝓞 K') K' y) = 1 := by
  let A := RingOfIntegers.mapRingEquiv a
  let m := Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K' A).toMulEquiv
  let γ := galoisMulEquivOfTowerRingEquiv a b h
  let f := numberFieldIdealArtin K L
  let f' := numberFieldIdealArtin K' L'
  have hmap : (toPrincipalIdeal (𝓞 K) K).range.map m.toMonoidHom =
      (toPrincipalIdeal (𝓞 K') K').range :=
    FractionalIdeal.map_ringEquivOfRingEquiv_toPrincipalIdeal (K := K) (L := K') A
  have hy : toPrincipalIdeal (𝓞 K') K' y ∈ (toPrincipalIdeal (𝓞 K) K).range.map m.toMonoidHom :=
    hmap.symm ▸ (show toPrincipalIdeal (𝓞 K') K' y ∈ (toPrincipalIdeal (𝓞 K') K').range from ⟨y, rfl⟩)
  obtain ⟨I, ⟨x, rfl⟩, he⟩ := Subgroup.mem_map.mp hy
  have hcomm : γ (f (toPrincipalIdeal (𝓞 K) K x)) = f' (m (toPrincipalIdeal (𝓞 K) K x)) :=
    DFunLike.congr_fun (numberFieldIdealArtin_equivariant a b h hI) _
  calc
    f' (toPrincipalIdeal (𝓞 K') K' y) = f' (m (toPrincipalIdeal (𝓞 K) K x)) := congrArg f' he.symm
    _ = γ (f (toPrincipalIdeal (𝓞 K) K x)) := hcomm.symm
    _ = 1 := by rw [show f (toPrincipalIdeal (𝓞 K) K x) = 1 from hp x, map_one]

/-- Given principal-ideal reciprocity on the two extensions, the
class-group Artin maps commute with both transports. -/
theorem numberFieldClassGroupArtinOfPrincipal_equivariant
    (a : K ≃+* K') (b : L ≃+* L')
    (h : ∀ x : K, b (algebraMap K L x) = algebraMap K' L' (a x))
    (hp : ∀ x : Kˣ, numberFieldIdealArtin K L (toPrincipalIdeal (𝓞 K) K x) = 1)
    (hp' : ∀ x : K'ˣ, numberFieldIdealArtin K' L' (toPrincipalIdeal (𝓞 K') K' x) = 1)
    (hI : ∀ (P : Ideal (𝓞 L')) [P.IsPrime], P ≠ ⊥ → ∀ τ ∈ P.inertia Gal(L'/K'), τ = 1) :
    (galoisMulEquivOfTowerRingEquiv a b h).toMonoidHom.comp (numberFieldClassGroupArtinOfPrincipal K L hp) =
      (numberFieldClassGroupArtinOfPrincipal K' L' hp').comp
        (classGroupMulEquivOfRingEquiv K K' (RingOfIntegers.mapRingEquiv a)).toMonoidHom := by
  apply classGroupHom_ext_on_primeClasses
  intro v
  let A := RingOfIntegers.mapRingEquiv a
  let w := HeightOneSpectrum.equivOfRingEquiv A v
  have hw : w.asIdeal = v.asIdeal.map A := Ideal.comap_symm A
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, numberFieldClassGroupArtinOfPrincipal_mk0_prime]
  rw [classGroupMulEquivOfRingEquiv_mk0 K K' A _
    (mem_nonZeroDivisors_iff_ne_zero.mpr (hw ▸ w.ne_bot))]
  have hclass : ClassGroup.mk0 ⟨v.asIdeal.map A, mem_nonZeroDivisors_iff_ne_zero.mpr (hw ▸ w.ne_bot)⟩ =
      ClassGroup.mk0 ⟨w.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr w.ne_bot⟩ :=
    congrArg ClassGroup.mk0 (Subtype.ext hw.symm)
  rw [hclass, numberFieldClassGroupArtinOfPrincipal_mk0_prime]
  exact numberFieldPrimeArtin_galoisMulEquivOfTowerRingEquiv a b h v hI

end Artin

end Utilities
