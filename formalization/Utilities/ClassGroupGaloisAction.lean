module

public import Utilities.ClassGroupPrimeValues
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

@[expose] public section

open NumberField
open scoped NumberField nonZeroDivisors

namespace Utilities

/-- An isomorphism of rings acts on their nonzero integral ideals. -/
def nonzeroIdealMapOfRingEquiv {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (e : R ≃+* S) : (Ideal R)⁰ →* (Ideal S)⁰ where
  toFun I := ⟨I.val.map e, mem_nonZeroDivisors_iff_ne_zero.mpr
    (fun h => (mem_nonZeroDivisors_iff_ne_zero.mp I.property)
      ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h))⟩
  map_one' := Subtype.ext (by
    change (1 : Ideal R).map e.toRingHom = (1 : Ideal S)
    simp only [Ideal.one_eq_top, Ideal.map_top])
  map_mul' I J := Subtype.ext (Ideal.map_mul e I.val J.val)

section Transport

variable {R S T K L M : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [CommRing T] [IsDedekindDomain T] [Field M] [Algebra T M]
  [IsFractionRing T M]

variable (K L) in
theorem classGroupMulEquivOfRingEquiv_mk0_map (e : R ≃+* S) (I : (Ideal R)⁰) :
    classGroupMulEquivOfRingEquiv K L e (ClassGroup.mk0 I) =
      ClassGroup.mk0 (nonzeroIdealMapOfRingEquiv e I) :=
  classGroupMulEquivOfRingEquiv_mk0 K L e I _

variable (K) in
theorem classGroupMulEquivOfRingEquiv_refl_apply (c : ClassGroup R) :
    classGroupMulEquivOfRingEquiv K K (RingEquiv.refl R) c = c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [classGroupMulEquivOfRingEquiv_mk0_map]
  apply congrArg ClassGroup.mk0
  apply Subtype.ext
  exact Ideal.map_id I.val

variable (K L M) in
theorem classGroupMulEquivOfRingEquiv_trans_apply (e : R ≃+* S) (f : S ≃+* T) (c : ClassGroup R) :
    classGroupMulEquivOfRingEquiv K M (e.trans f) c =
      classGroupMulEquivOfRingEquiv L M f (classGroupMulEquivOfRingEquiv K L e c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [classGroupMulEquivOfRingEquiv_mk0_map]
  apply congrArg ClassGroup.mk0
  apply Subtype.ext
  exact (Ideal.map_map (I := I.val) e.toRingHom f.toRingHom).symm

end Transport

section Galois

variable (F E : Type*) [Field F] [Field E] [NumberField E] [Algebra F E]

/-- The Galois action on the additive class group. -/
noncomputable def numberFieldClassGroupGaloisAction :
    Representation ℤ Gal(E/F) (Additive (ClassGroup (𝓞 E))) where
  toFun σ := (MonoidHom.toAdditive
    (classGroupMulEquivOfRingEquiv E E (RingOfIntegers.mapRingEquiv σ.toRingEquiv)).toMonoidHom).toIntLinearMap
  map_one' := by
    ext c
    change classGroupMulEquivOfRingEquiv E E (RingEquiv.refl (𝓞 E)) c.toMul = c.toMul
    exact classGroupMulEquivOfRingEquiv_refl_apply E _
  map_mul' σ τ := by
    ext c
    change classGroupMulEquivOfRingEquiv E E
        ((RingOfIntegers.mapRingEquiv τ.toRingEquiv).trans (RingOfIntegers.mapRingEquiv σ.toRingEquiv)) c.toMul =
      classGroupMulEquivOfRingEquiv E E (RingOfIntegers.mapRingEquiv σ.toRingEquiv)
        (classGroupMulEquivOfRingEquiv E E (RingOfIntegers.mapRingEquiv τ.toRingEquiv) c.toMul)
    exact classGroupMulEquivOfRingEquiv_trans_apply E E E _ _ _

@[simp]
theorem numberFieldClassGroupGaloisAction_apply_mk0 (σ : Gal(E/F)) (I : (Ideal (𝓞 E))⁰) :
    numberFieldClassGroupGaloisAction F E σ (Additive.ofMul (ClassGroup.mk0 I)) =
      Additive.ofMul (ClassGroup.mk0 (nonzeroIdealMapOfRingEquiv
        (RingOfIntegers.mapRingEquiv σ.toRingEquiv) I)) :=
  congrArg Additive.ofMul (classGroupMulEquivOfRingEquiv_mk0_map E E _ I)

end Galois

section Norm

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]

omit [IsGalois ℚ E] in
private theorem absNorm_map_ringEquiv_integer (e : 𝓞 E ≃+* 𝓞 E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  let _ : Infinite (𝓞 E) := Infinite.of_injective (Nat.cast : ℕ → 𝓞 E) Nat.cast_injective
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv).symm

/-- The product of all conjugates of an integral ideal is the extension of its norm. -/
theorem prod_galois_map_ideal_eq_map_relNorm_int [Fintype Gal(E/ℚ)]
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    (∏ σ : Gal(E/ℚ), I.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv)) =
      (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 E)) := by
  let J : Ideal (𝓞 E) := ∏ σ : Gal(E/ℚ), I.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv)
  have hle : (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 E)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    change algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) ∈ J
    have hnorm : algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) =
        ∏ σ : Gal(E/ℚ), RingOfIntegers.mapRingEquiv σ.toRingEquiv x := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ E,
        Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_automorphisms, map_prod]
      rw [show AlgEquiv.fintype ℚ E = (inferInstance : Fintype Gal(E/ℚ)) from Subsingleton.elim _ _]
      rfl
    rw [hnorm]
    exact Ideal.prod_mem_prod fun _ _ => Ideal.mem_map_of_mem _ hx
  obtain ⟨D, hD⟩ := Ideal.dvd_iff_le.mpr hle
  have hnorm := congrArg Ideal.absNorm hD
  change Ideal.absNorm ((Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 E))) =
    Ideal.absNorm ((∏ σ : Gal(E/ℚ), I.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv)) * D) at hnorm
  rw [map_mul, map_prod, Ideal.absNorm_algebraMap, Ideal.absNorm_relNorm] at hnorm
  simp only [absNorm_map_ringEquiv_integer, Finset.prod_const, Finset.card_univ] at hnorm
  rw [RingOfIntegers.rank, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card] at hnorm
  have hnonzero : Ideal.absNorm I ^ Fintype.card Gal(E/ℚ) ≠ 0 :=
    pow_ne_zero _ fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
  have hD1 : Ideal.absNorm D = 1 :=
    (mul_left_cancel₀ hnonzero ((mul_one _).trans hnorm)).symm
  change J = _
  rw [hD, Ideal.absNorm_eq_one_iff.mp hD1, Ideal.mul_top]

/-- The norm element acts trivially on the class group of a Galois number
field over the rationals since the norm ideal is principal. -/
theorem sum_numberFieldClassGroupGaloisAction_eq_zero [Fintype Gal(E/ℚ)]
    (c : Additive (ClassGroup (𝓞 E))) :
    ∑ σ : Gal(E/ℚ), numberFieldClassGroupGaloisAction ℚ E σ c = 0 := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c.toMul
  have hc : c = Additive.ofMul (ClassGroup.mk0 I) := congrArg Additive.ofMul hI.symm
  rw [hc]
  simp only [numberFieldClassGroupGaloisAction_apply_mk0, ← ofMul_prod, ← map_prod]
  let J := ∏ σ : Gal(E/ℚ), nonzeroIdealMapOfRingEquiv (RingOfIntegers.mapRingEquiv σ.toRingEquiv) I
  change Additive.ofMul (ClassGroup.mk0 J) = Additive.ofMul 1
  apply congrArg Additive.ofMul
  apply (ClassGroup.mk0_eq_one_iff J.property).mpr
  have hJ : J.val = (Ideal.relNorm ℤ I.val).map (algebraMap ℤ (𝓞 E)) := by
    change (nonZeroDivisors (Ideal (𝓞 E))).subtype
      (∏ σ : Gal(E/ℚ), nonzeroIdealMapOfRingEquiv (RingOfIntegers.mapRingEquiv σ.toRingEquiv) I) = _
    rw [map_prod]
    exact prod_galois_map_ideal_eq_map_relNorm_int I.val (mem_nonZeroDivisors_iff_ne_zero.mp I.property)
  rw [hJ, Ideal.relNorm_int, Ideal.map_span, Set.image_singleton]
  exact ⟨⟨_, rfl⟩⟩

end Norm

end Utilities
