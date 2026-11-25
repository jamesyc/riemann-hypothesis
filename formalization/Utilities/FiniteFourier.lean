module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Abel

@[expose] public section

open scoped BigOperators Classical

namespace Utilities

/-- The sign character of the additive group of order two. -/
noncomputable def zmodTwoSign : AddChar (ZMod 2) ℂ where
  toFun x := if x = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    have hcases (a : ZMod 2) : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    rcases hcases x with rfl | rfl <;> rcases hcases y with rfl | rfl <;> simp [htwo]

@[simp] theorem zmodTwoSign_apply (x : ZMod 2) :
    zmodTwoSign x = if x = 0 then 1 else -1 := rfl

/-- A character of a finite subgroup of complex units is a power of the inclusion. -/
theorem finite_complex_unit_subgroup_character_eq_pow
    (S : Subgroup ℂˣ) [Finite S] (χ : S →* ℂ) :
    ∃ i < Nat.card S, ∀ s : S, χ s = (((s : ℂˣ) : ℂ)) ^ i := by
  let z : S →* ℂ := (Units.coeHom ℂ).comp S.subtype
  have hz : Function.Injective z := Units.val_injective.comp Subtype.val_injective
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic S)
  have hprimitive : IsPrimitiveRoot (z g) (Nat.card S) := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_injective z hz, orderOf_eq_card_of_zpowers_eq_top hg]
  let _ : NeZero (Nat.card S) := ⟨Nat.card_pos.ne'⟩
  have hroot : χ g ^ Nat.card S = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  obtain ⟨i, hi, heq⟩ := hprimitive.eq_pow_of_pow_eq_one hroot
  refine ⟨i, hi, fun s => ?_⟩
  change χ s = z s ^ i
  have hs : s ∈ Submonoid.powers g :=
    (isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers.mpr (hg.ge (Subgroup.mem_top s))
  obtain ⟨j, rfl⟩ := hs
  rw [map_pow, map_pow, ← heq, pow_right_comm]

/-- If a character kills the kernel of a homomorphism into the complex
units, it is one of the powers of that homomorphism. -/
theorem character_eq_pow_of_ker_le {G : Type*} [Group G] [Finite G]
    (f : G →* ℂˣ) (χ : G →* ℂ) (hker : f.ker ≤ χ.ker) :
    ∃ i < Nat.card f.range, ∀ g, χ g = (f g : ℂ) ^ i := by
  let _ : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hr : f.rangeRestrict.ker ≤ χ.toHomUnits.ker := by
    intro g hg
    change χ.toHomUnits g = 1
    apply Units.ext
    change f.rangeRestrict g = 1 at hg
    exact hker (congrArg (fun w : f.range => (w : ℂˣ)) hg)
  let data : {g : G →* ℂˣ // f.rangeRestrict.ker ≤ g.ker} := ⟨χ.toHomUnits, hr⟩
  let ψ := (Units.coeHom ℂ).comp (f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective data)
  have hψ (g : G) : ψ (f.rangeRestrict g) = χ g := congrArg (fun u : ℂˣ => (u : ℂ))
    (f.rangeRestrict.liftOfRightInverse_comp_apply _
      (Function.rightInverse_surjInv f.rangeRestrict_surjective) data g)
  obtain ⟨i, hi, hpow⟩ := finite_complex_unit_subgroup_character_eq_pow f.range ψ
  exact ⟨i, hi, fun g => (hψ g).symm.trans (hpow (f.rangeRestrict g))⟩

private theorem sum_star_mul_addChar {A : Type*} [AddCommGroup A] [Fintype A]
    (x y : A) [DecidableEq A] :
    (∑ ψ : AddChar A ℂ, star (ψ x) * ψ y) =
      if x = y then (Fintype.card A : ℂ) else 0 := by
  calc
    _ = ∑ ψ : AddChar A ℂ, ψ (y - x) := by
      refine Finset.sum_congr rfl fun ψ _ => ?_
      rw [Complex.star_def, ← ψ.inv_apply_eq_conj, ψ.map_sub_eq_div, div_eq_mul_inv,
        mul_comm]
    _ = _ := by
      rw [AddChar.sum_apply_eq_ite]
      simp [sub_eq_zero, eq_comm]

/-- Orthogonality of two characters, summed over group elements. -/
theorem sum_star_mul_character_eq_ite {A : Type*} [AddCommGroup A] [Fintype A]
    (ψ χ : AddChar A ℂ) :
    (∑ x : A, star (ψ x) * χ x) = if ψ = χ then (Fintype.card A : ℂ) else 0 := by
  have heq (x : A) : star (ψ x) * χ x = (χ - ψ) x := by
    rw [Complex.star_def, ← ψ.inv_apply_eq_conj, AddChar.sub_apply', div_eq_mul_inv, mul_comm]
  simp_rw [heq]
  rw [AddChar.sum_eq_ite]
  simp [sub_eq_zero, eq_comm]

theorem sum_star_character_eq_ite {A : Type*} [AddCommGroup A] [Fintype A]
    (ψ : AddChar A ℂ) :
    (∑ x : A, star (ψ x)) = if ψ = 0 then (Fintype.card A : ℂ) else 0 := by
  simpa only [AddChar.zero_apply, mul_one] using sum_star_mul_character_eq_ite ψ (0 : AddChar A ℂ)

/-- Orthogonality on the nonzero slice of a product with `ZMod 2`. -/
theorem sum_star_character_on_zmodTwo_one {A : Type*} [AddCommGroup A] [Fintype A]
    (χ ψ : AddChar (ZMod 2 × A) ℂ)
    (hχ : ∀ x : ZMod 2 × A, χ x = if x.1 = 0 then 1 else -1) :
    (∑ g : A, star (ψ (1, g))) =
      (if ψ = 0 then (Fintype.card A : ℂ) else 0) -
        (if ψ = χ then (Fintype.card A : ℂ) else 0) := by
  let term (x : ZMod 2 × A) := star (ψ x) * (1 - χ x)
  have hzero (g : A) : term (0, g) = 0 := by simp [term, hχ]
  have hone (g : A) : term (1, g) = 2 * star (ψ (1, g)) := by
    have htwo : (1 : ℂ) - (-1) = 2 := by norm_num
    simp only [term, hχ, ite_eq_right one_ne_zero, htwo]
    exact mul_comm _ _
  have hdouble : (∑ x : ZMod 2 × A, term x) = 2 * ∑ g : A, star (ψ (1, g)) := by
    rw [Fintype.sum_prod_type]
    rw [← (ZMod.finEquiv 2).toEquiv.sum_comp (fun b : ZMod 2 => ∑ g : A, term (b, g))]
    change (∑ b : Fin 2, ∑ g : A, term (ZMod.finEquiv 2 b, g)) = _
    simp only [Fin.sum_univ_two, map_zero, map_one, hzero, hone, Finset.sum_const_zero, zero_add, Finset.mul_sum]
  have hfull : (∑ x : ZMod 2 × A, term x) =
      (if ψ = 0 then (Fintype.card (ZMod 2 × A) : ℂ) else 0) -
        (if ψ = χ then (Fintype.card (ZMod 2 × A) : ℂ) else 0) := by
    simp only [term, mul_sub, mul_one, Finset.sum_sub_distrib, sum_star_character_eq_ite,
      sum_star_mul_character_eq_ite]
  have hcard : (Fintype.card (ZMod 2 × A) : ℂ) = 2 * (Fintype.card A : ℂ) := by
    rw [Fintype.card_prod, ZMod.card, Nat.cast_mul]
    norm_num
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  rw [← hdouble, hfull, hcard]
  simp only [mul_sub, mul_ite, mul_zero]

/-- The finite carrier of an additive subgroup. -/
noncomputable def subgroupElements {A : Type*} [AddCommGroup A] [Fintype A]
    (I : AddSubgroup A) : Finset A := by
  classical
  exact Finset.univ.filter (· ∈ I)

@[simp] theorem mem_subgroupElements {A : Type*} [AddCommGroup A] [Fintype A]
    {I : AddSubgroup A} {x : A} : x ∈ subgroupElements I ↔ x ∈ I := by
  classical
  simp [subgroupElements]

@[simp] theorem subgroupElements_bot {A : Type*} [AddCommGroup A] [Fintype A] :
    subgroupElements (⊥ : AddSubgroup A) = {0} := by
  classical
  ext x
  simp only [mem_subgroupElements, AddSubgroup.mem_bot, Finset.mem_singleton]

noncomputable def characterCosetAverage {A : Type*} [AddCommGroup A] [Fintype A]
    (I : AddSubgroup A) (z : A) (ψ : AddChar A ℂ) : ℂ :=
  ((subgroupElements I).card : ℂ)⁻¹ * ∑ h ∈ subgroupElements I, ψ (z + h)

@[simp] theorem characterCosetAverage_zero {A : Type*} [AddCommGroup A] [Fintype A]
    (I : AddSubgroup A) (z : A) : characterCosetAverage I z 0 = 1 := by
  have hcard : (subgroupElements I).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (mem_subgroupElements.mpr I.zero_mem)
  simp only [characterCosetAverage, AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hcard)

/-- A coset average retains precisely the characters trivial on its subgroup. -/
theorem characterCosetAverage_eq_ite {A : Type*} [AddCommGroup A] [Fintype A]
    (I : AddSubgroup A) (z : A) (ψ : AddChar A ℂ) :
    characterCosetAverage I z ψ = if ∀ u ∈ I, ψ u = 1 then ψ z else 0 := by
  classical
  have hcard : ((subgroupElements I).card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem (mem_subgroupElements.mpr I.zero_mem))
  unfold characterCosetAverage
  simp_rw [ψ.map_add_eq_mul, ← Finset.mul_sum]
  by_cases h : ∀ u ∈ I, ψ u = 1
  · have hsum : (∑ u ∈ subgroupElements I, ψ u) = (subgroupElements I).card := by
      calc
        _ = ∑ _ ∈ subgroupElements I, (1 : ℂ) :=
          Finset.sum_congr rfl fun u hu => h u (mem_subgroupElements.mp hu)
        _ = _ := by simp
    rw [ite_eq_left h, hsum, mul_comm (ψ z), inv_mul_cancel_left₀ hcard]
  · let _ : Fintype I := Fintype.ofFinite I
    let restricted := ψ.compAddMonoidHom I.subtype
    have hne : restricted ≠ 0 := by
      intro heq
      apply h
      intro u hu
      exact congrArg (fun χ : AddChar I ℂ => χ ⟨u, hu⟩) heq
    have hsum : (∑ u ∈ subgroupElements I, ψ u) = 0 := by
      rw [Finset.sum_subtype (subgroupElements I) (fun u => mem_subgroupElements (x := u)) (fun u => ψ u)]
      exact AddChar.sum_eq_zero_iff_ne_zero.mpr hne
    simp [h, hsum]

/-- Fourier inversion for the uniform average on a coset. -/
theorem characterCosetAverage_orthogonality {A : Type*} [AddCommGroup A] [Fintype A]
    (I : AddSubgroup A) (z x : A) :
    (∑ ψ : AddChar A ℂ, star (ψ x) * characterCosetAverage I z ψ) =
      if x - z ∈ I then (Fintype.card A : ℂ) / (subgroupElements I).card else 0 := by
  classical
  let J := subgroupElements I
  have hiff (h : A) : x = z + h ↔ h = x - z := by
    constructor
    · intro heq
      rw [heq]
      abel
    · intro heq
      rw [heq]
      abel
  calc
    _ = ∑ ψ : AddChar A ℂ, (J.card : ℂ)⁻¹ *
        ∑ h ∈ J, star (ψ x) * ψ (z + h) := by
      refine Finset.sum_congr rfl fun ψ _ => ?_
      unfold characterCosetAverage
      rw [mul_left_comm, Finset.mul_sum]
    _ = (J.card : ℂ)⁻¹ * ∑ h ∈ J, ∑ ψ : AddChar A ℂ, star (ψ x) * ψ (z + h) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by
      simp_rw [sum_star_mul_addChar, hiff]
      rw [Finset.sum_ite_eq']
      simp [J, subgroupElements, div_eq_mul_inv, mul_comm]

end Utilities
