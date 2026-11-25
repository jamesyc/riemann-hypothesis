module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Utilities.KummerRadical
import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open scoped BigOperators NumberField
open NumberField

namespace Utilities

/-- The quotient by nth powers of the ordinary units of a number field. -/
abbrev NumberFieldUnitPowerClasses (K : Type*) [Field K] (n : ℕ) :=
  (𝓞 K)ˣ ⧸ (powMonoidHom n : (𝓞 K)ˣ →* (𝓞 K)ˣ).range

/-- Dirichlet's fundamental units contribute at most one `ZMod n` coordinate
per unit rank. The torsion quotient has at most `n` elements. -/
theorem finite_card_numberFieldUnitPowerClasses_le (K : Type*) [Field K] [NumberField K]
    (n : ℕ) [NeZero n] :
    Finite (NumberFieldUnitPowerClasses K n) ∧
      Nat.card (NumberFieldUnitPowerClasses K n) ≤ n ^ (Units.rank K + 1) := by
  let U := (𝓞 K)ˣ
  let T := Units.torsion K
  let P := (powMonoidHom n : U →* U).range
  let Q := (powMonoidHom n : T →* T).range
  have hQP : Q ≤ P.comap T.subtype := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u.val, rfl⟩
  let ι := QuotientGroup.map Q P T.subtype hQP
  let f : (T ⧸ Q) × (Fin (Units.rank K) → ZMod n) → U ⧸ P := fun t =>
    ι t.1 * QuotientGroup.mk (∏ i, Units.fundSystem K i ^ (t.2 i).val)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨⟨t, e⟩, h, _⟩ := Units.exist_unique_eq_mul_prod K u
    let r : Fin (Units.rank K) → ZMod n := fun i => (e i : ZMod n)
    let v : U := ∏ i, Units.fundSystem K i ^ (e i / (n : ℤ))
    have hprod : (∏ i, Units.fundSystem K i ^ e i) =
        (∏ i, Units.fundSystem K i ^ (r i).val) * v ^ n := by
      unfold v
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      rw [← zpow_natCast _ n, ← zpow_mul, ← zpow_natCast, ← zpow_add]
      congr 1
      rw [show ((r i).val : ℤ) = e i % (n : ℤ) from ZMod.val_intCast (e i), mul_comm]
      exact (Int.emod_add_mul_ediv (e i) n).symm
    have hv : (QuotientGroup.mk (v ^ n) : U ⧸ P) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨v, rfl⟩
    refine ⟨(QuotientGroup.mk t, r), ?_⟩
    change ι (QuotientGroup.mk t) * QuotientGroup.mk (∏ i, Units.fundSystem K i ^ (r i).val) =
      QuotientGroup.mk u
    rw [show ι (QuotientGroup.mk t) = QuotientGroup.mk (t : U) from rfl,
      ← QuotientGroup.mk_mul, h, hprod, ← mul_assoc, QuotientGroup.mk_mul P _ (v ^ n), hv]
    exact (mul_one (QuotientGroup.mk ((t : U) * ∏ i, Units.fundSystem K i ^ (r i).val) : U ⧸ P)).symm
  have hT : Nat.card (T ⧸ Q) ≤ n := by
    rw [← Subgroup.index_eq_card, IsCyclic.index_powMonoidHom_range]
    exact Nat.gcd_le_right _ (NeZero.pos n)
  refine ⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans ?_⟩
  rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_succ]
  exact (Nat.mul_le_mul_right _ hT).trans_eq (mul_comm _ _)

/-- In terms of the field degree, the ordinary unit contribution is at most
`n` raised to the degree. -/
theorem finite_card_numberFieldUnitPowerClasses_le_degree (K : Type*) [Field K] [NumberField K]
    (n : ℕ) [NeZero n] :
    Finite (NumberFieldUnitPowerClasses K n) ∧
      Nat.card (NumberFieldUnitPowerClasses K n) ≤ n ^ Module.finrank ℚ K := by
  obtain ⟨hfinite, hcard⟩ := finite_card_numberFieldUnitPowerClasses_le K n
  refine ⟨hfinite, hcard.trans (Nat.pow_le_pow_right (NeZero.pos n) ?_)⟩
  have hcardPos : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  have hdegree := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hplaces := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  unfold Units.rank
  omega

/-- Include ordinary unit classes in the ambient Kummer power classes. -/
def numberFieldUnitPowerClassesToKummer (K : Type*) [Field K] (n : ℕ) :
    NumberFieldUnitPowerClasses K n →* KummerPowerClass K n := by
  let j := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  apply QuotientGroup.map _ _ j
  rintro _ ⟨u, rfl⟩
  exact ⟨j u, (map_pow j u n).symm⟩

/-- A field root of a unit is integral, as is its inverse. Thus the map
from ordinary unit power classes is injective. -/
theorem numberFieldUnitPowerClassesToKummer_injective (K : Type*) [Field K]
    (n : ℕ) [NeZero n] : Function.Injective (numberFieldUnitPowerClassesToKummer K n) := by
  unfold numberFieldUnitPowerClassesToKummer
  apply (QuotientGroup.map_injective_iff _ _ _ _).mpr
  intro u hu
  let j := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  obtain ⟨b, hb⟩ : ∃ b : Kˣ, b ^ n = j u := hu
  have hbval : (b : K) ^ n = algebraMap (𝓞 K) K (u : 𝓞 K) :=
    congrArg (fun x : Kˣ => (x : K)) hb
  have hbinv : ((b⁻¹ : Kˣ) : K) ^ n = algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    have h := congrArg (fun x : Kˣ => ((x⁻¹ : Kˣ) : K)) hb
    rw [← inv_pow, ← map_inv j] at h
    exact h
  let x : 𝓞 K := ⟨(b : K), IsIntegral.of_pow (NeZero.pos n)
    (hbval ▸ RingOfIntegers.isIntegral_coe (u : 𝓞 K))⟩
  let y : 𝓞 K := ⟨((b⁻¹ : Kˣ) : K), IsIntegral.of_pow (NeZero.pos n)
    (hbinv ▸ RingOfIntegers.isIntegral_coe ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))⟩
  let z : (𝓞 K)ˣ := ⟨x, y,
    RingOfIntegers.ext (congrArg (fun a : Kˣ => (a : K)) (mul_inv_cancel b)),
    RingOfIntegers.ext (congrArg (fun a : Kˣ => (a : K)) (inv_mul_cancel b))⟩
  have hz : j z = b := Units.ext rfl
  refine ⟨z, Units.map_injective RingOfIntegers.coe_injective ?_⟩
  change j (z ^ n) = j u
  rwa [map_pow, hz]

/-- The image of the ordinary units in the Kummer power classes is finite
with the same degree bound. -/
theorem finite_card_numberFieldUnitKummerImage_le (K : Type*) [Field K] [NumberField K]
    (n : ℕ) [NeZero n] :
    Finite (numberFieldUnitPowerClassesToKummer K n).range ∧
      Nat.card (numberFieldUnitPowerClassesToKummer K n).range ≤ n ^ Module.finrank ℚ K := by
  obtain ⟨hfinite, hcard⟩ := finite_card_numberFieldUnitPowerClasses_le_degree K n
  let _ := hfinite
  let f := numberFieldUnitPowerClassesToKummer K n
  exact ⟨Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective,
    (Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective).trans hcard⟩

end Utilities
