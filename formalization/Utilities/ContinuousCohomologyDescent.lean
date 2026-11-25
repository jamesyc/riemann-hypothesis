module

public import Utilities.ContinuousCocycleTransfer
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Module
import Mathlib.GroupTheory.Coset.Card

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
  (A : DiscreteGaloisModule k G) (H : Subgroup G) [H.Normal] [Finite (G ⧸ H)]

local notation "Q" => G ⧸ H
local notation "p" => QuotientGroup.mk' H
local notation "ρ" => A.rep.ρ

omit [H.Normal] [Finite (G ⧸ H)] in
private theorem card_smul_eq (u : kˣ) (hu : (u : k) = Nat.card Q) [Fintype (G ⧸ H)]
    (x : A.rep) : Fintype.card Q • x = (u : k) • x := by
  rw [← Nat.cast_smul_eq_nsmul k, ← Nat.card_eq_fintype_card, ← hu]

/-- Restriction in degree one detects coboundaries if the subgroup index
is invertible in the coefficient ring. The argument is purely algebraic. -/
theorem exists_coboundary_of_restriction_eq_coboundary
    (hunit : IsUnit (Nat.card Q : k)) (f : cocycles₁ A.rep)
    (h : ∃ a : A.rep, ∀ x : H, f.val x.val = ρ x.val a - a) :
    ∃ a : A.rep, ∀ g : G, f.val g = ρ g a - a := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  let s := Function.surjInv (QuotientGroup.mk'_surjective (N := H))
  have hs : Function.RightInverse s p := Function.rightInverse_surjInv _
  obtain ⟨a, ha⟩ := h
  let z : cocycles₁ A.rep := f - ⟨(d₀₁ A.rep).hom a, d₀₁_apply_mem_cocycles₁ a⟩
  have hz (x : H) : z.val x.val = 0 := by
    change f.val x.val - (ρ x.val a - a) = 0
    rw [ha, sub_self]
  have hzc (g g' : G) : z.val (g * g') = ρ g (z.val g') + z.val g :=
    (mem_cocycles₁_iff _).mp z.property g g'
  let b := ∑ q : Q, z.val (s q)
  let u := hunit.unit
  have hu : (u : k) = Nat.card Q := hunit.unit_spec
  refine ⟨a - ((↑u⁻¹ : k) • b), fun g => ?_⟩
  have hshift (q : Q) : z.val (g * s q) = z.val (s (p g * q)) := by
    let t := cocycleTransferAdjustment H s hs g q
    rw [← representative_mul_cocycleTransferAdjustment H s hs g q]
    rw [hzc, hz t, map_zero, zero_add]
  have hsum : b = ρ g b + (u : k) • z.val g := by
    calc
      b = ∑ q : Q, z.val (s (p g * q)) :=
        (Fintype.sum_equiv (Equiv.mulLeft (p g)) _ _ (fun _ => rfl)).symm
      _ = ∑ q : Q, z.val (g * s q) := Finset.sum_congr rfl fun q _ => (hshift q).symm
      _ = _ := by
        simp_rw [hzc, Finset.sum_add_distrib, ← map_sum, Finset.sum_const, Finset.card_univ]
        exact congrArg (ρ g b + ·) (card_smul_eq A H u hu _)
  have hz_scaled : (u : k) • z.val g = b - ρ g b :=
    eq_sub_of_add_eq (by rw [add_comm, ← hsum])
  have hform : z.val g = (↑u⁻¹ : k) • (b - ρ g b) := by
    rw [← hz_scaled, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  calc
    f.val g = z.val g + (ρ g a - a) := by
      change f.val g = f.val g - (ρ g a - a) + (ρ g a - a)
      abel
    _ = _ := by rw [hform, smul_sub, map_sub, map_smul]; abel

/-- An invariant continuous cohomology class descends when the finite
normal quotient has invertible order. The descended cocycle can be chosen
to restrict to the given representative. -/
theorem exists_continuousCocycle_of_invariant_restriction [IsTopologicalGroup G]
    (hopen : IsOpen (H : Set G)) (hunit : IsUnit (Nat.card Q : k))
    (f : (A.restrictToSubgroup H).continuousCocycles₁)
    (hinv : ∀ g : G, ∃ a : A.rep, ∀ x : H,
      ρ g (f.val (normalSubgroupConjugate H g⁻¹ x)) =
        (show A.rep from f.val x) + (ρ x.val a - a)) :
    ∃ z : A.continuousCocycles₁, ∀ x : H, z.val x.val = f.val x := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  let s := Function.surjInv (QuotientGroup.mk'_surjective (N := H))
  have hs : Function.RightInverse s p := Function.rightInverse_surjInv _
  choose a ha using fun q : Q => hinv (s q)
  let b := ∑ q : Q, a q
  let c := continuousCocycleTransfer A H s hs hopen f
  let u := hunit.unit
  have hu : (u : k) = Nat.card Q := hunit.unit_spec
  let d : A.continuousCocycles₁ :=
    ⟨(d₀₁ A.rep).hom b, d₀₁_apply_mem_cocycles₁ b, (A.discreteOrbit b).comp (· - b)⟩
  refine ⟨(↑u⁻¹ : k) • (c - d), fun x => ?_⟩
  let z : H → A.rep := f.val
  have hc : c.val x.val = (u : k) • z x + (ρ x.val b - b) := by
    calc
      _ = ∑ q : Q, ρ (s q) (z (normalSubgroupConjugate H (s q)⁻¹ x)) :=
        continuousCocycleTransfer_apply_of_mem A H s hs hopen f x
      _ = ∑ q : Q, (z x + (ρ x.val (a q) - a q)) :=
        Finset.sum_congr rfl (fun q _ => ha q x)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Finset.sum_sub_distrib,
          ← map_sum, card_smul_eq A H u hu]
  change (↑u⁻¹ : k) • (c.val x.val - (ρ x.val b - b)) = z x
  rw [hc, add_sub_cancel_right, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- Local triviality on intersections with the normal subgroup detects
local triviality on the original family when the index is invertible. -/
theorem locallyTrivial_of_restriction_locallyTrivial
    (hunit : IsUnit (Nat.card Q : k)) (D : Set (Subgroup G)) (z : A.continuousCocycles₁)
    (hlocal : ∀ J ∈ D, ∃ a : A.rep, ∀ x : H, x.val ∈ J → z.val x.val = ρ x.val a - a) :
    z.val ∈ A.locallyTrivialCocycles₁ D := by
  refine ⟨z.property, fun J hJ => ?_⟩
  let j : J →* Q := (QuotientGroup.mk' H).comp J.subtype
  let e := QuotientGroup.quotientKerEquivRange j
  let _ : Finite (J ⧸ j.ker) := Finite.of_injective e e.injective
  have hdvd : Nat.card (J ⧸ j.ker) ∣ Nat.card Q :=
    (Nat.card_congr e.toEquiv).symm ▸ Subgroup.card_subgroup_dvd_card j.range
  obtain ⟨n, hn⟩ := hdvd
  have hunitJ : IsUnit (Nat.card (J ⧸ j.ker) : k) := by
    apply (IsUnit.mul_iff.mp ?_).1
    show IsUnit ((Nat.card (J ⧸ j.ker) : k) * (n : k))
    rwa [← Nat.cast_mul, ← hn]
  let zJ : cocycles₁ (A.restrictToSubgroup J).rep :=
    ⟨fun g : J => z.val g.val, (A.restrict_mem_continuousCocycles₁ J z.property).1⟩
  obtain ⟨a, ha⟩ := hlocal J hJ
  have haJ (x : j.ker) : (show A.rep from zJ.val x.val) = ρ x.val.val a - a := by
    have hq : p x.val.val = 1 := MonoidHom.mem_ker.mp x.property
    have hx : x.val.val ∈ H := (QuotientGroup.eq_one_iff _).mp hq
    exact ha ⟨x.val.val, hx⟩ x.val.property
  obtain ⟨b, hb⟩ := exists_coboundary_of_restriction_eq_coboundary (A.restrictToSubgroup J)
    j.ker hunitJ zJ ⟨a, haJ⟩
  exact ⟨b, fun g hg => hb ⟨g, hg⟩⟩

/-- The invariant cocycle descent preserves the Selmer local conditions
when the upper restriction family contains the intersections. -/
theorem exists_locallyTrivialCocycle_of_invariant_restriction [IsTopologicalGroup G]
    (hopen : IsOpen (H : Set G)) (hunit : IsUnit (Nat.card Q : k))
    (D : Set (Subgroup G)) (D' : Set (Subgroup H))
    (hD : ∀ J ∈ D, J.comap H.subtype ∈ D')
    (f : (A.restrictToSubgroup H).locallyTrivialCocycles₁ D')
    (hinv : ∀ g : G, ∃ a : A.rep, ∀ x : H,
      ρ g (f.val (normalSubgroupConjugate H g⁻¹ x)) = (show A.rep from f.val x) + (ρ x.val a - a)) :
    ∃ z : A.locallyTrivialCocycles₁ D, ∀ x : H, z.val x.val = f.val x := by
  let f₀ : (A.restrictToSubgroup H).continuousCocycles₁ := ⟨f.val, f.property.1⟩
  obtain ⟨z, hz⟩ := exists_continuousCocycle_of_invariant_restriction A H hopen hunit f₀ hinv
  have hlocal : ∀ J ∈ D, ∃ a : A.rep, ∀ x : H, x.val ∈ J → z.val x.val = ρ x.val a - a := by
    intro J hJ
    obtain ⟨a, ha⟩ := f.property.2 _ (hD J hJ)
    exact ⟨a, fun x hx => (hz x).trans (ha x hx)⟩
  exact ⟨⟨z.val, locallyTrivial_of_restriction_locallyTrivial A H hunit D z hlocal⟩, hz⟩

end Utilities.DiscreteGaloisModule
