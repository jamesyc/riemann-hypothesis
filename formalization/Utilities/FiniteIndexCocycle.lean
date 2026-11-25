module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Abel

@[expose] public section

open scoped BigOperators
open groupCohomology

namespace Utilities

/-- A cocycle that vanishes on a subgroup of invertible finite index is a
coboundary, by averaging it over the left coset space. -/
theorem cocycle_eq_coboundary_of_vanishing_on_finiteIndex
    {R G M : Type*} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (ρ : G →* Module.End R M) (H : Subgroup G) [Finite (G ⧸ H)]
    (f : G → M) (hf : ∀ g h, f (g * h) = ρ g (f h) + f g)
    (hH : ∀ h ∈ H, f h = 0) (hindex : IsUnit (H.index : R)) :
    ∃ m : M, ∀ g, f g = ρ g m - m := by
  classical
  let _ := Fintype.ofFinite (G ⧸ H)
  have hconst (a b : G) (hab : (a : G ⧸ H) = (b : G ⧸ H)) : f a = f b := by
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h := hf a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hH _ hmem, map_zero, zero_add] at h
    exact h.symm
  let F (q : G ⧸ H) := f q.out
  have hF (a : G) : F (a : G ⧸ H) = f a := hconst _ _ (QuotientGroup.out_eq' _)
  have hstep (g : G) (q : G ⧸ H) : F (g • q) = ρ g (F q) + f g := by
    induction q using QuotientGroup.induction_on with | H a =>
    change F (↑(g * a) : G ⧸ H) = ρ g (F (a : G ⧸ H)) + f g
    rw [hF, hF, hf]
  let s := ∑ q : G ⧸ H, F q
  have hsum (g : G) : s = ρ g s + (H.index : R) • f g := by
    calc
      _ = ∑ q : G ⧸ H, F (g • q) := (Equiv.sum_comp (MulAction.toPerm g) F).symm
      _ = ∑ q : G ⧸ H, (ρ g (F q) + f g) := Finset.sum_congr rfl fun q _ => hstep g q
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
          ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, Nat.cast_smul_eq_nsmul]
  obtain ⟨a, ha⟩ := hindex.exists_left_inv
  refine ⟨-(a • s), fun g => ?_⟩
  have hgf : (H.index : R) • f g = s - ρ g s :=
    eq_sub_of_add_eq (by simpa only [add_comm] using (hsum g).symm)
  calc
    f g = a • ((H.index : R) • f g) := by rw [smul_smul, ha, one_smul]
    _ = _ := by rw [hgf, map_neg, map_smul, smul_sub]; abel

theorem cocycle_mem_coboundaries_of_vanishing_on_finiteIndex
    {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)
    (H : Subgroup G) [Finite (G ⧸ H)] (f : G → A)
    (hf : f ∈ cocycles₁ A) (hH : ∀ h ∈ H, f h = 0) (hindex : IsUnit (H.index : R)) :
    f ∈ coboundaries₁ A := by
  obtain ⟨m, hm⟩ := cocycle_eq_coboundary_of_vanishing_on_finiteIndex A.ρ H f
    ((mem_cocycles₁_iff _).mp hf) hH hindex
  exact ⟨m, funext fun g => (hm g).symm⟩

end Utilities
