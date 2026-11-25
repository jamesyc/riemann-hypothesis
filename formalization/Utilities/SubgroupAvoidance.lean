module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

namespace Utilities

private theorem exists_mem_not_mem_two_subgroups {G : Type*} [Group G]
    (H A B : Subgroup G) (hA : ¬ H ≤ A) (hB : ¬ H ≤ B) :
    ∃ g ∈ H, g ∉ A ∧ g ∉ B := by
  classical
  by_contra h
  have hcover : (H : Set G) ⊆ (A : Set G) ∪ (B : Set G) := by
    intro g hg
    by_cases ha : g ∈ A
    · exact Or.inl ha
    · exact Or.inr (not_not.mp (fun hb => h ⟨g, hg, ha, hb⟩))
  exact ((SubgroupClass.subset_union.mp hcover).elim hA hB)

/-- Three subgroup exclusions can be satisfied simultaneously if each
is proper on the chosen subgroup and odd powers land in one exclusion. -/
theorem exists_mem_not_mem_three_subgroups_of_odd_pow {G : Type*} [Group G]
    (H A B C : Subgroup G) (hA : ¬ H ≤ A) (hB : ¬ H ≤ B) (hC : ¬ H ≤ C)
    {m : ℕ} (hm : Odd m) (hpow : ∀ x ∈ H, x ^ m ∈ B) :
    ∃ x ∈ H, x ∉ A ∧ x ∉ B ∧ x ∉ C := by
  classical
  obtain ⟨x, hx, hxB, hxC⟩ := exists_mem_not_mem_two_subgroups H B C hB hC
  by_cases hxA : x ∈ A
  · obtain ⟨y, hy, hyA, hyC⟩ := exists_mem_not_mem_two_subgroups H A C hA hC
    by_cases hyB : y ∈ B
    · by_cases hxyC : x * y ∈ C
      · have hx₂B : x ^ 2 ∉ B := by
          intro h
          obtain ⟨k, rfl⟩ := hm
          have hk := hpow x hx
          rw [pow_succ, pow_mul] at hk
          exact hxB ((B.mul_mem_cancel_left (B.pow_mem h k)).mp hk)
        have hxy₂C : x ^ 2 * y ∉ C := by
          rw [sq, mul_assoc, C.mul_mem_cancel_right hxyC]
          exact hxC
        exact ⟨x ^ 2 * y, H.mul_mem (H.pow_mem hx _) hy,
          fun h => hyA ((A.mul_mem_cancel_left (A.pow_mem hxA _)).mp h),
          fun h => hx₂B ((B.mul_mem_cancel_right hyB).mp h), hxy₂C⟩
      · exact ⟨x * y, H.mul_mem hx hy, fun h => hyA ((A.mul_mem_cancel_left hxA).mp h),
          fun h => hxB ((B.mul_mem_cancel_right hyB).mp h), hxyC⟩
    · exact ⟨y, hy, hyA, hyB, hyC⟩
  · exact ⟨x, hx, hxA, hxB, hxC⟩

end Utilities
