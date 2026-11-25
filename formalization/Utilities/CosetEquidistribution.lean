module

public import Utilities.FiniteFourier
public import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Card

@[expose] public section

open scoped BigOperators Classical

namespace Utilities

/-- The neutral coset carries target weight `4c`, and all other cosets carry
target weight `3c`, with the same available error in each count. -/
def HasCosetEquidistribution {A Q : Type*} [Zero Q] (T : Finset A) (f : A → Q)
    (c E : ℝ) : Prop := by
  classical
  exact ∀ q : Q, |((T.filter (fun t => f t = q)).card : ℝ) -
    (3 * c + if q = 0 then c else 0) * T.card| ≤ E

/-- A finite set with prescribed fiber counts exists whenever each count
fits in its ambient fiber. -/
theorem exists_finset_with_fiber_counts {A Q : Type*} [Fintype A] [Fintype Q]
    (f : A → Q) (count : Q → ℕ)
    (hcount : ∀ q, count q ≤ (Finset.univ.filter fun a => f a = q).card) :
    ∃ T : Finset A, T.card = ∑ q : Q, count q ∧
      ∀ q, (T.filter fun a => f a = q).card = count q := by
  classical
  choose S hsub hcard using fun q => Finset.exists_subset_card_eq (hcount q)
  let T := Finset.univ.biUnion S
  have hfiber (q : Q) : T.filter (fun a => f a = q) = S q := by
    ext a
    constructor
    · intro ha
      obtain ⟨hT, hq⟩ := Finset.mem_filter.mp ha
      obtain ⟨r, _, har⟩ := Finset.mem_biUnion.mp hT
      have hr := (Finset.mem_filter.mp (hsub r har)).2
      exact (hr.symm.trans hq) ▸ har
    · intro ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, ha⟩,
        (Finset.mem_filter.mp (hsub q ha)).2⟩
  refine ⟨T, ?_, fun q => (congrArg Finset.card (hfiber q)).trans (hcard q)⟩
  calc
    _ = ∑ q : Q, (T.filter fun a => f a = q).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ = _ := Finset.sum_congr rfl fun q _ => (congrArg Finset.card (hfiber q)).trans (hcard q)

/-- Choose a set with exact coset shares in the ratio `4 : 3 : … : 3`.
The capacity condition ensures that the larger share fits in the neutral coset. -/
theorem exists_exactCosetShares {H : Type*} [AddGroup H] [Fintype H]
    (A : AddSubgroup H) [A.Normal] (k : ℕ) (hk : 4 * k ≤ Nat.card A) :
    ∃ T : Finset H, T.card = (3 * A.index + 1) * k ∧
      HasCosetEquidistribution T (QuotientAddGroup.mk' A) ((3 * (A.index : ℝ) + 1)⁻¹) 0 := by
  classical
  let f := QuotientAddGroup.mk' A
  let : Fintype (H ⧸ A) := Fintype.ofFinite _
  let m (q : H ⧸ A) := 3 * k + if q = 0 then k else 0
  have hcap (q : H ⧸ A) : (Finset.univ.filter fun a => f a = q).card = Nat.card A := by
    let : Fintype {a : H // f a = q} := Fintype.ofFinite _
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    change Nat.card (f ⁻¹' {q}) = _
    have h := Nat.card_congr (f.fiberEquivKerOfSurjective QuotientAddGroup.mk_surjective q)
    change Nat.card (f ⁻¹' {q}) = Nat.card (QuotientAddGroup.mk' A).ker at h
    rwa [QuotientAddGroup.ker_mk'] at h
  obtain ⟨T, hcard, hT⟩ := exists_finset_with_fiber_counts f m (fun q => by
    calc
      m q ≤ Nat.card A := by dsimp only [m]; split_ifs <;> omega
      _ = _ := by
        convert (hcap q).symm using 1
        exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _))
  have hindex : Fintype.card (H ⧸ A) = A.index := by
    rw [← Nat.card_eq_fintype_card, AddSubgroup.index_eq_card]
  have hcard' : T.card = (3 * A.index + 1) * k := by
    rw [hcard]
    simp [m, Finset.sum_add_distrib, hindex]
    ring
  refine ⟨T, hcard', fun q => ?_⟩
  have hT' :
      (@Finset.filter H (fun t => (QuotientAddGroup.mk' A) t = q)
        (fun _ => Classical.propDecidable _) T).card = m q := by
    convert hT q using 1
  rw [hT', hcard']
  have hden : 3 * (A.index : ℝ) + 1 ≠ 0 := by positivity
  by_cases hq : q = 0 <;> simp [m, hq, Nat.cast_mul, Nat.cast_add]
  all_goals field_simp [hden]; ring

/-- When one fiber has relative weight `4c` and all the others have
weight `3c`, a nontrivial character of the quotient has mean `c`,
up to the sum of the individual fiber errors. -/
theorem norm_sum_character_sub_expected_le
    {A Q : Type*} [AddGroup Q] [Fintype Q] (f : A → Q)
    (χ : AddChar Q ℂ) (hχ : χ ≠ 0) (T : Finset A) (c E : ℝ)
    (hcount : HasCosetEquidistribution T f c E) :
    ‖(∑ t ∈ T, χ (f t)) - ((c * T.card : ℝ) : ℂ)‖ ≤ (Fintype.card Q : ℝ) * E := by
  classical
  let N (q : Q) := (T.filter (fun t => f t = q)).card
  let w (q : Q) : ℝ := 3 * c + if q = 0 then c else 0
  have hfib :
      (∑ t ∈ T, χ (f t)) = ∑ q : Q, (N q : ℂ) * χ q := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset Q))
      (g := f) (fun _ _ => Finset.mem_univ _) (fun t => χ (f t))]
    apply Finset.sum_congr rfl
    intro q _
    calc
      _ = ∑ _t ∈ T.filter (fun t => f t = q), χ q := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [(Finset.mem_filter.mp ht).2]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsum : (∑ q : Q, χ q) = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hχ
  have hweight :
      (∑ q : Q, (w q : ℂ) * χ q) = (c : ℂ) := by
    have hsplit (q : Q) :
        (w q : ℂ) * χ q = (3 * c : ℝ) * χ q + if q = 0 then (c : ℂ) else 0 := by
      by_cases hq : q = 0
      · subst q
        simp [w, χ.map_zero_eq_one, Complex.ofReal_add]
      · simp [w, hq]
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_add]
  have hmain :
      (∑ q : Q, ((w q * T.card : ℝ) : ℂ) * χ q) = ((c * T.card : ℝ) : ℂ) := by
    push_cast
    rw [← hweight]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hfib, ← hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q : Q, ‖(N q : ℂ) * χ q - ((w q * T.card : ℝ) : ℂ) * χ q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _q : Q, E := by
      apply Finset.sum_le_sum
      intro q _
      rw [← sub_mul, norm_mul, χ.norm_apply, mul_one, ← Complex.ofReal_natCast,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hcount q
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Utilities
