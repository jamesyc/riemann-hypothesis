module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace Utilities

/-- The exponent in the finite-exception window construction. -/
noncomputable def finiteScaleWindowExponent (R : ℕ) (B : ℝ) : ℝ :=
  (2 : ℝ) ^ (R + 2) * B ^ R

theorem finiteScaleWindowExponent_pos (R : ℕ) {B : ℝ} (hB : 0 < B) :
    0 < finiteScaleWindowExponent R B :=
  mul_pos (pow_pos (by norm_num) _) (pow_pos hB _)

private theorem two_le_finiteScaleWindowExponent (R : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    2 ≤ finiteScaleWindowExponent R B := by
  unfold finiteScaleWindowExponent
  exact (show (2 : ℝ) ≤ 2 ^ (R + 2) from by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ R + 2 by omega)).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hB))

private theorem finiteScaleWindowExponent_succ (R : ℕ) (B : ℝ) :
    finiteScaleWindowExponent (R + 1) B = 2 * B * finiteScaleWindowExponent R B := by
  unfold finiteScaleWindowExponent
  rw [show R + 1 + 2 = (R + 2) + 1 by omega, pow_succ, pow_succ]
  ring

/-- Find a doubling interval disjoint from the forbidden gaps between
`a` and `B * a`, for a finite set of left endpoints. -/
theorem exists_doublingInterval_avoiding (R : ℕ) {B U : ℝ} (T : Finset ℝ)
    (hB : 1 ≤ B) (hU : 0 < U) (hT : T.card ≤ R) :
    ∃ y : ℝ, U / finiteScaleWindowExponent R B ≤ y ∧ 2 * y ≤ U ∧
      ∀ a ∈ T, ∀ u ∈ Set.Icc y (2 * y), a ≤ u → B * a ≤ u := by
  classical
  induction R generalizing U T with
  | zero =>
    have hzero : T = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨U / 2, div_le_div_of_nonneg_left hU.le (by norm_num)
      (two_le_finiteScaleWindowExponent _ hB), by linarith, ?_⟩
    simp [hzero]
  | succ R ih =>
    have hB₀ : 0 < B := zero_lt_one.trans_le hB
    by_cases h : ∃ a ∈ T, U / (2 * B) < a ∧ a ≤ U
    · obtain ⟨a, ha, hlow, _⟩ := h
      have hcard : (T.erase a).card ≤ R := by
        rw [Finset.card_erase_of_mem ha]
        omega
      obtain ⟨y, hy, hupper, havoid⟩ := ih (T.erase a) (by positivity : 0 < U / (2 * B)) hcard
      have hcut : U / (2 * B) ≤ U := div_le_self hU.le (by linarith)
      refine ⟨y, ?_, hupper.trans hcut, ?_⟩
      · rw [finiteScaleWindowExponent_succ, ← div_div]
        exact hy
      · intro a' ha' u hu hau
        by_cases he : a' = a
        · subst a'
          exact False.elim (hlow.not_ge (hau.trans (hu.2.trans hupper)))
        · exact havoid a' (Finset.mem_erase.mpr ⟨he, ha'⟩) u hu hau
    · refine ⟨U / 2, div_le_div_of_nonneg_left hU.le (by norm_num)
        (two_le_finiteScaleWindowExponent _ hB), by linarith, ?_⟩
      intro a ha u hu hau
      have hau' : a ≤ U := hau.trans (hu.2.trans (by linarith))
      have hcut : a ≤ U / (2 * B) := le_of_not_gt (fun hlt => h ⟨a, ha, hlt, hau'⟩)
      calc
        _ ≤ B * (U / (2 * B)) := mul_le_mul_of_nonneg_left hcut hB₀.le
        _ = U / 2 := by field_simp
        _ ≤ _ := hu.1

/-- Every exception below the large cutoff is already below the small one. -/
def GoodFiniteScale (η Ct : ℝ) (exceptions : Finset ℕ) (x : ℝ) : Prop :=
  ∀ a ∈ exceptions, (a : ℝ) ≤ x ^ Ct → (a : ℝ) ≤ x ^ η

/-- A finite list of exceptional integers can be avoided on a common
quadratic window, using the logarithms of the two cutoffs. -/
theorem exists_quadraticWindow_goodFiniteScale (R : ℕ) {η Ct X : ℝ}
    (exceptions : Finset ℕ) (hη : 0 < η) (hCt : η ≤ Ct) (hX : 1 < X)
    (hcard : exceptions.card ≤ R) :
    ∃ Y : ℝ, 0 < Y ∧ X ^ (1 / finiteScaleWindowExponent R (Ct / η)) ≤ Y ∧
      Y ^ (2 : ℕ) ≤ X ∧
      ∀ x ∈ Set.Icc Y (Y ^ (2 : ℕ)), GoodFiniteScale η Ct exceptions x := by
  classical
  have hCt₀ := hη.trans_le hCt
  have hX₀ : 0 < X := zero_lt_one.trans hX
  let T := exceptions.image fun a : ℕ => Real.log (a : ℝ) / Ct
  obtain ⟨y, hy, hupper, hav⟩ := exists_doublingInterval_avoiding (B := Ct / η) R T
    ((one_le_div hη).mpr hCt) (Real.log_pos hX) (Finset.card_image_le.trans hcard)
  have hsq : Real.exp y ^ (2 : ℕ) = Real.exp (2 * y) := by
    rw [← Real.exp_nat_mul]
    norm_num
  refine ⟨Real.exp y, Real.exp_pos _, ?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hX₀, Real.exp_le_exp, mul_one_div]
    exact hy
  · rw [hsq]
    exact (Real.le_log_iff_exp_le hX₀).mp hupper
  · intro x hx a ha hax
    have hx₀ := (Real.exp_pos y).trans_le hx.1
    rcases a.eq_zero_or_pos with rfl | ha₀
    · simpa using (Real.rpow_nonneg hx₀.le η)
    have ha₀' : (0 : ℝ) < a := by exact_mod_cast ha₀
    have hxu : Real.log x ≤ 2 * y := by
      rw [Real.log_le_iff_le_exp hx₀, ← hsq]
      exact hx.2
    have halog : Real.log (a : ℝ) / Ct ≤ Real.log x := by
      rw [div_le_iff₀ hCt₀, mul_comm, ← Real.log_rpow hx₀]
      exact Real.log_le_log ha₀' hax
    have hg := hav _ (Finset.mem_image_of_mem _ ha) (Real.log x)
      ⟨(Real.le_log_iff_exp_le hx₀).mpr hx.1, hxu⟩ halog
    have hcmp : Ct / η * (Real.log (a : ℝ) / Ct) = Real.log (a : ℝ) / η := by
      field_simp
    rw [hcmp, div_le_iff₀ hη] at hg
    rw [Real.rpow_def_of_pos hx₀, ← Real.log_le_iff_le_exp ha₀']
    exact hg

end Utilities
