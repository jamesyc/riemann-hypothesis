module

public import Utilities.IdealClassPrimeSieve
import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

open Filter Ideal NumberField
open scoped NumberField nonZeroDivisors Topology

namespace Utilities

/-- A family with a positive linear lower count has divergent harmonic sum. -/
theorem not_summable_inv_of_eventually_linear_lower_count {A : Type*}
    (n : A → ℕ) (hn : ∀ a, 0 < n a)
    (hfinite : ∀ x : ℝ, 0 ≤ x → Finite {a : A // (n a : ℝ) ≤ x})
    {D : ℝ} (hD : 0 < D)
    (hlo : ∀ᶠ x : ℝ in atTop, D ≤ (Nat.card {a : A // (n a : ℝ) ≤ x} : ℝ) / x) :
    ¬ Summable (fun a : A => (n a : ℝ)⁻¹) := by
  classical
  intro h
  let f (x : ℝ) (a : A) : ℝ := if (n a : ℝ) ≤ x then x⁻¹ else 0
  have hf (a : A) : Tendsto (fun x : ℝ => f x a) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.congr'
    filter_upwards [eventually_ge_atTop (n a : ℝ)] with x hx
    simp [f, hx]
  have hb : ∀ᶠ x : ℝ in atTop, ∀ a : A, ‖f x a‖ ≤ (n a : ℝ)⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    intro a
    by_cases ha : (n a : ℝ) ≤ x
    · dsimp only [f]
      rw [ite_eq_left ha, Real.norm_of_nonneg (inv_nonneg.mpr hx.le)]
      exact (inv_le_inv₀ hx (Nat.cast_pos.mpr (hn a))).mpr ha
    · simp [f, ha, inv_nonneg]
  have ht : Tendsto (fun x : ℝ => ∑' a : A, f x a) atTop (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence h hf hb
  have hzero : Tendsto (fun x : ℝ => (Nat.card {a : A // (n a : ℝ) ≤ x} : ℝ) / x)
      atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    let S : Set A := {a | (n a : ℝ) ≤ x}
    let _ : Finite S := hfinite x hx
    let _ : Fintype S := Fintype.ofFinite _
    change (∑' a : A, S.indicator (fun _ => x⁻¹) a) = (Nat.card S : ℝ) / x
    rw [← tsum_subtype, tsum_fintype, Nat.card_eq_fintype_card]
    simp [div_eq_mul_inv, nsmul_eq_mul]
  exact hD.not_ge (ge_of_tendsto hzero hlo)

/-- Pairs from any family with a positive linear lower count cannot be
injected into the ideals of a number field preserving the product of norms. -/
theorem not_injective_pair_of_norm_mul_of_eventually_linear_lower_count {A : Type*}
    (n : A → ℕ) (hn : ∀ a, 0 < n a)
    (hfinite : ∀ x : ℝ, 0 ≤ x → Finite {a : A // (n a : ℝ) ≤ x})
    {D : ℝ} (hD : 0 < D)
    (hlo : ∀ᶠ x : ℝ in atTop, D ≤ (Nat.card {a : A // (n a : ℝ) ≤ x} : ℝ) / x)
    (L : Type*) [Field L] [NumberField L] (f : A × A → (Ideal (𝓞 L))⁰)
    (hnorm : ∀ a b : A, absNorm (f (a, b)).val = n a * n b) :
    ¬ Function.Injective f := by
  intro hf
  classical
  obtain ⟨B, _, hbound⟩ := exists_linear_bound_nonzeroIntegralIdealCount L
  apply not_summable_inv_of_eventually_linear_lower_count n hn hfinite hD hlo
  refine summable_of_sum_le (c := B / D) (fun _ => inv_nonneg.mpr (by positivity)) fun T => ?_
  let m (i : T) : ℝ := n i.val
  have hm (i : T) : 0 < m i := Nat.cast_pos.mpr (hn i.val)
  have hscaled (i : T) : ∀ᶠ x : ℝ in atTop,
      D / m i ≤ (Nat.card {a : A // (n a : ℝ) ≤ x / m i} : ℝ) / x := by
    filter_upwards [((tendsto_id.atTop_div_const (hm i)).eventually hlo),
      eventually_gt_atTop (0 : ℝ)] with x hx hx₀
    change D ≤ (Nat.card {a : A // (n a : ℝ) ≤ x / m i} : ℝ) / (x / m i) at hx
    have hh := div_le_div_of_nonneg_right hx (hm i).le
    rwa [div_div, div_mul_cancel₀ _ (hm i).ne'] at hh
  have hlarge : ∀ᶠ x : ℝ in atTop,
      (∑ i : T, (Nat.card {a : A // (n a : ℝ) ≤ x / m i} : ℝ) / x) ≤ B := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx₀ : 0 < x := zero_lt_one.trans_le hx
    let Q (i : T) := {a : A // (n a : ℝ) ≤ x / m i}
    let _ (i : T) : Finite (Q i) := hfinite _ (div_nonneg hx₀.le (hm i).le)
    let U := {J : (Ideal (𝓞 L))⁰ // (absNorm J.val : ℝ) ≤ x}
    let _ : Finite U := finite_nonzeroIntegralIdeals_norm_le L x hx₀.le
    let g (z : Σ i : T, Q i) : U := ⟨f (z.1.val, z.2.val), by
      rw [hnorm, Nat.cast_mul, mul_comm]
      exact (le_div_iff₀ (hm z.1)).mp z.2.property⟩
    have hg : Function.Injective g := by
      intro z z' h
      have hpair := hf (congrArg (fun w : U => w.val) h)
      have he : z.1 = z'.1 := Subtype.ext (congrArg Prod.fst hpair)
      cases z with | mk i j =>
        cases z' with | mk i' j' =>
          change i = i' at he
          subst i'
          exact congrArg (Sigma.mk i) (Subtype.ext (congrArg Prod.snd hpair))
    have hcard := Nat.card_le_card_of_injective g hg
    rw [Nat.card_sigma] at hcard
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hx₀).mpr
    exact (by exact_mod_cast hcard : (∑ i : T, (Nat.card (Q i) : ℝ)) ≤ Nat.card U).trans (hbound x hx)
  obtain ⟨x, hx₁, hx₂⟩ := ((Filter.eventually_all.mpr hscaled).and hlarge).exists
  have hsum : ∑ i : T, D / m i ≤ B :=
    (Finset.sum_le_sum fun i _ => hx₁ i).trans hx₂
  apply (le_div_iff₀ hD).mpr
  calc
    (∑ a ∈ T, (n a : ℝ)⁻¹) * D = ∑ i : T, D / m i := by
      rw [Finset.sum_mul, ← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro i _
      simp [m, div_eq_mul_inv, mul_comm]
    _ ≤ B := hsum

variable (K : Type*) [Field K] [NumberField K]

local notation "I₀" => (Ideal (𝓞 K))⁰

private theorem eventually_ideal_count_lower :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ x : ℝ in atTop,
      D ≤ (Nat.card {I : I₀ // (absNorm I.val : ℝ) ≤ x} : ℝ) / x := by
  have hp := integralIdealCountConstant_pos K
  refine ⟨integralIdealCountConstant K / 2, by positivity, ?_⟩
  exact ((tendsto_card_nonzeroIntegralIdeal_norm_le_div K).eventually
    (Ioi_mem_nhds (show integralIdealCountConstant K / 2 < integralIdealCountConstant K by linarith))).mono
    fun _ h => h.le

/-- The harmonic series over nonzero integral ideals diverges. -/
theorem not_summable_inv_absNorm_nonzeroIntegralIdeals :
    ¬ Summable (fun I : I₀ => (absNorm I.val : ℝ)⁻¹) := by
  obtain ⟨D, hD, hb⟩ := eventually_ideal_count_lower K
  exact not_summable_inv_of_eventually_linear_lower_count (fun I : I₀ => absNorm I.val)
    absNorm_pos_of_nonZeroDivisors (finite_nonzeroIntegralIdeals_norm_le K) hD hb

/-- No injection of pairs of nonzero ideals can send the product of their
norms to the norm of the image in another number field. -/
theorem not_injective_idealPair_of_absNorm_mul
    (L : Type*) [Field L] [NumberField L] (f : I₀ × I₀ → (Ideal (𝓞 L))⁰)
    (hnorm : ∀ I J : I₀, absNorm (f (I, J)).val = absNorm I.val * absNorm J.val) :
    ¬Function.Injective f := by
  obtain ⟨D, hD, hb⟩ := eventually_ideal_count_lower K
  exact not_injective_pair_of_norm_mul_of_eventually_linear_lower_count
    (fun I : I₀ => absNorm I.val) absNorm_pos_of_nonZeroDivisors
    (finite_nonzeroIntegralIdeals_norm_le K) hD hb L f hnorm

end Utilities
