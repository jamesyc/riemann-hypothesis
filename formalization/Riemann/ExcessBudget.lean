module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace Riemann

/-- Scale-independent names for the counts and weights in §4.3. -/
structure ExcessBudget where
  ambientCount : ℕ
  topCount : ℕ
  thickCount : ℕ
  steps : ℕ
  a : ℝ
  b : ℝ
  k : ℝ

noncomputable def ExcessBudget.thickDensity (d : ExcessBudget) : ℝ :=
  (d.thickCount : ℝ) / d.ambientCount

noncomputable def ExcessBudget.normalization (d : ExcessBudget) : ℝ :=
  (d.topCount : ℝ) * d.steps * d.b * d.thickDensity / 2

noncomputable def ExcessBudget.liftCost (d : ExcessBudget) (x ε : ℝ) : ℝ :=
  2 * (d.ambientCount : ℝ) * d.steps * d.b * x ^ ε

noncomputable def ExcessBudget.congruenceCost (d : ExcessBudget) (x ε : ℝ) : ℝ :=
  (d.thickCount : ℝ) * d.k * d.b * x ^ (2 * ε) / (d.ambientCount : ℝ) ^ 2

/-- The error budget B in equations (4.8) and (18.1). -/
noncomputable def ExcessBudget.total (d : ExcessBudget) (x ε : ℝ) : ℝ :=
  (d.topCount : ℝ) * d.a * (1 + (d.steps : ℝ) ^ 2 / d.k) +
    (d.steps : ℝ) * (d.liftCost x ε + d.congruenceCost x ε)

/-- Positivity and the size hypotheses (4.6) and (4.7). -/
structure ExcessSizeBounds (d : ExcessBudget) (x ε : ℝ) : Prop where
  scale_ge_three : 3 ≤ x
  epsilon_pos : 0 < ε
  ambient_pos : 0 < d.ambientCount
  top_pos : 0 < d.topCount
  thick_pos : 0 < d.thickCount
  steps_pos : 0 < d.steps
  a_pos : 0 < d.a
  b_pos : 0 < d.b
  k_pos : 0 < d.k
  a_le : d.a ≤ 2 * x * d.b
  top_lower : (1 / 2 : ℝ) * x ^ (-ε / 8) * d.ambientCount ≤ d.topCount
  thick_lower : x ^ (-ε) * d.ambientCount ≤ d.thickCount
  thick_upper : d.thickCount ≤ d.ambientCount
  steps_lower : x ^ (1 / 2 - ε) ≤ (d.steps : ℝ)
  steps_upper : (d.steps : ℝ) ≤ x ^ (1 / 2 + ε / 2)
  k_lower : x * d.steps ≤ d.k
  k_upper : d.k ≤ (d.ambientCount : ℝ) ^ 2 * x ^ (1 / 2 - ε)
  slack : 26 ≤ x ^ (3 * ε / 8)

theorem ExcessSizeBounds.normalization_pos {d : ExcessBudget} {x ε : ℝ}
    (h : ExcessSizeBounds d x ε) : 0 < d.normalization := by
  have hn : 0 < (d.ambientCount : ℝ) := by exact_mod_cast h.ambient_pos
  have ht : 0 < (d.topCount : ℝ) := by exact_mod_cast h.top_pos
  have h₂ : 0 < (d.thickCount : ℝ) := by exact_mod_cast h.thick_pos
  have hm : 0 < (d.steps : ℝ) := by exact_mod_cast h.steps_pos
  have hb := h.b_pos
  unfold ExcessBudget.normalization ExcessBudget.thickDensity
  positivity

theorem ExcessSizeBounds.total_nonneg {d : ExcessBudget} {x ε : ℝ}
    (h : ExcessSizeBounds d x ε) : 0 ≤ d.total x ε := by
  have hx : 0 < x := by linarith [h.scale_ge_three]
  have ha := h.a_pos
  have hb := h.b_pos
  have hk := h.k_pos
  unfold ExcessBudget.total ExcessBudget.liftCost ExcessBudget.congruenceCost
  positivity

noncomputable def ExcessBudget.normalizedTerms (d : ExcessBudget) (x ε : ℝ) : ℝ :=
  2 * d.a / (d.steps * d.b * d.thickDensity) * (1 + (d.steps : ℝ) ^ 2 / d.k) +
    4 * d.ambientCount * d.steps * x ^ ε / (d.topCount * d.thickDensity) +
    2 * d.k * x ^ (2 * ε) / (d.ambientCount * (d.topCount : ℝ))

theorem ExcessBudget.total_div_normalization {d : ExcessBudget} {x ε : ℝ}
    (h : ExcessSizeBounds d x ε) :
    d.total x ε / d.normalization = d.normalizedTerms x ε := by
  have hn : (d.ambientCount : ℝ) ≠ 0 := by exact_mod_cast h.ambient_pos.ne'
  have ht : (d.topCount : ℝ) ≠ 0 := by exact_mod_cast h.top_pos.ne'
  have h₂ : (d.thickCount : ℝ) ≠ 0 := by exact_mod_cast h.thick_pos.ne'
  have hm : (d.steps : ℝ) ≠ 0 := by exact_mod_cast h.steps_pos.ne'
  have hb := h.b_pos.ne'
  have hk := h.k_pos.ne'
  unfold ExcessBudget.total ExcessBudget.liftCost ExcessBudget.congruenceCost
    ExcessBudget.normalization ExcessBudget.normalizedTerms ExcessBudget.thickDensity
  field_simp
  ring

/-- The three normalized terms in (4.8) are bounded using (4.6) and (4.7). -/
theorem normalizedExcessBudget_le_intermediate {d : ExcessBudget} {x ε : ℝ}
    (h : ExcessSizeBounds d x ε) :
    d.normalizedTerms x ε ≤ 20 * x ^ (1 / 2 + (21 / 8 : ℝ) * ε) := by
  let n : ℝ := d.ambientCount
  let t : ℝ := d.topCount
  let m : ℝ := d.steps
  let δ := d.thickDensity
  let X := x ^ (1 / 2 + (21 / 8 : ℝ) * ε)
  have hx₁ : 1 ≤ x := by linarith [h.scale_ge_three]
  have hx : 0 < x := zero_lt_one.trans_le hx₁
  have hn : 0 < n := by dsimp [n]; exact_mod_cast h.ambient_pos
  have ht : 0 < t := by dsimp [t]; exact_mod_cast h.top_pos
  have hm : 0 < m := by dsimp [m]; exact_mod_cast h.steps_pos
  have hb := h.b_pos
  have hk := h.k_pos
  have ha := h.a_pos
  have hε := h.epsilon_pos
  have hδ₀ : 0 < δ := by
    have h₂ : 0 < (d.thickCount : ℝ) := by exact_mod_cast h.thick_pos
    exact div_pos h₂ hn
  have hδ : δ⁻¹ ≤ x ^ ε := by
    have hlower : x ^ (-ε) ≤ δ := (le_div_iff₀ hn).mpr h.thick_lower
    calc
      _ ≤ (x ^ (-ε))⁻¹ := (inv_le_inv₀ hδ₀ (Real.rpow_pos_of_pos hx _)).mpr hlower
      _ = _ := by rw [Real.rpow_neg hx.le, inv_inv]
  have hnt : n / t ≤ 2 * x ^ (ε / 8) := by
    apply (div_le_iff₀ ht).mpr
    have hcancel : x ^ (ε / 8) * x ^ (-ε / 8) = 1 := by
      rw [← Real.rpow_add hx, show ε / 8 + -ε / 8 = 0 by ring, Real.rpow_zero]
    calc
      n = (x ^ (ε / 8) * x ^ (-ε / 8)) * n := by rw [hcancel, one_mul]
      _ = (2 * x ^ (ε / 8)) * ((1 / 2 : ℝ) * x ^ (-ε / 8) * n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h.top_lower (by positivity)
  have hmInv : m⁻¹ ≤ x ^ (-(1 / 2 - ε)) := by
    rw [Real.rpow_neg hx.le]
    exact (inv_le_inv₀ hm (Real.rpow_pos_of_pos hx _)).mpr h.steps_lower
  have hmk : m / d.k ≤ x⁻¹ := by
    rw [← one_div]
    exact (div_le_div_iff₀ hk hx).mpr (by simpa only [one_mul, mul_comm m x] using h.k_lower)
  have hExponent (s : ℝ) (hs : s ≤ 1 / 2 + (21 / 8 : ℝ) * ε) : x ^ s ≤ X :=
    Real.rpow_le_rpow_of_exponent_le hx₁ hs
  let slopeFactor := (2 * d.a / d.b) * δ⁻¹
  have hSlope : slopeFactor ≤ 4 * x ^ (1 + ε) := by
    have ha' : 2 * d.a / d.b ≤ 4 * x := by
      apply (div_le_iff₀ hb).mpr
      have hsize := h.a_le
      linarith
    calc
      slopeFactor ≤ (4 * x) * x ^ ε := mul_le_mul ha' hδ (by positivity) (by positivity)
      _ = 4 * (x * x ^ ε) := mul_assoc _ _ _
      _ = _ := congrArg (fun value => 4 * value) (by
        simpa only [Real.rpow_one] using (Real.rpow_add hx 1 ε).symm)
  have hFirst : 2 * d.a / (m * d.b * δ) * (1 + m ^ (2 : ℕ) / d.k) ≤ 8 * X := by
    have hInvTerm : slopeFactor * m⁻¹ ≤ 4 * X := by
      calc
        _ ≤ (4 * x ^ (1 + ε)) * x ^ (-(1 / 2 - ε)) :=
          mul_le_mul hSlope hmInv (by positivity) (by positivity)
        _ = 4 * x ^ (1 / 2 + 2 * ε) := by
          rw [mul_assoc, ← Real.rpow_add hx, show (1 + ε) + -(1 / 2 - ε) = 1 / 2 + 2 * ε by ring]
        _ ≤ 4 * X := mul_le_mul_of_nonneg_left (hExponent _ (by linarith)) (by norm_num)
    have hRatioTerm : slopeFactor * (m / d.k) ≤ 4 * X := by
      calc
        _ ≤ (4 * x ^ (1 + ε)) * x⁻¹ := mul_le_mul hSlope hmk (by positivity) (by positivity)
        _ = 4 * x ^ ε := by
          rw [mul_assoc, ← Real.rpow_neg_one x, ← Real.rpow_add hx,
            show (1 + ε) + -1 = ε by ring]
        _ ≤ 4 * X := mul_le_mul_of_nonneg_left (hExponent _ (by linarith)) (by norm_num)
    calc
      _ = slopeFactor * m⁻¹ + slopeFactor * (m / d.k) := by
        dsimp [slopeFactor]
        field_simp [hm.ne', hb.ne', hδ₀.ne', hk.ne']
      _ ≤ 4 * X + 4 * X := add_le_add hInvTerm hRatioTerm
      _ = _ := by ring
  have hLift : 4 * n * m * x ^ ε / (t * δ) ≤ 8 * X := by
    calc
      _ = 4 * (n / t) * m * x ^ ε * δ⁻¹ := by field_simp [ht.ne', hδ₀.ne']
      _ ≤ 4 * (2 * x ^ (ε / 8)) * x ^ (1 / 2 + ε / 2) * x ^ ε * x ^ ε := by
        have hcount := mul_le_mul_of_nonneg_left hnt (by norm_num : (0 : ℝ) ≤ 4)
        have hsteps := mul_le_mul hcount h.steps_upper hm.le (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_right hsteps (by positivity)) hδ
          (by positivity) (by positivity)
      _ = 8 * (x ^ (ε / 8) * x ^ (1 / 2 + ε / 2) * x ^ ε * x ^ ε) := by ring
      _ = _ := by
        dsimp [X]
        rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx,
          show ε / 8 + (1 / 2 + ε / 2) + ε + ε = 1 / 2 + (21 / 8 : ℝ) * ε by ring]
  have hCongruence : 2 * d.k * x ^ (2 * ε) / (n * t) ≤ 4 * X := by
    have hk' : d.k / n ^ (2 : ℕ) ≤ x ^ (1 / 2 - ε) := by
      apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
      simpa only [mul_comm] using h.k_upper
    calc
      _ = 2 * (d.k / n ^ (2 : ℕ)) * (n / t) * x ^ (2 * ε) := by
        field_simp [hn.ne', ht.ne']
      _ ≤ 2 * x ^ (1 / 2 - ε) * (2 * x ^ (ε / 8)) * x ^ (2 * ε) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hk' (by norm_num))
          hnt (by positivity) (by positivity)) (by positivity)
      _ = 4 * (x ^ (1 / 2 - ε) * x ^ (ε / 8) * x ^ (2 * ε)) := by ring
      _ = 4 * x ^ (1 / 2 + (9 / 8 : ℝ) * ε) := by
        rw [← Real.rpow_add hx, ← Real.rpow_add hx,
          show 1 / 2 - ε + ε / 8 + 2 * ε = 1 / 2 + (9 / 8 : ℝ) * ε by ring]
      _ ≤ 4 * X := mul_le_mul_of_nonneg_left (hExponent _ (by linarith)) (by norm_num)
  change 2 * d.a / (m * d.b * δ) * (1 + m ^ (2 : ℕ) / d.k) +
    4 * n * m * x ^ ε / (t * δ) + 2 * d.k * x ^ (2 * ε) / (n * t) ≤ 20 * X
  linarith

/-- Proposition 4.3, including the final exponent slack. -/
theorem normalizedExcessBudget_le {d : ExcessBudget} {x ε C : ℝ}
    (h : ExcessSizeBounds d x ε) (_hC : 0 ≤ C) :
    x ^ (C * ε) * d.total x ε / d.normalization ≤
      (10 / 13 : ℝ) * x ^ (1 / 2 + (C + 3) * ε) := by
  have hx : 0 < x := by linarith [h.scale_ge_three]
  have hterms := normalizedExcessBudget_le_intermediate h
  rw [← ExcessBudget.total_div_normalization h] at hterms
  have hpow : x ^ (1 / 2 + (21 / 8 : ℝ) * ε) * x ^ (3 * ε / 8) =
      x ^ (1 / 2 + 3 * ε) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hslack : 20 * x ^ (1 / 2 + (21 / 8 : ℝ) * ε) ≤
      (10 / 13 : ℝ) * x ^ (1 / 2 + 3 * ε) := by
    rw [← hpow]
    have hone := mul_le_mul_of_nonneg_left h.slack
      (Real.rpow_nonneg hx.le (1 / 2 + (21 / 8 : ℝ) * ε))
    linarith
  have hfinish : x ^ (C * ε) * x ^ (1 / 2 + 3 * ε) =
      x ^ (1 / 2 + (C + 3) * ε) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [mul_div_assoc, ← hfinish]
  calc
    _ ≤ x ^ (C * ε) * ((10 / 13 : ℝ) * x ^ (1 / 2 + 3 * ε)) :=
      mul_le_mul_of_nonneg_left (hterms.trans hslack) (Real.rpow_nonneg hx.le _)
    _ = _ := by ring

/-- The numerical deduction in Corollary 4.4 from the normalized form of (4.5). -/
theorem combination_le_of_normalizedExcess {d : ExcessBudget} {x ε C : ℝ}
    (h : ExcessSizeBounds d x ε) (hC : 0 ≤ C)
    {main auxiliary correction error edgeError : ℝ}
    (haverage : main - correction - auxiliary ≤ error / d.normalization + edgeError)
    (herror : error ≤ x ^ (C * ε) * d.total x ε)
    (hcorrection : edgeError + correction ≤ (3 / 13 : ℝ) * x ^ (1 / 2 + (C + 3) * ε)) :
    main ≤ x ^ (1 / 2 + (C + 3) * ε) + auxiliary := by
  have hbudget := normalizedExcessBudget_le h hC
  have herror' := div_le_div_of_nonneg_right herror h.normalization_pos.le
  linarith

end Riemann
