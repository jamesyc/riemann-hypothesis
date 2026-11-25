module

public import Riemann.ChainParameters
public import Riemann.ChainRecord
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter

namespace Riemann

/-- The chosen horizontal rank absorbs the large factor from the frame
normalization in Theorem 15.26. -/
theorem eventually_chainRank_frameLog_le {ε CΓ : ℝ} (hε : 0 < ε) (hCΓ : 0 ≤ CΓ) :
    ∀ᶠ x : ℝ in atTop, ∀ {m k : ℕ}, ChainRankBounds x ε m k →
      ∀ f : ℕ, Real.log (Real.exp (CΓ * (m : ℝ) ^ 5 * f * x ^ ε)) ≤ (f : ℝ) * k := by
  have hgap : 0 < 2 + 9 * ε := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hgap).eventually_ge_atTop (32 * CΓ)] with x hx hlarge m k hrank f
  have hx' : 0 < x := by positivity
  have hm : (m : ℝ) ≤ 2 * x ^ (1 / 2 : ℝ) := hrank.steps_upper.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by norm_num))
  have hprod : CΓ * (m : ℝ) ^ 5 * x ^ ε ≤ (k : ℝ) := by
    calc
      _ ≤ CΓ * (2 * x ^ (1 / 2 : ℝ)) ^ (5 : ℕ) * x ^ ε := by gcongr
      _ = (32 * CΓ) * x ^ (5 / 2 + ε) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hx'.le]
        norm_num
        rw [show CΓ * (32 * x ^ ((5 / 2 : ℝ))) * x ^ ε =
            (32 * CΓ) * (x ^ ((5 / 2 : ℝ)) * x ^ ε) by ring,
          ← Real.rpow_add hx']
      _ ≤ x ^ (2 + 9 * ε) * x ^ (5 / 2 + ε) := by gcongr
      _ = x ^ (9 / 2 + 10 * ε) := by rw [← Real.rpow_add hx']; congr 1; ring
      _ ≤ _ := hrank.rank_lower
  rw [Real.log_exp, show CΓ * (m : ℝ) ^ 5 * f * x ^ ε =
    (f : ℝ) * (CΓ * (m : ℝ) ^ 5 * x ^ ε) by ring]
  exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg f)

/-- The logarithmic placement of an auxiliary level once a prime in the
short interval of Remark 15.27 has been supplied. The dimension ratio
`D / d` is the one in Definition 15.22. -/
theorem chainLevel_log_bounds {F D d Γ T : ℝ}
    (hF : 0 < F) (hD : 0 < D) (hd : 0 < d) (hΓ : 0 < Γ)
    (hlogΓ : Real.log Γ ≤ F)
    (hT : (D / d) ^ F⁻¹ * Γ ^ (-2 / F) ≤ T)
    (hT' : T ≤ (1 + F⁻¹) * ((D / d) ^ F⁻¹ * Γ ^ (-2 / F))) :
    (Real.log D - Real.log d) / F - 2 ≤ Real.log T ∧
      0 ≤ Real.log T - (Real.log D - Real.log d - 2 * Real.log Γ) / F ∧
      Real.log T - (Real.log D - Real.log d - 2 * Real.log Γ) / F ≤ F⁻¹ := by
  have hX : 0 < (D / d) ^ F⁻¹ * Γ ^ (-2 / F) :=
    mul_pos (Real.rpow_pos_of_pos (div_pos hD hd) _) (Real.rpow_pos_of_pos hΓ _)
  have htpos : 0 < T := hX.trans_le hT
  have heq : Real.log ((D / d) ^ F⁻¹ * Γ ^ (-2 / F)) =
      (Real.log D - Real.log d - 2 * Real.log Γ) / F := by
    rw [Real.log_mul (Real.rpow_pos_of_pos (div_pos hD hd) _).ne' (Real.rpow_pos_of_pos hΓ _).ne',
      Real.log_rpow (div_pos hD hd), Real.log_rpow hΓ, Real.log_div hD.ne' hd.ne']
    field_simp
    ring
  have hlo := Real.log_le_log hX hT
  have hhi := Real.log_le_log htpos hT'
  rw [heq] at hlo
  rw [Real.log_mul (by positivity) hX.ne', heq] at hhi
  have hcap : Real.log (1 + F⁻¹) ≤ F⁻¹ := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + F⁻¹)]
  have hpen : 2 * Real.log Γ / F ≤ 2 :=
    (div_le_iff₀ hF).mpr (by linarith)
  refine ⟨?_, by linarith, by linarith⟩
  rw [sub_div] at hlo
  linarith

/-- For the common target dimension and frame normalization, variations
between the short level intervals come only from their source dimensions
and the interval width. -/
theorem chainLevel_log_variation {F D d₁ d₂ Γ T₁ T₂ : ℝ}
    (hF : 0 < F) (hD : 0 < D) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hΓ : 0 < Γ) (hlogΓ : Real.log Γ ≤ F)
    (h₁ : (D / d₁) ^ F⁻¹ * Γ ^ (-2 / F) ≤ T₁)
    (h₁' : T₁ ≤ (1 + F⁻¹) * ((D / d₁) ^ F⁻¹ * Γ ^ (-2 / F)))
    (h₂ : (D / d₂) ^ F⁻¹ * Γ ^ (-2 / F) ≤ T₂)
    (h₂' : T₂ ≤ (1 + F⁻¹) * ((D / d₂) ^ F⁻¹ * Γ ^ (-2 / F))) :
    |Real.log T₁ - Real.log T₂| ≤ |Real.log d₁ - Real.log d₂| / F + F⁻¹ := by
  obtain ⟨_, hlo₁, hhi₁⟩ := chainLevel_log_bounds hF hD hd₁ hΓ hlogΓ h₁ h₁'
  obtain ⟨_, hlo₂, hhi₂⟩ := chainLevel_log_bounds hF hD hd₂ hΓ hlogΓ h₂ h₂'
  have habs₁ := le_abs_self (Real.log d₁ - Real.log d₂)
  have habs₂ := neg_abs_le (Real.log d₁ - Real.log d₂)
  have habs₁' := div_le_div_of_nonneg_right habs₁ hF.le
  have habs₂' := div_le_div_of_nonneg_right habs₂ hF.le
  rw [neg_div] at habs₂'
  apply abs_le.mpr
  constructor <;> linarith only [hlo₁, hhi₁, hlo₂, hhi₂, habs₁', habs₂',
    show (Real.log D - Real.log d₁ - 2 * Real.log Γ) / F -
        (Real.log D - Real.log d₂ - 2 * Real.log Γ) / F =
        -((Real.log d₁ - Real.log d₂) / F) by ring]

/-- Convert the dimension budget in Proposition 15.25 and the placement of
an auxiliary level in Remark 15.27 into the lower half of (K7). -/
theorem chainRecord_logPrime_lower_of_dimensionBudget
    {U : Type*} {p : ChainInputs} {c : ChainConstants}
    (r : ChainRecord U p.budget.steps) (u : U) {F D d Γ C₆ : ℝ}
    (hF : 0 < F) (hD : 0 < D) (hd : 0 < d) (hΓ : 0 < Γ)
    (hlogΓ : Real.log Γ ≤ F)
    (hC₆ : 0 ≤ C₆) (hc : C₆ + 2 ≤ c.scaleConstant)
    (hk : 0 < p.budget.k) (hy : 1 ≤ p.scalePower) (hlogSize : p.scalePower ≤ p.logSize)
    (hdim : p.nodeLogSum + (p.budget.steps : ℝ) * p.localLog -
        C₆ * p.scalePower * (1 + (p.budget.steps : ℝ) ^ 2 / p.budget.k) ≤
        (Real.log D - Real.log d) / F)
    (hT : (D / d) ^ F⁻¹ * Γ ^ (-2 / F) ≤ (r.auxiliaryPrime u : ℝ))
    (hT' : (r.auxiliaryPrime u : ℝ) ≤ (1 + F⁻¹) * ((D / d) ^ F⁻¹ * Γ ^ (-2 / F))) :
    p.nodeLogSum + (p.budget.steps : ℝ) * p.localLog - (p.errors c r.indices.card).e6 ≤
      r.logPrime u := by
  obtain ⟨hlower, -, -⟩ := chainLevel_log_bounds hF hD hd hΓ hlogΓ hT hT'
  let q := 1 + (p.budget.steps : ℝ) ^ 2 / p.budget.k
  have hq : 1 ≤ q := le_add_of_nonneg_right (by positivity)
  have hq' : 0 ≤ q := by linarith
  have hnonneg : 0 ≤ p.logSize := by linarith
  have hprod : 1 ≤ p.logSize * q := one_le_mul_of_one_le_of_one_le (hy.trans hlogSize) hq
  have herror : C₆ * p.scalePower * q + 2 ≤ c.scaleConstant * p.logSize * q := by
    calc
      _ ≤ C₆ * p.logSize * q + 2 * (p.logSize * q) := by
        gcongr
        linarith
      _ = (C₆ + 2) * p.logSize * q := by ring
      _ ≤ _ := by gcongr
  dsimp only [ChainInputs.errors, ChainRecord.logPrime]
  change p.nodeLogSum + (p.budget.steps : ℝ) * p.localLog -
    c.scaleConstant * p.logSize * q ≤ Real.log (r.auxiliaryPrime u : ℝ)
  linarith

end Riemann
