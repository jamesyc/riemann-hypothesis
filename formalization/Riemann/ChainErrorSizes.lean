module

public import Riemann.ChainRecord
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter
open scoped Topology

namespace Riemann

theorem ExcessSizeBounds.steps_le_scale {d : ExcessBudget} {x ε : ℝ}
    (h : ExcessSizeBounds d x ε) (hε : ε ≤ 1) : (d.steps : ℝ) ≤ x := by
  refine h.steps_upper.trans ?_
  simpa using Real.rpow_le_rpow_of_exponent_le (by linarith [h.scale_ge_three] : 1 ≤ x)
    (show 1 / 2 + ε / 2 ≤ (1 : ℝ) by linarith)

/-- Lemma 18.15, with the arithmetic estimate on the root discriminant
supplied by the host. The threshold is uniform in the translation and in
the record's index set. -/
theorem eventually_chainErrorSizes {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52)
    {c : ChainConstants} (hc : c.Valid) :
    ∀ᶠ x : ℝ in atTop, ∀ (p : ChainInputs) (N : ℕ),
      p.x = x → p.ε = ε → ExcessSizeBounds p.budget x ε →
      p.budget.b = Real.exp (x ^ ε) → p.budget.a = x * p.budget.b →
      p.thinCutoff = Real.exp (x ^ (ε / 3)) → p.thinScale = p.budget.a / p.thinCutoff →
      (p.budget.ambientCount : ℝ) ≤ 2 * x ^ (2 + 8 * ε) →
      1 ≤ p.rootDiscriminant → Real.log p.rootDiscriminant ≤ x ^ ε / 2 →
      0 ≤ p.topMass → p.topMass ≤ 2 * p.budget.topCount * p.budget.a →
      0 < N → (N : ℝ) ≤ 2 ^ (p.budget.k - 3) → ChainErrorSizes p c N := by
  have hgap : 0 < 1 / 2 - 15 * ε := by linarith
  have hlogs := (isLittleO_log_rpow_atTop (show 0 < ε / 3 by positivity)).bound
    (show (0 : ℝ) < 1 / 12 by norm_num)
  have hthird : 0 < ε - ε / 3 := by linarith
  filter_upwards [hlogs, (tendsto_rpow_atTop hthird).eventually_ge_atTop 2, (tendsto_rpow_atTop hgap).eventually_ge_atTop 4,
    (tendsto_rpow_atTop hε).eventually_ge_atTop
      (260 * (1 + c.heightExponent) * c.scaleConstant ^ 2)] with
    x hlog hthirdx hgapx hthreshold
  intro p N hpx hpε h hb ha hcut hthin hn hrd hrdlog hmass hmass' hN hcount
  have hx : 1 ≤ x := by linarith [h.scale_ge_three]
  have hx' : 0 < x := by positivity
  have hy : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hlog₀ : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog₁ : Real.log x ≤ x ^ (ε / 3) / 12 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog₀,
      abs_of_nonneg (Real.rpow_nonneg hx'.le _), div_eq_mul_inv, mul_comm] using hlog
  have hpow : x ^ (ε / 3) ≤ x ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hpow₂ : 2 * x ^ (ε / 3) ≤ x ^ ε := by
    calc
      _ ≤ x ^ (ε - ε / 3) * x ^ (ε / 3) := by gcongr
      _ = _ := by rw [← Real.rpow_add hx', sub_add_cancel]
  have hlogy : Real.log x ≤ x ^ ε := by linarith
  have hb₁ : 1 ≤ p.budget.b := hb ▸ Real.one_le_exp (by positivity)
  have hba : p.budget.b ≤ p.budget.a := by rw [ha]; nlinarith
  have hm : (p.budget.steps : ℝ) ≤ x := h.steps_le_scale (by linarith)
  have hk₅ : p.budget.k ≤ x ^ (5 : ℕ) := by
    calc
      p.budget.k ≤ (p.budget.ambientCount : ℝ) ^ 2 * x ^ (1 / 2 - ε) := h.k_upper
      _ ≤ (2 * x ^ (2 + 8 * ε)) ^ 2 * x ^ (1 / 2 - ε) := by gcongr
      _ = 4 * x ^ (9 / 2 + 15 * ε) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hx'.le, mul_assoc,
          ← Real.rpow_add hx' ((2 + 8 * ε) * (2 : ℕ)) (1 / 2 - ε),
          show (2 + 8 * ε) * ((2 : ℕ) : ℝ) + (1 / 2 - ε) = 9 / 2 + 15 * ε by push_cast; ring]
        norm_num
      _ ≤ x ^ (5 : ℕ) := by
        calc
          _ ≤ x ^ (1 / 2 - 15 * ε) * x ^ (9 / 2 + 15 * ε) := by gcongr
          _ = _ := by
            rw [← Real.rpow_add hx', show 1 / 2 - 15 * ε + (9 / 2 + 15 * ε) =
              (5 : ℝ) by ring]
            exact Real.rpow_natCast x 5
  have hklog : Real.log p.budget.k ≤ 5 * Real.log x := by
    simpa [Real.log_pow] using Real.log_le_log h.k_pos hk₅
  have hkcut : p.budget.k ≤ p.thinCutoff := by
    rw [hcut, ← Real.exp_log h.k_pos]
    exact Real.exp_le_exp.mpr (by linarith)
  have hcutb : p.thinCutoff ≤ p.budget.b := by rw [hcut, hb]; exact Real.exp_le_exp.mpr hpow
  have hcutpos : 0 < p.thinCutoff := hcut ▸ Real.exp_pos _
  have hnb : (p.budget.ambientCount : ℝ) * p.thinCutoff ≤ p.budget.b := by
    refine (mul_le_mul_of_nonneg_right hn hcutpos.le).trans ?_
    rw [hcut, hb, ← Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hx', ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog2 : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) (by linarith [h.scale_ge_three])
    have hexp : (2 + 8 * ε) * Real.log x ≤ 3 * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith) hlog₀
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log x)]
    linarith
  have hheight : Real.log (1 + x ^ c.heightExponent) ≤ (1 + c.heightExponent) * x ^ ε := by
    have hH : 1 ≤ x ^ c.heightExponent := Real.one_le_rpow hx hc.height_nonneg
    calc
      _ ≤ Real.log (2 * x ^ c.heightExponent) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + c.heightExponent * Real.log x := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx' _).ne', Real.log_rpow hx']
      _ ≤ _ := by
        have hlog2 : Real.log 2 ≤ Real.log x :=
          Real.log_le_log (by norm_num) (by linarith [h.scale_ge_three])
        nlinarith [mul_le_mul_of_nonneg_left hlogy hc.height_nonneg]
  have hcountlog : Real.log (N : ℝ) ≤ p.budget.k := by
    have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
    have hk₃ : 3 ≤ p.budget.k := by
      have hm₁ : (1 : ℝ) ≤ p.budget.steps := by exact_mod_cast h.steps_pos
      exact (h.scale_ge_three.trans (by simpa using mul_le_mul_of_nonneg_left hm₁ hx'.le)).trans h.k_lower
    calc
      _ ≤ Real.log (2 ^ (p.budget.k - 3)) := Real.log_le_log hN' hcount
      _ = (p.budget.k - 3) * Real.log 2 := Real.log_rpow (by norm_num) _
      _ ≤ p.budget.k - 3 := by
        have hlog2 : Real.log 2 ≤ 1 := by
          linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)]
        simpa using mul_le_mul_of_nonneg_left hlog2 (sub_nonneg.mpr hk₃)
      _ ≤ _ := by linarith
  refine ⟨hpx ▸ hpε ▸ h, ?_, ?_, hb₁, hba, hpx.symm ▸ hm, ?_, hpx.symm ▸ hk₅,
    hkcut.trans (hcutb.trans hba), ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmass, hmass', hcountlog, ?_⟩
  · rw [hthin]; positivity [h.a_pos]
  · unfold ChainInputs.scaledCutoff
    rw [hpx]
    positivity
  · rw [ha]; gcongr
  · rw [hthin, ← mul_div_assoc, div_le_iff₀ hcutpos, mul_comm p.budget.a]
    exact mul_le_mul_of_nonneg_right hkcut h.a_pos.le
  · unfold ChainInputs.scaledCutoff
    rw [hpx, ha, mul_assoc]
    gcongr
  · apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le (hb₁.trans hba) hrd
  · unfold ChainInputs.logSize ChainInputs.scalePower
    rw [hpx, hpε, ha, Real.log_mul (by positivity [h.b_pos]) (by linarith),
      Real.log_mul hx'.ne' (by positivity [h.b_pos]), hb, Real.log_exp]
    linarith
  · simpa [ChainInputs.scalePower, hpx, hpε] using hlogy
  · simpa [ChainInputs.scalePower, hpx, hpε] using hklog.trans (by linarith)
  · simpa [ChainInputs.scalePower, hpx, hpε] using hheight
  · simpa [ChainInputs.scalePower, hpx, hpε] using hthreshold

end Riemann
