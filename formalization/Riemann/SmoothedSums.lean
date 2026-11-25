module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Utilities.SmoothedMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

open Utilities

namespace Riemann

noncomputable def zetaCorrection (x : ℝ) : ℝ :=
  -x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

/-- The function G from (2.1). -/
noncomputable def smoothedZetaSum (x : ℝ) : ℝ :=
  (smoothedMangoldt (fun _ => 1) x).re + zetaCorrection x

noncomputable def smoothedTwist (coefficient : ℕ → ℂ) (logDerivativeAtOne : ℂ)
    (x : ℝ) : ℂ :=
  smoothedMangoldt coefficient x + logDerivativeAtOne * (x : ℂ)

theorem continuous_smoothedZetaSum : Continuous smoothedZetaSum := by
  have hcorrection : Continuous zetaCorrection := by
    unfold zetaCorrection
    simp_rw [neg_mul]
    exact Real.continuous_mul_log.fun_neg.add (continuous_const.mul continuous_id)
  exact (Complex.continuous_re.comp (continuous_smoothedMangoldt _)).add hcorrection

theorem continuous_smoothedTwist (coefficient : ℕ → ℂ) (d : ℂ) :
    Continuous (smoothedTwist coefficient d) :=
  (continuous_smoothedMangoldt coefficient).add (continuous_const.mul Complex.continuous_ofReal)

end Riemann
