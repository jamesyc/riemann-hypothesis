module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal

namespace Utilities

/-- A series of integrable functions with summable integrals of their norms
has an integrable pointwise sum. -/
theorem integrable_tsum_of_summable_integral_norm {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [CompleteSpace E] [Countable ι] {μ : Measure α} {f : ι → α → E}
    (hf : ∀ i, Integrable (f i) μ) (hs : Summable fun i => ∫ x, ‖f i x‖ ∂μ) :
    Integrable (fun x => ∑' i, f i x) μ := by
  have hmeas (i : ι) : AEMeasurable (fun x => ‖f i x‖ₑ) μ := (hf i).aestronglyMeasurable.eNorm
  have hsize : (∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hmeas]
    have hnorm (i : ι) : (∫⁻ x, ‖f i x‖ₑ ∂μ) = ‖∫ x, ‖f i x‖ ∂μ‖ₑ :=
      (eNorm_integral_norm_eq_lintegral_eNorm (hf i)).symm
    simp_rw [hnorm]
    exact tsum_eNorm_ne_top_iff_summable_norm.mpr (by simpa only [Real.norm_eq_abs] using hs.abs)
  have hae := ae_lt_top' (AEMeasurable.tsum hmeas) hsize
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
      (f := fun indices x => ∑ i ∈ indices, f i x)
      (fun indices => indices.aestronglyMeasurable_fun_sum fun i _ => (hf i).aestronglyMeasurable) ?_
    exact hae.mono fun x hx => (Summable.of_eNorm hx.ne).hasSum
  · rw [hasFiniteIntegral_iff_eNorm]
    exact lt_of_le_of_lt (lintegral_mono fun _ => eNorm_tsum_le_tsum_eNorm) hsize.lt_top

end Utilities
