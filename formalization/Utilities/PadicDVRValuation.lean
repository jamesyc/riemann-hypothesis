module

public import Utilities.PadicSplittingCoefficients
import Utilities.DVREvaluationLength

@[expose] public section

namespace Utilities

open IsDiscreteValuationRing

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O]

/-- Normalize the DVR valuation by the length of the quotient by the base
maximal ideal. This is the weight used in the Selmer character sums. -/
theorem padicDVR_addVal_mul_log_eq (a : O) (ha : a ≠ 0) :
    ((addVal O a).toNat : ℝ) * Real.log ℓ =
      ((Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map
        (algebraMap ℤ_[ℓ] O))).toNat : ℝ) * (-Real.log ‖(a : PadicAlgCl ℓ)‖) := by
  let p : O := (ℓ : O)
  have hp : p ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hspan : (IsLocalRing.maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O) = Ideal.span {p} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hspan, dvr_length_quotient_span_singleton hp]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨r, v, hv⟩ := eq_unit_mul_pow_irreducible hp hϖ
  have hlog (b : O) (w : Oˣ) (k : ℕ) (hb : b = (w : O) * ϖ ^ k) :
      Real.log ‖(b : PadicAlgCl ℓ)‖ = k * Real.log ‖(ϖ : PadicAlgCl ℓ)‖ := by
    rw [hb]
    change Real.log ‖O.val ((w : O) * ϖ ^ k)‖ = _
    have hw : ‖O.val (w : O)‖ = 1 := padicSubalgebra_norm_unit ℓ O w
    rw [map_mul, map_pow, norm_mul, hw, one_mul, norm_pow, Real.log_pow]
    rfl
  have hnormp : ‖(p : PadicAlgCl ℓ)‖ = (ℓ : ℝ)⁻¹ := by
    calc
      _ = ‖algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) (ℓ : ℚ_[ℓ])‖ := by
        rw [map_natCast]
        congr 1
      _ = _ := (PadicAlgCl.norm_extends ℓ (ℓ : ℚ_[ℓ])).trans Padic.norm_p
  have hlogp : (r : ℝ) * Real.log ‖(ϖ : PadicAlgCl ℓ)‖ = -Real.log ℓ := by
    rw [← hlog p v r hv, hnormp, Real.log_inv]
  rw [addVal_def a u hϖ n hu, addVal_def p v hϖ r hv, ENat.toNat_natCast, ENat.toNat_natCast,
    hlog a u n hu]
  calc
    _ = (n : ℝ) * (-((r : ℝ) * Real.log ‖(ϖ : PadicAlgCl ℓ)‖)) := by rw [hlogp, neg_neg]
    _ = _ := by ring

end Utilities
