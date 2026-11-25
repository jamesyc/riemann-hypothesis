module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter
open scoped BigOperators

namespace Riemann

/-- The elementary size conditions of Lemma 13.19, separated from the
estimates for the Bessel operators. -/
theorem chainFrame_sizeBounds_of_wordCount {U : Type*} (words : Finset U)
    {X ω b C D η₀ η₁ e₀ : ℝ} {f : ℕ} {dS T : U → ℝ}
    (hX : 20 ≤ X) (hb : 3 ≤ b) (hC : 0 < C) (hD : 0 < D)
    (he₀ : 0 ≤ e₀) (hη₀ : η₀ ≤ ω) (hη₁ : η₁ ≤ ω) (he : Real.sqrt e₀ ≤ ω)
    (hω : 11 * ω * X ≤ 1) (hf : 4 * (f : ℝ) ≤ b * ω ^ 2)
    (hcount : C * X ≤ (words.card : ℝ))
    (hdS : ∀ u ∈ words, D / C ≤ dS u) (hT : ∀ u ∈ words, b ≤ T u) :
    let σ := X⁻¹
    let δ' := 2 * (f : ℝ) / b
    let d u := dS u * (1 - (T u - 1)⁻¹) ^ f
    D ≤ σ * ∑ u ∈ words, dS u ∧
    (∑ u ∈ words, (dS u - d u)) ≤ δ' * ∑ u ∈ words, dS u ∧
    (0 < σ ∧ σ ≤ 1 / 20) ∧ η₀ ≤ σ / 2 ∧ η₁ ≤ σ / 2 ∧ Real.sqrt e₀ ≤ σ / 2 ∧
    e₀ ≤ 1 / 8 ∧ (0 ≤ δ' ∧ δ' ≤ 1 / 4) ∧
    (5 * σ + 3 * Real.sqrt δ' + 4 * Real.sqrt (2 * e₀)) * X ≤ 6 := by
  dsimp only
  have hX' : 0 < X := by linarith
  have hσ := inv_pos.mpr hX'
  have hσ₀ : X⁻¹ ≤ 1 / 20 := by simpa [one_div] using inv_anti₀ (by norm_num) hX
  have hb' : 0 < b := by linarith
  have hω₀ := (Real.sqrt_nonneg e₀).trans he
  have hω₁ : 11 * ω ≤ X⁻¹ := by
    simpa using (le_inv_mul_iff₀ hX').mpr (show X * (11 * ω) ≤ 1 by linarith)
  have hsqrtδ : Real.sqrt (2 * (f : ℝ) / b) ≤ ω := by
    apply Real.sqrt_le_iff.mpr ⟨hω₀, ?_⟩
    apply (div_le_iff₀ hb').mpr
    linarith [mul_nonneg hb'.le (sq_nonneg ω)]
  have hsqrt2e : Real.sqrt (2 * e₀) ≤ 2 * ω := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt he₀, pow_le_pow_left₀ (Real.sqrt_nonneg e₀) he 2]
  have hωsmall : ω ≤ 1 / 20 := by linarith
  have he₁ : e₀ ≤ 1 / 8 := by
    nlinarith [Real.sq_sqrt he₀, pow_le_pow_left₀ (Real.sqrt_nonneg e₀) (he.trans hωsmall) 2]
  have hδ : 0 ≤ 2 * (f : ℝ) / b := by positivity
  have hδ₁ : 2 * (f : ℝ) / b ≤ 1 / 4 := by
    nlinarith [Real.sq_sqrt hδ, pow_le_pow_left₀ (Real.sqrt_nonneg _) (hsqrtδ.trans hωsmall) 2]
  refine ⟨?_, ?_, ⟨hσ, hσ₀⟩, by linarith, by linarith, by linarith, he₁, ⟨hδ, hδ₁⟩, ?_⟩
  · have hsum : (words.card : ℝ) * (D / C) ≤ ∑ u ∈ words, dS u := by
      simpa using (Finset.sum_le_sum hdS : (∑ _u ∈ words, D / C) ≤ ∑ u ∈ words, dS u)
    apply (le_inv_mul_iff₀ hX').mpr
    calc
      _ = (C * X) * (D / C) := by field_simp
      _ ≤ (words.card : ℝ) * (D / C) := by gcongr
      _ ≤ _ := hsum
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have ht : 2 ≤ T u - 1 := by linarith [hT u hu]
    have hrecip : (T u - 1)⁻¹ ≤ 2 / b := by
      have hlow : b / 2 ≤ T u - 1 := by linarith [hT u hu]
      simpa [div_eq_mul_inv] using inv_anti₀ (by positivity : 0 < b / 2) hlow
    have hpow : 1 + (f : ℝ) * (-(T u - 1)⁻¹) ≤ (1 + (-(T u - 1)⁻¹)) ^ f :=
      one_add_mul_le_pow (by linarith [inv_anti₀ (by norm_num : (0 : ℝ) < 2) ht]) _
    have hds : 0 ≤ dS u := (by positivity : 0 ≤ D / C).trans (hdS u hu)
    have hpow' : 1 - (f : ℝ) * (2 / b) ≤ (1 - (T u - 1)⁻¹) ^ f := by
      rw [sub_eq_add_neg (1 : ℝ) ((T u - 1)⁻¹)]
      nlinarith [mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg f)]
    have hmul := mul_le_mul_of_nonneg_left hpow' hds
    rw [show 2 * (f : ℝ) / b * dS u = dS u * ((f : ℝ) * (2 / b)) by ring]
    linarith [show dS u * (1 - (f : ℝ) * (2 / b)) = dS u - dS u * ((f : ℝ) * (2 / b)) by ring]
  · have hsub : 3 * Real.sqrt (2 * (f : ℝ) / b) + 4 * Real.sqrt (2 * e₀) ≤ 11 * ω := by
      linarith
    calc
      _ ≤ (5 * X⁻¹ + 11 * ω) * X := by linarith [mul_le_mul_of_nonneg_right hsub hX'.le]
      _ = 5 + 11 * ω * X := by rw [add_mul, mul_assoc, inv_mul_cancel₀ hX'.ne', mul_one]
      _ ≤ _ := by linarith

/-- The scale and host-degree assumptions of Lemma 13.19 follow from
the same degree interval as Proposition 5.15. -/
theorem eventually_chainFrame_sizeHypotheses {ε CH : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 52) (hCH : 0 < CH) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, (n : ℝ) ≤ 2 * x ^ (2 + 8 * ε) →
      let b := Real.exp (x ^ ε)
      let ω := Real.exp (-(x ^ ε / 8))
      3 ≤ b ∧ 20 ≤ x ^ CH ∧ 11 * ω * x ^ CH ≤ 1 ∧
        4 * (2 * (n : ℝ)) ≤ b * ω ^ (2 : ℕ) := by
  have hcoef : 0 < 1 / (16 * (1 + CH)) := by positivity
  have hlog := (isLittleO_log_rpow_atTop hε).bound hcoef
  filter_upwards [eventually_ge_atTop (3 : ℝ), hlog,
    (tendsto_rpow_atTop hε).eventually_ge_atTop (max (16 * Real.log 11) (max (2 * Real.log 16) (Real.log 3))),
    (tendsto_rpow_atTop hCH).eventually_ge_atTop 20] with x hx hxlog hlarge hX n hn
  have hx₁ : 1 ≤ x := by linarith
  have hx' : 0 < x := by positivity
  have hlogx : Real.log x ≤ x ^ ε / (16 * (1 + CH)) := by
    simpa [Real.norm_of_nonneg (Real.log_nonneg hx₁), Real.norm_of_nonneg (Real.rpow_nonneg hx'.le _),
      div_eq_mul_inv, mul_comm] using hxlog
  have hy : 0 ≤ x ^ ε := Real.rpow_nonneg hx'.le _
  have hlogx₁ : 16 * (1 + CH) * Real.log x ≤ x ^ ε := by
    simpa [mul_comm] using (le_div_iff₀ (by positivity : 0 < 16 * (1 + CH))).mp hlogx
  have hlog₀ : 0 ≤ Real.log x := Real.log_nonneg hx₁
  have hlogx₂ : Real.log x ≤ x ^ ε / 16 := by
    nlinarith [mul_nonneg hCH.le hlog₀]
  have hlogx₃ : CH * Real.log x ≤ x ^ ε / 16 := by linarith
  dsimp only
  refine ⟨(Real.log_le_iff_le_exp (by norm_num)).mp (?_ : Real.log 3 ≤ x ^ ε), hX, ?_, ?_⟩
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  · have h' : 16 * Real.log 11 ≤ x ^ ε := (le_max_left _ _).trans hlarge
    rw [show (11 : ℝ) = Real.exp (Real.log 11) by rw [Real.exp_log (by norm_num)],
      Real.rpow_def_of_pos hx' CH, ← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    rw [mul_comm (Real.log x)]
    linarith
  · have hn' : (n : ℝ) ≤ 2 * x ^ (3 : ℕ) := hn.trans (by
      gcongr
      simpa using Real.rpow_le_rpow_of_exponent_le hx₁ (show 2 + 8 * ε ≤ (3 : ℝ) by linarith))
    have h' : 2 * Real.log 16 ≤ x ^ ε := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
    calc
      _ ≤ 16 * x ^ (3 : ℕ) := by linarith
      _ ≤ Real.exp (3 / 4 * x ^ ε) := by
        apply (Real.log_le_iff_le_exp (by positivity)).mp
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
        linarith
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring

end Riemann
