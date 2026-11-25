module

public import Riemann.AuxiliarySmoothedPrimeSelection
public import Riemann.HostRealCharacters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter Utilities

namespace Riemann

/-- The majorant of Proposition 5.3, with coefficients independent of the
primitive character and its logarithmic conductor bound. -/
noncomputable def preparedSmoothedTailMajorant (c₀ c₁ P Q R L y : ℝ) : ℝ :=
  y * (P * Real.exp (-c₀ * Real.log y) +
    Q * L ^ (5 : ℕ) * Real.exp (-c₁ * Real.log y / L) +
    R * L ^ (4 : ℕ) * (1 + c₁ * Real.sqrt (Real.log y)) * Real.exp (-c₁ * Real.sqrt (Real.log y)))

/-- Proposition 5.3 and its trivial-character case, after integrating the
quantitative prime number theorem. -/
theorem exists_preparedSmoothedTailMajorants (c₀ : ℝ) (h₀ : 0 < c₀) (hc : c₀ ≤ 1 / 400) :
    ∃ c₁ P Q R : ℝ, 0 < c₁ ∧ 0 < P ∧ 0 ≤ Q ∧ 0 ≤ R ∧
      (∀ L y : ℝ, 1 ≤ L → 2 ≤ y → |smoothedZetaSum y| ≤ preparedSmoothedTailMajorant c₀ c₁ P Q R L y) ∧
      ∀ (χ : BundledDirichletCharacter), χ.character.IsPrimitive → χ.character ≠ 1 →
        ((∀ a : ZMod (χ.modulus : ℕ), (χ.character a).im = 0) →
          ∀ β ∈ Set.Ioo (1 - c₀) 1, DirichletCharacter.LFunction χ.character (β : ℂ) ≠ 0) →
        ∀ L y : ℝ, 1 ≤ L → Real.log (χ.modulus : ℕ) ≤ L → 2 ≤ y →
          ‖complexSmoothedCharacterSum χ y‖ ≤ preparedSmoothedTailMajorant c₀ c₁ P Q R L y := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The real-zero tests at the chosen pair give a common tail bound on the
full inducing family, including characters outside the survivor set. -/
theorem eventually_preparedHostSmoothedTail (target : BundledDirichletCharacter) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∀ (e : ℕ) {base : ℝ} {q d : ℕ+},
      3 ≤ base → base ≤ x → (pair : SelmerWindowPair ε base q d) →
      ((target.modulus : ℕ) : ℝ) ≤ base ^ (ε / 5) →
      FirstAuxiliaryRealGood target q → SecondAuxiliaryRealGood target q d →
      (Nat.card (SelmerHostBaseGroup target e) : ℝ) ≤ 2 * x ^ (2 + 8 * ε) →
      ∀ {H : Type} [AddCommGroup H] [Fintype H]
        (coord : Multiplicative (ExcessGroup H) ≃*
          (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d))
        (prime : PrimeExcessData H),
        HostInducingConditions prime (selmerHostInducingCharacter coord) →
        ∀ ψ : ExcessCharacter H, ∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y →
          ‖prime.smoothed ψ y‖ ≤ Real.exp (-(x ^ (ε / 8))) * y := by
  obtain ⟨c₀, hc₀, hc, hreal⟩ := exists_noRealZero_nearOne_of_goodTwists target
  obtain ⟨c₁, P, Q, R, hc₁, hP, hQ, hR, hz, hchar⟩ :=
    exists_preparedSmoothedTailMajorants c₀ hc₀ hc
  obtain ⟨A, hA, hmodulus⟩ := exists_selmerHost_logModulus_le target
  have hylarge := (tendsto_rpow_atTop (show 0 < ε / 3 by positivity)).eventually_ge_atTop (Real.log 6)
  filter_upwards [eventually_tailBound_of_prop53_majorant hε hA hP hQ hR hc₀ hc₁, hylarge]
    with x htail hx e base q d hbase hbx pair hmod hqgood hdgood hcard H _ _ coord prime hprime ψ y hy
  obtain ⟨hL₁, hL₂⟩ := hmodulus hε.le hbase hbx pair hcard hsmall
  let L := A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ)
  have hy₂ : 2 ≤ y := by
    have he := Real.exp_le_exp.mpr hx
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 6)] at he
    linarith
  apply htail L y ‖prime.smoothed ψ y‖ hL₁ le_rfl hy
  change ‖prime.smoothed ψ y‖ ≤ preparedSmoothedTailMajorant c₀ c₁ P Q R L y
  by_cases hψ : ψ = 0
  · rw [hψ, prime.smoothed_zero, Complex.norm_real, Real.norm_eq_abs]
    exact hz L y hL₁ hy₂
  let χ := selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) coord ψ
  have hχne : χ.character ≠ 1 := selmerHostInducingCharacter_ne_one coord hψ
  have hχp : χ.character.IsPrimitive := selmerHostInducingCharacter_isPrimitive coord ψ
  have hχL : Real.log (χ.modulus : ℕ) ≤ L :=
    (selmerHostInducingCharacter_logModulus_le coord ψ).trans hL₂
  let : Fact (q : ℕ).Prime := ⟨pair.q_prime⟩
  let : Fact (d : ℕ).Prime := ⟨pair.d_prime⟩
  have hq₄ : (q : ℕ) % 4 = 3 := by have := pair.q_residue; omega
  have hd₄ : (d : ℕ) % 4 = 3 := by have := pair.d_residue; omega
  obtain ⟨hq, hd⟩ := pair.coprime_fixedRealBaseModulus target hmod
  rw [hprime.smoothed_eq_inducing hψ]
  exact hchar χ hχp hχne
    (hreal q d hq₄ hd₄ hq hd (hqgood pair.q_prime hq₄)
      (hdgood pair.q_prime pair.d_prime hq₄ hd₄) coord ψ hψ) L y hL₁ hχL hy₂

end Riemann
