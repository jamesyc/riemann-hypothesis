module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.DirichletCharacter.Bounds

@[expose] public section

open scoped BigOperators

abbrev RiemannZetaZerosOnLine : Prop := RiemannHypothesis

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

namespace Riemann

def ZetaNonvanishingRightOfHalf : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0

def PrimitiveDirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

theorem riemannHypothesis_of_zetaNonvanishing (h : ZetaNonvanishingRightOfHalf) :
    RiemannHypothesis := by
  intro s hz htrivial hs₁
  have hupper : s.re ≤ 1 / 2 := le_of_not_gt (fun hs => h s hs hz)
  have hpositive : 0 < s.re := by
    by_contra! hs
    exact htrivial ((riemannZeta_eq_zero_iff_of_re_nonpos hs).mp hz)
  have hlower : 1 / 2 ≤ s.re := by
    by_contra! hs
    have hreflected : 1 / 2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hnegative : ∀ n : ℕ, s ≠ -(n : ℂ) := by
      intro n hn
      have hnre : s.re = -(n : ℝ) := by simp [hn]
      have hnonnegative : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hzreflected : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_one_sub hnegative hs₁, hz, mul_zero]
    exact h (1 - s) hreflected hzreflected
  exact le_antisymm hupper hlower

private theorem dirichletEulerFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    1 - χ (p : ZMod N) * (p : ℂ) ^ (-s) ≠ 0 := by
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  have hnorm : ‖χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc
      ‖χ (p : ZMod N)‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
      _ < 1 := by simpa only [one_mul] using hpow
  intro heq
  have hprod : χ (p : ZMod N) * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp heq).symm
  simp [hprod] at hnorm

private theorem primitiveCharacter_ne_one_or {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hexcept : χ ≠ 1 ∨ s ≠ 1) :
    χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
  refine hexcept.imp_left fun hχ hprim => hχ ?_
  rw [← χ.changeLevel_primitiveCharacter, hprim, DirichletCharacter.changeLevel_one]

/-- Passing to the inducing primitive character preserves nonvanishing for positive real part. -/
theorem dirichletLNonvanishing_iff_primitive {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) (hexcept : χ ≠ 1 ∨ s ≠ 1) :
    letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    DirichletCharacter.LFunction χ s ≠ 0 ↔
      DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := by
  let instanceConductor : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprod :
      (∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      dirichletEulerFactor_ne_zero χ.primitiveCharacter (Nat.prime_of_mem_primeFactors hp) hs
  have hfactor := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter (primitiveCharacter_ne_one_or χ hexcept)
  rw [χ.changeLevel_primitiveCharacter] at hfactor
  rw [hfactor, mul_ne_zero_iff_right hprod]

/-- Use the Euler factors of the inducing primitive character. -/
theorem dirichletLNonvanishing_of_primitive
    (h : PrimitiveDirichletLNonvanishingRightOfHalf) :
    DirichletLNonvanishingRightOfHalf := by
  intro N _ χ s hs hexcept
  let instanceConductor : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact (dirichletLNonvanishing_iff_primitive χ (by linarith) hexcept).mpr
    (h χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hs
      (primitiveCharacter_ne_one_or χ hexcept))

/-- Reflect a primitive zero using the completed L-function. -/
theorem primitiveDirichletLZerosOnLine_of_nonvanishing
    (h : PrimitiveDirichletLNonvanishingRightOfHalf) :
    PrimitiveDirichletLZerosOnLine := by
  intro N _ χ hprimitive s hs₀ hs₁ hzero
  have hsne₁ : s ≠ 1 := by
    intro heq
    simp [heq] at hs₁
  refine le_antisymm (le_of_not_gt fun hs => h N χ hprimitive s hs (Or.inr hsne₁) hzero) ?_
  by_contra! hlt
  have hγ : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    rcases χ.even_or_odd with heven | hodd
    · rw [heven.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos hs₀
    · rw [hodd.gammaFactor_def]
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp only [Complex.add_re, Complex.one_re]
      linarith
  have hsne₀ : s ≠ 0 := by
    intro heq
    simp [heq] at hs₀
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hsne₀)] at hzero
  have hcompleted := (div_eq_zero_iff.mp hzero).resolve_right hγ
  have hreflection := hprimitive.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel, hcompleted] at hreflection
  have hlevel : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hreflected := (mul_eq_zero.mp hreflection.symm).resolve_left
    (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hlevel))
      (DirichletCharacter.rootNumber_ne_zero hprimitive))
  have hreflected₀ : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr hsne₁.symm
  have hreflected₁ : (1 - s : ℂ) ≠ 1 := by
    intro heq
    have heqRe := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.one_re] at heqRe
    linarith
  have hreflectedHalf : 1 / 2 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  apply h N χ⁻¹ hprimitive.inv (1 - s) hreflectedHalf (Or.inr hreflected₁)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ _ (Or.inl hreflected₀),
    hreflected, zero_div]

/-- Euler factors preserve zeros in the open critical strip under a change of level. -/
theorem dirichletLZerosOnLine_of_primitive (h : PrimitiveDirichletLZerosOnLine) :
    DirichletLZerosOnLine := by
  intro N _ χ s hs₀ hs₁ hzero
  let instanceConductor : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hsne : s ≠ 1 := by
    intro heq
    simp [heq] at hs₁
  have hprimitiveZero : DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
    by_contra hprimitiveNonzero
    exact (dirichletLNonvanishing_iff_primitive χ hs₀ (Or.inr hsne)).mpr
      hprimitiveNonzero hzero
  exact h χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hs₀ hs₁ hprimitiveZero

end Riemann
