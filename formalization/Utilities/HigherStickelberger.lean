module

public import Utilities.GeneralizedBernoulli
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

@[expose] public section

open scoped BigOperators

namespace Utilities

variable {N : ℕ} [NeZero N] {G : Type*} [CommGroup G]

/-- The inverse pullback of a character along the cyclotomic quotient. -/
noncomputable def stickelbergerDirichletCharacter (π : (ZMod N)ˣ →* G) (χ : G →* ℂ) :
    DirichletCharacter ℂ N :=
  MulChar.ofUnitHom (χ.toHomUnits.comp π)⁻¹

omit [NeZero N] in
@[simp]
theorem stickelbergerDirichletCharacter_apply_unit
    (π : (ZMod N)ˣ →* G) (χ : G →* ℂ) (u : (ZMod N)ˣ) :
    stickelbergerDirichletCharacter π χ (u : ZMod N) = χ ((π u)⁻¹) := by
  rw [stickelbergerDirichletCharacter, MulChar.ofUnitHom_coe, MonoidHom.inv_apply,
    MonoidHom.comp_apply, ← map_inv χ.toHomUnits]
  rfl

/-- The denominator-scaled Bernoulli coefficient as an integer. -/
noncomputable def integralBernoulliCoefficient (N k a : ℕ) [NeZero N] : ℤ :=
  (exists_int_denominator_mul_generalizedBernoulliCoefficient k a (NeZero.pos N)).choose

theorem cast_integralBernoulliCoefficient (N k a : ℕ) [NeZero N] :
    (integralBernoulliCoefficient N k a : ℚ) =
      (generalizedBernoulliDenominator N k : ℚ) * generalizedBernoulliCoefficient N k a :=
  (exists_int_denominator_mul_generalizedBernoulliCoefficient k a (NeZero.pos N)).choose_spec.symm

/-- The Bernoulli part of the higher Stickelberger element, scaled by
`k * generalizedBernoulliDenominator N k` relative to the rational element. -/
noncomputable def integralStickelbergerTheta (π : (ZMod N)ˣ →* G) (k : ℕ) : MonoidAlgebra ℤ G :=
  -∑ u : (ZMod N)ˣ, MonoidAlgebra.single (π u)⁻¹ (integralBernoulliCoefficient N k (u : ZMod N).val)

/-- The integral higher Stickelberger element with the smoothing factor at `a`. -/
noncomputable def integralHigherStickelberger (π : (ZMod N)ˣ →* G) (k a : ℕ)
    (ha : a.Coprime N) : MonoidAlgebra ℤ G :=
  (1 - MonoidAlgebra.single (π (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℤ) ^ k)) *
    integralStickelbergerTheta π k

/-- The Bernoulli part of the rational higher Stickelberger element. -/
noncomputable def rationalStickelbergerTheta (π : (ZMod N)ˣ →* G) (k : ℕ) : MonoidAlgebra ℚ G :=
  -∑ u : (ZMod N)ˣ, MonoidAlgebra.single (π u)⁻¹
    (generalizedBernoulliCoefficient N k (u : ZMod N).val / k)

/-- The usual Bernoulli-normalized higher Stickelberger element, before
clearing rational denominators. -/
noncomputable def rationalHigherStickelberger (π : (ZMod N)ˣ →* G) (k a : ℕ)
    (ha : a.Coprime N) : MonoidAlgebra ℚ G :=
  (1 - MonoidAlgebra.single (π (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℚ) ^ k)) *
    rationalStickelbergerTheta π k

/-- Clearing denominators multiplies the rational element by the explicit
integer `k * generalizedBernoulliDenominator N k`. -/
theorem map_integralHigherStickelberger_eq_smul (π : (ZMod N)ˣ →* G) {k a : ℕ}
    (hk : k ≠ 0) (ha : a.Coprime N) :
    MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ) (integralHigherStickelberger π k a ha) =
      ((k : ℚ) * generalizedBernoulliDenominator N k) • rationalHigherStickelberger π k a ha := by
  rw [integralHigherStickelberger, integralStickelbergerTheta, rationalHigherStickelberger, rationalStickelbergerTheta]
  simp only [map_mul, map_sub, map_one, map_neg, map_sum, MonoidAlgebra.mapRingHom_single,
    map_pow, map_natCast]
  rw [← mul_smul_comm, smul_neg, Finset.smul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro u _
  rw [MonoidAlgebra.smul_single']
  apply congrArg (MonoidAlgebra.single (π u)⁻¹)
  change (integralBernoulliCoefficient N k (u : ZMod N).val : ℚ) = _
  rw [cast_integralBernoulliCoefficient]
  field_simp [Nat.cast_ne_zero.mpr hk]

private theorem generalizedBernoulliValue_eq_sum_units {k : ℕ} (hN : 1 < N)
    (ψ : DirichletCharacter ℂ N) :
    generalizedBernoulliValue k (ψ : ZMod N → ℂ) =
      ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * algebraMap ℚ ℂ (generalizedBernoulliCoefficient N k (u : ZMod N).val) := by
  classical
  let _ : Fact (1 < N) := ⟨hN⟩
  let f (x : ZMod N) := ψ x * algebraMap ℚ ℂ (generalizedBernoulliCoefficient N k x.val)
  calc
    _ = ∑ a ∈ Finset.Icc 1 N, f (a : ZMod N) := by
      unfold generalizedBernoulliValue
      apply Finset.sum_congr rfl
      intro a ha
      have h := (Finset.mem_Icc.mp ha).2
      rcases h.lt_or_eq with hlt | rfl
      · simp only [f, ZMod.val_cast_of_lt hlt]
      · simp [f, MulChar.map_nonunit ψ not_isUnit_zero]
    _ = ∑ x : ZMod N, f x := sum_Icc_natCast_zmod f
    _ = ∑ x ∈ Finset.univ.map (⟨Units.val, Units.val_injective⟩ : (ZMod N)ˣ ↪ ZMod N), f x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      have hx' : ¬ IsUnit x := by
        rintro ⟨u, rfl⟩
        exact hx (Finset.mem_map.mpr ⟨u, Finset.mem_univ _, rfl⟩)
      simp [f, MulChar.map_nonunit ψ hx']
    _ = _ := by rw [Finset.sum_map]; rfl

/-- The integral theta element evaluates to the scaled generalized Bernoulli value. -/
theorem lift_integralStickelbergerTheta (hN : 1 < N) (π : (ZMod N)ˣ →* G)
    (χ : G →* ℂ) (k : ℕ) :
    MonoidAlgebra.lift ℤ ℂ G χ (integralStickelbergerTheta π k) =
      -((generalizedBernoulliDenominator N k : ℂ) *
        generalizedBernoulliValue k (stickelbergerDirichletCharacter π χ : ZMod N → ℂ)) := by
  rw [integralStickelbergerTheta, map_neg, map_sum, generalizedBernoulliValue_eq_sum_units hN,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  have hcoeff := congrArg (algebraMap ℚ ℂ) (cast_integralBernoulliCoefficient N k (u : ZMod N).val)
  rw [map_intCast, map_mul, map_natCast] at hcoeff
  rw [MonoidAlgebra.lift_single, Algebra.smul_def]
  change (integralBernoulliCoefficient N k (u : ZMod N).val : ℂ) * χ ((π u)⁻¹) = _
  rw [hcoeff, stickelbergerDirichletCharacter_apply_unit]
  ring

/-- Character evaluation of the integral higher Stickelberger element. -/
theorem lift_integralHigherStickelberger (hN : 1 < N) (π : (ZMod N)ˣ →* G)
    (χ : G →* ℂ) (k a : ℕ) (ha : a.Coprime N) :
    let ψ := stickelbergerDirichletCharacter π χ
    MonoidAlgebra.lift ℤ ℂ G χ (integralHigherStickelberger π k a ha) =
      (1 - (a : ℂ) ^ k * ψ (a : ZMod N)) *
        (-((generalizedBernoulliDenominator N k : ℂ) * generalizedBernoulliValue k (ψ : ZMod N → ℂ))) := by
  dsimp only
  rw [integralHigherStickelberger, map_mul, map_sub, map_one, lift_integralStickelbergerTheta hN,
    MonoidAlgebra.lift_single, Algebra.smul_def, map_pow, map_natCast,
    ← ZMod.coe_unitOfCoprime a ha, stickelbergerDirichletCharacter_apply_unit]

omit [NeZero N] in
private theorem norm_at_coprime (ψ : DirichletCharacter ℂ N) {a : ℕ} (ha : a.Coprime N) :
    ‖ψ (a : ZMod N)‖ = 1 := by
  rw [← ZMod.coe_unitOfCoprime a ha]
  exact ψ.unit_norm_eq_one _

omit [NeZero N] in
/-- The smoothing factor has nonzero evaluation at any character when
`a > 1` and `k` is positive. -/
theorem stickelbergerSmoothing_ne_zero (ψ : DirichletCharacter ℂ N) {k a : ℕ}
    (hk : k ≠ 0) (ha : a.Coprime N) (ha₁ : 1 < a) :
    1 - (a : ℂ) ^ k * ψ (a : ZMod N) ≠ 0 := by
  intro hz
  have h := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_one, norm_mul, norm_pow, Complex.norm_natCast, norm_at_coprime ψ ha, mul_one] at h
  exact (Nat.one_lt_pow hk ha₁).ne (by exact_mod_cast h)

/-- On the Bernoulli parity the higher Stickelberger character value is nonzero. -/
theorem lift_integralHigherStickelberger_ne_zero (hN : 1 < N) (π : (ZMod N)ˣ →* G)
    (χ : G →* ℂ) {k a : ℕ} (ha : a.Coprime N) (hk : 2 ≤ k) (ha₁ : 1 < a)
    (hparity : χ (π (-1)) = (-1) ^ k) :
    MonoidAlgebra.lift ℤ ℂ G χ (integralHigherStickelberger π k a ha) ≠ 0 := by
  let ψ := stickelbergerDirichletCharacter π χ
  have hpar : ψ (-1) = (-1) ^ k := by
    change stickelbergerDirichletCharacter π χ (-1) = _
    rw [← show (((-1 : (ZMod N)ˣ) : ZMod N)) = -1 by simp,
      stickelbergerDirichletCharacter_apply_unit, ← map_inv π, inv_neg_one]
    exact hparity
  have hD : (generalizedBernoulliDenominator N k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (NeZero.ne N) (primorial_ne_zero (k + 1)))
  rw [lift_integralHigherStickelberger hN]
  exact mul_ne_zero (stickelbergerSmoothing_ne_zero ψ (by omega) ha ha₁)
    (neg_ne_zero.mpr (mul_ne_zero hD (generalizedBernoulliValue_ne_zero_of_parity hk ψ hpar)))

/-- The archimedean bound uses the existing normalized Bernoulli bound
and the elementary bound on the smoothing factor. -/
theorem norm_lift_integralHigherStickelberger_le (hN : 1 < N) (π : (ZMod N)ˣ →* G)
    (χ : G →* ℂ) {k a : ℕ} (ha : a.Coprime N) (hk : 2 ≤ k) :
    ‖MonoidAlgebra.lift ℤ ℂ G χ (integralHigherStickelberger π k a ha)‖ ≤
      (1 + (a : ℝ) ^ k) * generalizedBernoulliHeightBound N k := by
  let ψ := stickelbergerDirichletCharacter π χ
  have hfac : ‖(1 : ℂ) - (a : ℂ) ^ k * ψ (a : ZMod N)‖ ≤ 1 + (a : ℝ) ^ k := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(a : ℂ) ^ k * ψ (a : ZMod N)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_one, norm_mul, norm_pow, Complex.norm_natCast, norm_at_coprime ψ ha, mul_one]
  have hBernoulli := norm_generalizedBernoulliDenominator_mul_le (NeZero.pos N) (le_refl N) hk
    (ψ : ZMod N → ℂ) ψ.norm_le_one
  rw [lift_integralHigherStickelberger hN, norm_mul, norm_neg]
  exact mul_le_mul hfac hBernoulli (norm_nonneg _) (by positivity)

end Utilities
