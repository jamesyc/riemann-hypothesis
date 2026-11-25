module

public import Utilities.ModuleLengthBounds
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

namespace Utilities

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {W M U : Type*} [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M]
  [AddCommGroup U] [Module R U]

/-- The length of a principal DVR quotient is the valuation of its nonzero generator. -/
theorem dvr_length_quotient_span_singleton {a : R} (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    length_quotient_pow_maximalIdeal, addVal_def' u hϖ]

/-- A cyclic torsion layer with principal annihilator has length equal
to the valuation of the annihilator's generator. -/
theorem dvr_length_torsionBy_of_generator {a : R} (ha : a ≠ 0) (w : W)
    (hann : ∀ b : R, b • w = 0 ↔ a ∣ b)
    (hspan : ∀ x : W, a • x = 0 → ∃ b : R, b • w = x) :
    Module.length R (Submodule.torsionBy R W a) = addVal R a := by
  let f := LinearMap.toSpanSingleton R W w
  have hk : f.ker = Ideal.span {a} := by
    ext b
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton]
    exact hann b
  have hr : f.range = Submodule.torsionBy R W a := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      change a • (b • w) = 0
      rw [smul_comm, (hann a).mpr dvd_rfl, smul_zero]
    · exact hspan x
  let e := (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))
  exact e.symm.length_eq.trans (dvr_length_quotient_span_singleton ha)

/-- If multiplying a coefficient of order `a * b` by `y` gives a
coefficient of order `a`, then every vector killed by both `y` and
`a * b` is killed by `b`. -/
theorem dvr_smul_eq_zero_of_annihilator_factor {a b y : R} (ha : a ≠ 0)
    (hann : ∀ t : R, a * b ∣ t * y ↔ a ∣ t)
    {x : W} (hy : y • x = 0) (hab : (a * b) • x = 0) :
    b • x = 0 := by
  rcases le_total (addVal R y) (addVal R (a * b)) with h | h
  · obtain ⟨t, ht⟩ := addVal_le_iff_dvd.mp h
    have ht' : a ∣ t := (hann t).mp (by rw [mul_comm t y, ← ht])
    obtain ⟨u, rfl⟩ := ht'
    have hb : b = y * u :=
      mul_left_cancel₀ ha (ht.trans (by ac_rfl))
    rw [hb, mul_comm, mul_smul, hy, smul_zero]
  · have hua : IsUnit a := isUnit_iff_dvd_one.mpr ((hann 1).mp (by
      rw [one_mul]
      exact addVal_le_iff_dvd.mp h))
    exact hua.smul_eq_zero.mp (by simpa only [mul_smul] using hab)

/-- A killed evaluation bounds the length lost on passing to a submodule
containing its kernel. -/
theorem dvr_length_le_add_addVal_of_evaluation
    (f : M →ₗ[R] W) (u : U →ₗ[R] M) (hker : f.ker ≤ u.range)
    {a : R} (hlen : Module.length R (Submodule.torsionBy R W a) ≤ addVal R a)
    (hkill : ∀ x : M, a • f x = 0) :
    Module.length R M ≤ Module.length R U + addVal R a := by
  let g : M →ₗ[R] Submodule.torsionBy R W a := f.codRestrict _ hkill
  have hg : g.ker ≤ u.range := by
    intro x hx
    exact hker (congrArg Subtype.val hx)
  exact (module_length_le_of_ker_le_range u g hg).trans (add_le_add le_rfl hlen)

/-- If the evaluation has a nonzero value, its annihilator has positive
valuation. The length bound can be combined with the current rank. -/
theorem dvr_length_add_addVal_le_of_evaluation
    (f : M →ₗ[R] W) (u : U →ₗ[R] M) (hker : f.ker ≤ u.range)
    {a b : R} (hlen : Module.length R (Submodule.torsionBy R W b) ≤ addVal R b)
    (hkill : ∀ x : M, b • f x = 0) (hne : ∃ x : M, f x ≠ 0) :
    0 < addVal R b ∧
      Module.length R M + addVal R a ≤ Module.length R U + addVal R (a * b) := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨pos_iff_ne_zero.mpr (fun hb => hx ((addVal_eq_zero_iff.mp hb).smul_eq_zero.mp (hkill x))), ?_⟩
  calc
    _ ≤ (Module.length R U + addVal R b) + addVal R a :=
      add_le_add (dvr_length_le_add_addVal_of_evaluation f u hker hlen hkill) le_rfl
    _ = _ := by rw [add_right_comm, add_assoc, addVal_mul]

end Utilities
