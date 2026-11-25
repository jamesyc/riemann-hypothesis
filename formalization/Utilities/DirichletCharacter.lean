module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Data.PNat.Defs
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.IntegralDomain

@[expose] public section

open scoped ComplexConjugate

namespace Utilities

/-- A finite family can contain characters with different positive moduli. -/
structure BundledDirichletCharacter where
  modulus : ℕ+
  character : DirichletCharacter ℂ (modulus : ℕ)

/-- Bundle the primitive character inducing a character of positive level. -/
noncomputable def BundledDirichletCharacter.primitiveOf {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : BundledDirichletCharacter :=
  ⟨⟨χ.conductor, Nat.pos_of_ne_zero χ.conductor_ne_zero⟩, χ.primitiveCharacter⟩

@[simp] theorem BundledDirichletCharacter.primitiveOf_isPrimitive {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : (primitiveOf χ).character.IsPrimitive :=
  χ.primitiveCharacter_isPrimitive

@[simp] theorem BundledDirichletCharacter.primitiveOf_character_eq_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : (primitiveOf χ).character = 1 ↔ χ = 1 := by
  change χ.primitiveCharacter = 1 ↔ χ = 1
  constructor
  · intro h
    rw [← χ.changeLevel_primitiveCharacter, h, map_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

private theorem BundledDirichletCharacter.ext_int
    (χ ξ : BundledDirichletCharacter) (hmodulus : χ.modulus = ξ.modulus)
    (hvalue : ∀ n : ℤ, χ.character n = ξ.character n) : χ = ξ := by
  rcases χ with ⟨M, χ⟩
  rcases ξ with ⟨N, ξ⟩
  change M = N at hmodulus
  cases hmodulus
  congr 1
  exact MulChar.ext' fun a => by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    exact hvalue n

@[simp] theorem BundledDirichletCharacter.primitiveOf_changeLevel
    {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (χ : DirichletCharacter ℂ N) :
    primitiveOf (DirichletCharacter.changeLevel h χ) = primitiveOf χ := by
  apply ext_int
  · exact Subtype.ext (χ.conductor_changeLevel h)
  · exact χ.primitiveCharacter_changeLevel_apply h

theorem BundledDirichletCharacter.primitiveOf_eq_self (χ : BundledDirichletCharacter)
    (h : χ.character.IsPrimitive) :
    letI : NeZero (χ.modulus : ℕ) := ⟨χ.modulus.pos.ne'⟩
    primitiveOf χ.character = χ := by
  let _ : NeZero (χ.modulus : ℕ) := ⟨χ.modulus.pos.ne'⟩
  apply ext_int
  · exact Subtype.ext h
  · intro n
    by_cases hn : IsCoprime n (χ.modulus : ℕ)
    · exact χ.character.primitiveCharacter_apply_of_isCoprime hn
    · change χ.character.primitiveCharacter n = χ.character n
      rw [(χ.character.primitiveCharacter.apply_eq_zero_iff n).mpr (by rwa [show χ.character.conductor =
        (χ.modulus : ℕ) from h]), (χ.character.apply_eq_zero_iff n).mpr hn]

/-- The image of a complex Dirichlet character has cardinality equal to its order. -/
theorem card_dirichletCharacter_unit_range {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Nat.card χ.toUnitHom.range = orderOf χ := by
  let f := χ.toUnitHom
  let _ : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨z, hz⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic f.range)
  apply Nat.dvd_antisymm
  · rw [← orderOf_eq_card_of_zpowers_eq_top hz, orderOf_dvd_iff_pow_eq_one]
    obtain ⟨u, hu⟩ := f.rangeRestrict_surjective z
    rw [← hu]
    apply Subtype.ext
    apply Units.ext
    have huχ := congrArg (fun ψ : DirichletCharacter ℂ N => ψ (u : ZMod N))
      (pow_orderOf_eq_one χ)
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, MonoidHom.coe_rangeRestrict,
      Units.val_pow_eq_pow_val, Units.val_one, f, MulChar.coe_toUnitHom,
      ← MulChar.pow_apply_coe, MulChar.one_apply_coe] using huχ
  · rw [orderOf_dvd_iff_pow_eq_one]
    apply MulChar.ext
    intro u
    have hu := congrArg (fun w : f.range => ((w : ℂˣ) : ℂ))
      (pow_card_eq_one' (x := f.rangeRestrict u))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, MonoidHom.coe_rangeRestrict,
      Units.val_pow_eq_pow_val, Units.val_one, f, MulChar.coe_toUnitHom,
      ← MulChar.pow_apply_coe, MulChar.one_apply_coe] using hu

/-- Conjugation of the Dirichlet series extends to the entire L-functions of
nontrivial characters. -/
theorem dirichletLFunction_inv_eq_conj {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ⁻¹ = conj ∘ DirichletCharacter.LFunction χ ∘ conj := by
  have hχinv : χ⁻¹ ≠ 1 := by simpa using hχ
  have hinv := Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (DirichletCharacter.differentiable_LFunction hχinv)
  have hconj : Differentiable ℂ (conj ∘ DirichletCharacter.LFunction χ ∘ conj) := by
    intro z
    exact differentiableAt_conj_conj_iff.mpr (DirichletCharacter.differentiable_LFunction hχ (conj z))
  apply hinv.eq_of_eventuallyEq (Complex.analyticOnNhd_univ_iff_differentiable.mpr hconj)
    (z₀ := (2 : ℂ))
  filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : 1 < (2 : ℂ).re)] with z hz
  change 1 < z.re at hz
  have hzc : 1 < (conj z).re := by rwa [Complex.conj_re]
  change DirichletCharacter.LFunction χ⁻¹ z = conj (DirichletCharacter.LFunction χ (conj z))
  rw [DirichletCharacter.LFunction_eq_LSeries _ hz, DirichletCharacter.LFunction_eq_LSeries _ hzc]
  simp only [LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [LSeries.term_of_ne_zero hn, map_div₀]
    rw [← Complex.conj_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne),
      Complex.conj_natCast, ← Complex.star_def, MulChar.star_apply']

theorem logDeriv_dirichletLFunction_inv_at_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    logDeriv (DirichletCharacter.LFunction χ⁻¹) 1 =
      conj (logDeriv (DirichletCharacter.LFunction χ) 1) := by
  simp only [dirichletLFunction_inv_eq_conj χ hχ, logDeriv_apply, deriv_conj_conj,
    Function.comp_apply, map_one, map_div₀]

end Utilities
