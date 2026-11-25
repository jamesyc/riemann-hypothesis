module

public import Utilities.DirichletCharacter
public import Utilities.ZModUnits
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.NumberTheory.DirichletCharacter.Bounds

@[expose] public section

namespace Utilities

private theorem exists_square_root_mod_dyadic_mul {m a : ℤ} (hm : 8 ∣ m)
    (ha : a ≡ 1 [ZMOD m]) (k : ℕ) :
    ∃ r : ℤ, Odd r ∧ r ^ 2 ≡ a [ZMOD m * 2 ^ k] := by
  induction k with
  | zero => exact ⟨1, by decide, by simpa using ha.symm⟩
  | succ k ih =>
    obtain ⟨r, hr, hmod⟩ := ih
    obtain ⟨s, hs⟩ := hm.trans (dvd_mul_right m (2 ^ k))
    obtain ⟨d, hd⟩ := hmod.dvd
    by_cases hdEven : Even d
    · obtain ⟨e, he⟩ := hdEven
      refine ⟨r, hr, Int.modEq_iff_dvd.mpr ⟨e, ?_⟩⟩
      rw [hd, he, pow_succ]
      ring
    · obtain ⟨e, he⟩ := Int.not_even_iff_odd.mp hdEven
      obtain ⟨j, hj⟩ := hr
      refine ⟨r + 4 * s, ⟨j + 2 * s, by linarith⟩,
        Int.modEq_iff_dvd.mpr ⟨e - j - s, ?_⟩⟩
      have hpow : m * 2 ^ (k + 1) = 16 * s := by
        rw [pow_succ, ← mul_assoc, hs]
        ring
      calc
        a - (r + 4 * s) ^ (2 : ℕ) = a - r ^ (2 : ℕ) - 8 * s * (r + 2 * s) := by ring
        _ = _ := by rw [hd, hs, he, hj, hpow]; ring

/-- If the smaller level is divisible by eight, the unit reduction
kernel for any further doubling consists of squares. -/
theorem isSquare_of_unitsMap_dyadic_eq_one {m k : ℕ} (hm : 8 ∣ m)
    (u : (ZMod (m * 2 ^ k))ˣ)
    (hu : ZMod.unitsMap (dvd_mul_right m (2 ^ k)) u = 1) : IsSquare u := by
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod (m * 2 ^ k))
  have hval := congrArg (fun v : (ZMod m)ˣ => (v : ZMod m)) hu
  rw [ZMod.unitsMap_val, ← ha, ZMod.cast_intCast (dvd_mul_right m (2 ^ k)), Units.val_one] at hval
  have hmod : a ≡ 1 [ZMOD (m : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa only [Int.cast_one] using hval
  have hm' : (8 : ℤ) ∣ (m : ℤ) := by exact_mod_cast hm
  obtain ⟨r, _, hr⟩ := exists_square_root_mod_dyadic_mul hm' hmod k
  have hr₁ : (r ^ 2 : ℤ) ≡ a [ZMOD ((m * 2 ^ k : ℕ) : ℤ)] := by
    push_cast
    exact hr
  have hsq : (r : ZMod (m * 2 ^ k)) ^ (2 : ℕ) = (u : ZMod (m * 2 ^ k)) := by
    rw [← ha, ← Int.cast_pow, ZMod.intCast_eq_intCast_iff]
    exact hr₁
  have hrU : IsUnit (r : ZMod (m * 2 ^ k)) :=
    (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp (hsq.symm ▸ u.isUnit)
  refine ⟨hrU.unit, Units.ext ?_⟩
  rw [Units.val_mul, hrU.unit_spec, ← pow_two, hsq]

/-- Every quadratic character at a further dyadic level already factors
through any smaller level divisible by eight. -/
theorem quadraticCharacter_factorsThrough_dyadic {m k : ℕ} [NeZero (m * 2 ^ k)]
    (hm : 8 ∣ m) (χ : DirichletCharacter ℂ (m * 2 ^ k)) (hχ : χ ^ (2 : ℕ) = 1) :
    χ.FactorsThrough m := by
  apply (χ.factorsThrough_iff_ker_unitsMap (dvd_mul_right m (2 ^ k))).mpr
  intro u hu
  obtain ⟨v, rfl⟩ := isSquare_of_unitsMap_dyadic_eq_one hm u hu
  change χ.toUnitHom (v * v) = 1
  apply Units.ext
  rw [map_mul, Units.val_mul, MulChar.coe_toUnitHom, ← pow_two,
    ← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe, Units.val_one]

theorem quadraticCharacter_conductor_dvd_of_dyadic_extension
    {N m k : ℕ} [NeZero (m * 2 ^ k)]
    (hm : 8 ∣ m) (hdiv : N ∣ m * 2 ^ k)
    (χ : DirichletCharacter ℂ N) (hχ : χ ^ (2 : ℕ) = 1) :
    χ.conductor ∣ m := by
  let ξ := DirichletCharacter.changeLevel hdiv χ
  have hξ : ξ ^ (2 : ℕ) = 1 := by
    change (DirichletCharacter.changeLevel hdiv χ) ^ (2 : ℕ) = 1
    rw [← map_pow, hχ, map_one]
  have hfactor := quadraticCharacter_factorsThrough_dyadic hm ξ hξ
  have hcond := ξ.conductor_dvd_of_mem_conductorSet hfactor
  rw [show ξ.conductor = χ.conductor from χ.conductor_changeLevel hdiv] at hcond
  exact hcond

theorem dirichletCharacter_sq_eq_one_of_real {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : ∀ u : ZMod N, (χ u).im = 0) :
    χ ^ (2 : ℕ) = 1 := by
  apply MulChar.ext
  intro u
  have hreal : χ u = ((χ u).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hχ u
  have hnorm := χ.unit_norm_eq_one u
  rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hnorm
  have hsq : (χ u).re ^ (2 : ℕ) = 1 := by rw [← sq_abs, hnorm]; norm_num
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hreal, ← Complex.ofReal_pow, hsq,
    Complex.ofReal_one]

/-- A quadratic character at a product of coprime levels separates into
quadratic characters on the two factors. -/
theorem exists_quadraticCharacter_mul_of_coprime {a b : ℕ}
    (hab : a.Coprime b) (χ : DirichletCharacter ℂ (a * b)) (hχ : χ ^ (2 : ℕ) = 1) :
    ∃ χa : DirichletCharacter ℂ a, ∃ χb : DirichletCharacter ℂ b,
      χa ^ (2 : ℕ) = 1 ∧ χb ^ (2 : ℕ) = 1 ∧
      χ = DirichletCharacter.changeLevel (dvd_mul_right a b) χa *
        DirichletCharacter.changeLevel (dvd_mul_left b a) χb := by
  let e := zmodUnitsCRT hab
  let χa := MulChar.ofUnitHom (χ.toUnitHom.comp
    (e.symm.toMonoidHom.comp (MonoidHom.inl (ZMod a)ˣ (ZMod b)ˣ)))
  let χb := MulChar.ofUnitHom (χ.toUnitHom.comp
    (e.symm.toMonoidHom.comp (MonoidHom.inr (ZMod a)ˣ (ZMod b)ˣ)))
  have hχa (u : (ZMod a)ˣ) : χa u = χ (e.symm (u, 1)) := by
    simp [χa]
  have hχb (u : (ZMod b)ˣ) : χb u = χ (e.symm (1, u)) := by
    simp [χb]
  refine ⟨χa, χb, ?_, ?_, ?_⟩
  · apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hχa]
    have h := DFunLike.congr_fun hχ ((e.symm (u, 1) : (ZMod (a * b))ˣ) : ZMod (a * b))
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h
  · apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hχb]
    have h := DFunLike.congr_fun hχ ((e.symm (1, u) : (ZMod (a * b))ˣ) : ZMod (a * b))
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h
  · apply MulChar.ext
    intro u
    have he : e.symm ((e u).1, 1) * e.symm (1, (e u).2) = u := by
      apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      simp
    have h : χ u = χa (e u).1 * χb (e u).2 := by
      rw [hχa, hχb, ← map_mul, ← Units.val_mul, he]
    simpa only [e, zmodUnitsCRT_apply, MulChar.mul_apply, DirichletCharacter.changeLevel_def,
      MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom] using h

end Utilities
