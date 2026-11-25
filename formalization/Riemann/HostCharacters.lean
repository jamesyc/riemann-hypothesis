module

public import Riemann.AdmissibleExcess
public import Mathlib.NumberTheory.LegendreSymbol.Basic

@[expose] public section

open Utilities

namespace Riemann

theorem zmodTwo_character_eq_sign_pow (χ : AddChar (ZMod 2) ℂ) :
    ∃ b : Bool, ∀ t, χ t = zmodTwoSign t ^ b.toNat := by
  have hsq : χ 1 * χ 1 = 1 := by
    rw [← χ.map_add_eq_mul, show (1 : ZMod 2) + 1 = 0 by decide, χ.map_zero_eq_one]
  have hs : χ 1 = 1 ∨ χ 1 = -1 := by
    have h : (χ 1 - 1) * (χ 1 + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hcases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hs with hs | hs
  · exact ⟨false, fun t => (hcases t).elim
      (fun h => h.symm ▸ χ.map_zero_eq_one) (fun h => h.symm ▸ hs)⟩
  · refine ⟨true, fun t => ?_⟩
    rcases hcases t with rfl | rfl
    · simp [χ.map_zero_eq_one]
    · simp [hs, zmodTwoSign_apply, show (1 : ZMod 2) ≠ 0 by decide]

/-- A character surviving the average over `A₀` is a power of the target
character times independent quadratic characters in the two auxiliary factors. -/
theorem selmerSurvivor_eq_target_pow_mul_signs
    (target : BundledDirichletCharacter) (e : ℕ)
    (ψ : ExcessCharacter (SelmerHostBaseGroup target e))
    (hψ : ∀ u ∈ selmerAveragingSubgroup target e, ψ (0, 0, u) = 1) :
    ∃ (i : ℕ) (dSign qSign : Bool), i < orderOf target.character ∧
      ∀ c : ExcessGroup (SelmerHostBaseGroup target e),
        ψ c = (selmerBaseTarget target e c.2.2.toMul : ℂ) ^ i *
          zmodTwoSign c.2.1 ^ qSign.toNat * zmodTwoSign c.1 ^ dSign.toNat := by
  let H := SelmerHostBaseGroup target e
  let χ : AddChar H ℂ :=
    { toFun := fun t => ψ (0, 0, t)
      map_zero_eq_one' := ψ.map_zero_eq_one
      map_add_eq_mul' := fun a b => by simpa using ψ.map_add_eq_mul (0, 0, a) (0, 0, b) }
  let χq : AddChar (ZMod 2) ℂ :=
    { toFun := fun t => ψ (0, t, 0)
      map_zero_eq_one' := ψ.map_zero_eq_one
      map_add_eq_mul' := fun a b => by
        rw [← ψ.map_add_eq_mul]
        congr 1
        exact Prod.ext rfl (Prod.ext rfl (show (0 : H) = 0 + 0 from (zero_add (0 : H)).symm)) }
  let χd : AddChar (ZMod 2) ℂ :=
    { toFun := fun t => ψ (t, 0, 0)
      map_zero_eq_one' := ψ.map_zero_eq_one
      map_add_eq_mul' := fun a b => by
        rw [← ψ.map_add_eq_mul]
        congr 1
        exact Prod.ext rfl (Prod.ext rfl (show (0 : H) = 0 + 0 from (zero_add (0 : H)).symm)) }
  obtain ⟨i, hi, hpow⟩ := selmerBaseCharacter_eq_pow_of_averagingSubgroup target e χ hψ
  obtain ⟨qSign, hq⟩ := zmodTwo_character_eq_sign_pow χq
  obtain ⟨dSign, hd⟩ := zmodTwo_character_eq_sign_pow χd
  refine ⟨i, dSign, qSign, hi, fun c => ?_⟩
  have hsplit : ((0, 0, c.2.2) : ExcessGroup H) + (0, c.2.1, 0) + (c.1, 0, 0) = c := by
    rcases c with ⟨d, q, t⟩
    exact Prod.ext (by simp) (Prod.ext (by simp) (show (t + 0 + 0 : H) = t from (add_zero (t + (0 : H))).trans (add_zero t)))
  rw [← hpow c.2.2, ← hq c.2.1, ← hd c.1]
  change ψ c = ψ (0, 0, c.2.2) * ψ (0, c.2.1, 0) * ψ (c.1, 0, 0)
  nth_rw 1 [← hsplit]
  rw [ψ.map_add_eq_mul, ψ.map_add_eq_mul]


/-- The survivor with the indicated target power and optional auxiliary twists. -/
noncomputable def selmerSurvivor (target : BundledDirichletCharacter) (e i : ℕ)
    (qSign dSign : Bool) : ExcessCharacter (SelmerHostBaseGroup target e) := by
  let H := SelmerHostBaseGroup target e
  let base : AddChar H ℂ :=
    { toFun := fun u : H => (selmerBaseTarget target e u.toMul : ℂ)
      map_zero_eq_one' := by change ↑(selmerBaseTarget target e 1) = (1 : ℂ); simp
      map_add_eq_mul' := fun u v => by
        change ↑(selmerBaseTarget target e (u.toMul * v.toMul)) = (_ : ℂ) * _
        simp }
  let baseCoord := (AddMonoidHom.snd (ZMod 2) H).comp (AddMonoidHom.snd (ZMod 2) (ZMod 2 × H))
  let qCoord := (AddMonoidHom.fst (ZMod 2) H).comp (AddMonoidHom.snd (ZMod 2) (ZMod 2 × H))
  exact (base.compAddMonoidHom baseCoord) ^ i *
    (zmodTwoSign.compAddMonoidHom qCoord) ^ qSign.toNat *
    (zmodTwoSign.compAddMonoidHom (AddMonoidHom.fst (ZMod 2) (ZMod 2 × H))) ^ dSign.toNat

@[simp] theorem selmerSurvivor_apply (target : BundledDirichletCharacter) (e i : ℕ)
    (qSign dSign : Bool) (c : ExcessGroup (SelmerHostBaseGroup target e)) :
    selmerSurvivor target e i qSign dSign c = (selmerBaseTarget target e c.2.2.toMul : ℂ) ^ i *
      zmodTwoSign c.2.1 ^ qSign.toNat * zmodTwoSign c.1 ^ dSign.toNat := rfl

theorem selmerSurvivor_trivial_on_averagingSubgroup
    (target : BundledDirichletCharacter) (e i : ℕ) (qSign dSign : Bool)
    (u : SelmerHostBaseGroup target e) (hu : u ∈ selmerAveragingSubgroup target e) :
    selmerSurvivor target e i qSign dSign (0, 0, u) = 1 := by
  have ht : selmerBaseTarget target e u.toMul = 1 := hu
  rw [selmerSurvivor_apply, ht]
  simp

/-- A survivor is determined by its exponent modulo the order of the target and its two signs. -/
theorem selmerSurvivor_injective (target : BundledDirichletCharacter) (e : ℕ) :
    Function.Injective (fun c : Fin (orderOf target.character) × Bool × Bool =>
      selmerSurvivor target e c.1 c.2.1 c.2.2) := by
  intro a b hab
  have htarget : target.character ^ (a.1 : ℕ) = target.character ^ (b.1 : ℕ) := by
    apply MulChar.ext
    intro v
    let _ : NeZero (selmerBaseModulus target e) := ⟨(selmerBaseModulus_pos target e).ne'⟩
    have hdiv : (target.modulus : ℕ) ∣ selmerBaseModulus target e := Nat.dvd_lcm_right _ _
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hdiv v
    have hunit : (selmerBaseTarget target e (QuotientGroup.mk u) : ℂ) = target.character v := by
      rw [selmerBaseTarget_mk]
      change (target.character.toUnitHom (ZMod.unitsMap _ u) : ℂ) = _
      rw [hu, MulChar.coe_toUnitHom]
    have h := DFunLike.congr_fun hab (0, 0, Additive.ofMul (QuotientGroup.mk u))
    simp only [selmerSurvivor_apply, show zmodTwoSign 0 = 1 from zmodTwoSign.map_zero_eq_one,
      one_pow, mul_one] at h
    change (selmerBaseTarget target e (QuotientGroup.mk u) : ℂ) ^ (a.1 : ℕ) =
      (selmerBaseTarget target e (QuotientGroup.mk u) : ℂ) ^ (b.1 : ℕ) at h
    simpa only [hunit, MulChar.pow_apply_coe] using h
  apply Prod.ext (Fin.ext (pow_injOn_Iio_orderOf a.1.isLt b.1.isLt htarget))
  have hsign : Function.Injective (fun b : Bool => zmodTwoSign 1 ^ b.toNat) := by
    intro a b h
    change zmodTwoSign 1 ^ a.toNat = zmodTwoSign 1 ^ b.toNat at h
    cases a <;> cases b <;> (first
      | rfl
      | have hre := congrArg Complex.re h
        norm_num [zmodTwoSign_apply, show (1 : ZMod 2) ≠ 0 by decide] at hre)
  have hq := DFunLike.congr_fun hab (0, 1, 0)
  have hd := DFunLike.congr_fun hab (1, 0, 0)
  apply Prod.ext
  · apply hsign
    simpa [show (0 : SelmerHostBaseGroup target e).toMul = 1 from rfl] using hq
  · apply hsign
    simpa [show (0 : SelmerHostBaseGroup target e).toMul = 1 from rfl] using hd

/-- The nontrivial quadratic character attached to a prime congruent to three mod four. -/
noncomputable def selmerQuadraticCharacter {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    DirichletCharacter ℂ p :=
  MulChar.ofUnitHom (zmodTwoSign.toMonoidHom.comp
    ((selmerSquareClassSign hp).toMonoidHom.comp (QuotientGroup.mk' _))).toHomUnits

@[simp] theorem selmerQuadraticCharacter_apply_unit
    {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (u : (ZMod p)ˣ) :
    selmerQuadraticCharacter hp u = zmodTwoSign (selmerSquareClassSign hp (QuotientGroup.mk u)).toAdd := by
  simp only [selmerQuadraticCharacter, MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, AddChar.toMonoidHom_apply]
  rfl

theorem selmerQuadraticCharacter_apply_int {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 3) (n : ℤ) :
    selmerQuadraticCharacter hp n = (legendreSym p n : ℂ) := by
  let x := (n : ZMod p)
  change selmerQuadraticCharacter hp x = (quadraticChar (ZMod p) x : ℂ)
  by_cases hx : x = 0
  · rw [hx, MulChar.map_zero, quadraticChar_zero, Int.cast_zero]
  let u : (ZMod p)ˣ := Units.mk0 x hx
  have hsq : (QuotientGroup.mk u : (ZMod p)ˣ ⧸ selmerSquareUnits p) = 1 ↔ IsSquare x := by
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hu
      obtain ⟨v, -, hv⟩ := Subgroup.mem_map.mp hu
      refine ⟨v, ?_⟩
      change (u : ZMod p) = v * v
      simpa [pow_two] using congrArg (fun a : (ZMod p)ˣ => (a : ZMod p)) hv.symm
    · rintro ⟨z, hz⟩
      have hz₀ : z ≠ 0 := fun h => hx (by rw [hz, h, mul_zero])
      refine Subgroup.mem_map.mpr ⟨Units.mk0 z hz₀, Subgroup.mem_top _, ?_⟩
      apply Units.ext
      change z ^ 2 = x
      rw [pow_two, hz]
  have hsign : (selmerSquareClassSign hp (QuotientGroup.mk u)).toAdd = 0 ↔ IsSquare x := by
    rw [← hsq]
    change selmerSquareClassSign hp (QuotientGroup.mk u) = 1 ↔ _
    rw [← map_one (selmerSquareClassSign hp), (selmerSquareClassSign hp).injective.eq_iff]
  change selmerQuadraticCharacter hp u = _
  rw [selmerQuadraticCharacter_apply_unit, zmodTwoSign_apply]
  by_cases hs : IsSquare x
  · rw [ite_eq_left (hsign.mpr hs), (quadraticChar_one_iff_isSquare hx).mpr hs]
    norm_num
  · rw [ite_eq_right (hsign.not.mpr hs), quadraticChar_neg_one_iff_not_isSquare.mpr hs]
    norm_num

theorem selmerQuadraticCharacter_ne_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    selmerQuadraticCharacter hp ≠ 1 := by
  intro h
  have heq := DFunLike.congr_fun h ((-1 : (ZMod p)ˣ) : ZMod p)
  rw [selmerQuadraticCharacter_apply_unit, selmerSquareClassSign_neg_one, MulChar.one_apply_coe] at heq
  change zmodTwoSign 1 = 1 at heq
  have hre := congrArg Complex.re heq
  norm_num [zmodTwoSign_apply, show (1 : ZMod 2) ≠ 0 by decide] at hre

theorem selmerQuadraticCharacter_isPrimitive {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    (selmerQuadraticCharacter hp).IsPrimitive := by
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp
      (selmerQuadraticCharacter hp).conductor_dvd_level with h | h
  · exact (selmerQuadraticCharacter_ne_one hp
      (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)).elim
  · exact h

set_option backward.isDefEq.respectTransparency false in
theorem selmerHostDirichlet_eq_target_pow_mul_quadratic
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime]
    (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
    (ψ : ExcessCharacter (SelmerHostBaseGroup target e))
    (i : ℕ) (qSign dSign : Bool)
    (hψ : ∀ c : ExcessGroup (SelmerHostBaseGroup target e),
      ψ c = (selmerBaseTarget target e c.2.2.toMul : ℂ) ^ i *
        zmodTwoSign c.2.1 ^ qSign.toNat * zmodTwoSign c.1 ^ dSign.toNat) :
    let hbase : selmerBaseModulus target e ∣ selmerHostModulus target e q d :=
      dvd_trans (Nat.dvd_lcm_left _ q) (Nat.dvd_lcm_left _ d)
    let ht : (target.modulus : ℕ) ∣ selmerHostModulus target e q d :=
      dvd_trans (Nat.dvd_lcm_right _ _) hbase
    let hqdiv : (q : ℕ) ∣ selmerHostModulus target e q d :=
      dvd_trans (Nat.dvd_lcm_right (selmerBaseModulus target e) _) (Nat.dvd_lcm_left _ d)
    let hddiv : (d : ℕ) ∣ selmerHostModulus target e q d := Nat.dvd_lcm_right _ _
    selmerHostDirichlet (target := target) (e := e) (q := q) (d := d)
      (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm ψ =
      DirichletCharacter.changeLevel ht (target.character ^ i) *
      DirichletCharacter.changeLevel hqdiv (selmerQuadraticCharacter hq₄ ^ qSign.toNat) *
      DirichletCharacter.changeLevel hddiv (selmerQuadraticCharacter hd₄ ^ dSign.toNat) := by
  dsimp only
  let _ := selmerHostField_isAbelianGalois target e q d
  apply MulChar.ext
  intro u
  let τ := (selmerCyclotomicUnitsEquiv target e q d).symm u
  have hu : selmerCyclotomicUnitsEquiv target e q d τ = u :=
    (selmerCyclotomicUnitsEquiv target e q d).apply_symm_apply u
  conv_lhs => rw [← hu, selmerHostDirichlet_apply_gal]
  rw [MulEquiv.symm_symm]
  let c := selmerHostGalCRT target e q d hq hd (τ.restrictNormal (selmerHostField target e q d))
  change ψ ((selmerSquareClassSign hd₄ c.2).toAdd, (selmerSquareClassSign hq₄ c.1.2).toAdd,
      Additive.ofMul c.1.1) = _
  dsimp only [c]
  rw [selmerHostGalCRT_restrictNormal, hu, selmerHostUnitsCRT_apply, hψ]
  let N := selmerHostModulus target e q d
  let hb : selmerBaseModulus target e ∣ N :=
    dvd_trans (Nat.dvd_lcm_left _ q) (Nat.dvd_lcm_left _ d)
  let ht : (target.modulus : ℕ) ∣ selmerBaseModulus target e := Nat.dvd_lcm_right _ _
  have hvalue :
      (selmerBaseTarget target e (QuotientGroup.mk (ZMod.unitsMap hb u)) : ℂ) =
        target.character (ZMod.unitsMap (ht.trans hb) u) := by
    rw [selmerBaseTarget_mk]
    change (target.character.toUnitHom (ZMod.unitsMap ht (ZMod.unitsMap hb u)) : ℂ) = _
    rw [show ZMod.unitsMap ht (ZMod.unitsMap hb u) = ZMod.unitsMap (ht.trans hb) u from
      DFunLike.congr_fun (ZMod.unitsMap_comp ht hb) u, MulChar.coe_toUnitHom]
  simp only [MulChar.coe_toUnitHom, MulChar.mul_apply, DirichletCharacter.changeLevel_def,
    MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.pow_apply_coe,
    selmerQuadraticCharacter_apply_unit]
  exact congrArg (fun z : ℂ => z ^ i * _ * _) hvalue

/-- A fixed primitive power of the target, independent of the host scale and auxiliary primes. -/
noncomputable def selmerFixedCharacter (target : BundledDirichletCharacter) (i : ℕ) :
    BundledDirichletCharacter := by
  let _ : NeZero (target.modulus : ℕ) := ⟨target.modulus.pos.ne'⟩
  exact BundledDirichletCharacter.primitiveOf (target.character ^ i)

theorem selmerHostInducingCharacter_untwisted
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime]
    (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d) (i : ℕ) :
    selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
      (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm
      (selmerSurvivor target e i false false) = selmerFixedCharacter target i := by
  let _ : NeZero (selmerHostModulus target e q d) := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let _ : NeZero (target.modulus : ℕ) := ⟨target.modulus.pos.ne'⟩
  unfold selmerHostInducingCharacter selmerFixedCharacter
  rw [selmerHostDirichlet_eq_target_pow_mul_quadratic target e q d hq₄ hd₄ hq hd _ i false false
    (selmerSurvivor_apply target e i false false)]
  simp only [Bool.toNat_false, pow_zero, map_one, mul_one,
    BundledDirichletCharacter.primitiveOf_changeLevel]

/-- The fixed nontrivial characters of (6.1), with a common positive weight. -/
theorem exists_selmerFixedCombination (target : BundledDirichletCharacter)
    (hprim : target.character.IsPrimitive) :
    ∃ (family : Fin (orderOf target.character - 1) → BundledDirichletCharacter)
      (weight : Fin (orderOf target.character - 1) → ℝ),
      (∀ i, family i = selmerFixedCharacter target ((i : ℕ) + 1)) ∧
      (∀ i, weight i = (3 * (orderOf target.character : ℝ) + 1)⁻¹) ∧
      (∀ i, (family i).character ≠ 1) ∧ (∀ i, 0 < weight i) ∧
      (target.character ≠ 1 → ∃ i, family i = target) := by
  let _ : NeZero (target.modulus : ℕ) := ⟨target.modulus.pos.ne'⟩
  refine ⟨fun i => selmerFixedCharacter target ((i : ℕ) + 1),
    fun _ => (3 * (orderOf target.character : ℝ) + 1)⁻¹, fun _ => rfl, fun _ => rfl,
    ?_, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    exact mt ((BundledDirichletCharacter.primitiveOf_character_eq_one _).mp)
      (pow_ne_one_of_lt_orderOf (by omega) (by omega))
  · intro i
    positivity
  · intro h
    have horder : 0 < orderOf target.character := orderOf_pos _
    have hne : orderOf target.character ≠ 1 := mt orderOf_eq_one_iff.mp h
    refine ⟨⟨0, by omega⟩, ?_⟩
    change BundledDirichletCharacter.primitiveOf (target.character ^ 1) = target
    rw [pow_one]
    exact target.primitiveOf_eq_self hprim

/-- The primitive auxiliary twists use the original target modulus, together with
the two primes of the window. Their definition is independent of the dyadic level. -/
noncomputable def selmerTwistedCharacter (target : BundledDirichletCharacter)
    (q d : ℕ+) [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime]
    (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3) (i : ℕ) (qSign dSign : Bool) :
    BundledDirichletCharacter := by
  let M := ((target.modulus : ℕ).lcm q).lcm d
  let _ : NeZero M := ⟨(Nat.lcm_pos (Nat.lcm_pos target.modulus.pos q.pos) d.pos).ne'⟩
  have ht : (target.modulus : ℕ) ∣ M :=
    dvd_trans (Nat.dvd_lcm_left _ q) (Nat.dvd_lcm_left _ d)
  have hq : (q : ℕ) ∣ M := dvd_trans (Nat.dvd_lcm_right (target.modulus : ℕ) _) (Nat.dvd_lcm_left _ d)
  have hd : (d : ℕ) ∣ M := Nat.dvd_lcm_right _ _
  exact BundledDirichletCharacter.primitiveOf
    (DirichletCharacter.changeLevel ht (target.character ^ i) *
      DirichletCharacter.changeLevel hq (selmerQuadraticCharacter hq₄ ^ qSign.toNat) *
      DirichletCharacter.changeLevel hd (selmerQuadraticCharacter hd₄ ^ dSign.toNat))

/-- Primitive induction of a target power twisted at the first prime only. -/
noncomputable def selmerFirstTwistedCharacter (target : BundledDirichletCharacter)
    (q : ℕ+) [Fact (q : ℕ).Prime] (hq₄ : (q : ℕ) % 4 = 3) (i : ℕ) (qSign : Bool) :
    BundledDirichletCharacter := by
  let M := (target.modulus : ℕ).lcm q
  let _ : NeZero M := ⟨(Nat.lcm_pos target.modulus.pos q.pos).ne'⟩
  exact BundledDirichletCharacter.primitiveOf
    (DirichletCharacter.changeLevel (Nat.dvd_lcm_left _ _) (target.character ^ i) *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right _ _) (selmerQuadraticCharacter hq₄ ^ qSign.toNat))

theorem selmerTwistedCharacter_no_second_twist (target : BundledDirichletCharacter)
    (q d : ℕ+) [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime]
    (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3) (i : ℕ) (qSign : Bool) :
    selmerTwistedCharacter target q d hq₄ hd₄ i qSign false =
      selmerFirstTwistedCharacter target q hq₄ i qSign := by
  let M := (target.modulus : ℕ).lcm q
  let N := M.lcm d
  let _ : NeZero M := ⟨(Nat.lcm_pos target.modulus.pos q.pos).ne'⟩
  let _ : NeZero N := ⟨(Nat.lcm_pos (Nat.lcm_pos target.modulus.pos q.pos) d.pos).ne'⟩
  have hMN : M ∣ N := Nat.dvd_lcm_left _ _
  unfold selmerTwistedCharacter selmerFirstTwistedCharacter
  rw [← BundledDirichletCharacter.primitiveOf_changeLevel hMN]
  simp only [Bool.toNat_false, pow_zero, map_one, mul_one, map_mul,
    ← DirichletCharacter.changeLevel_trans]

theorem selmerFirstTwistedCharacter_no_twist (target : BundledDirichletCharacter)
    (q : ℕ+) [Fact (q : ℕ).Prime] (hq₄ : (q : ℕ) % 4 = 3) (i : ℕ) :
    selmerFirstTwistedCharacter target q hq₄ i false = selmerFixedCharacter target i := by
  let _ : NeZero (target.modulus : ℕ) := ⟨target.modulus.pos.ne'⟩
  unfold selmerFirstTwistedCharacter selmerFixedCharacter
  simp only [Bool.toNat_false, pow_zero, map_one, mul_one,
    BundledDirichletCharacter.primitiveOf_changeLevel]

theorem selmerHostInducingCharacter_eq_twistedCharacter
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime]
    (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
    (i : ℕ) (qSign dSign : Bool) :
    selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
      (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm
      (selmerSurvivor target e i qSign dSign) =
      selmerTwistedCharacter target q d hq₄ hd₄ i qSign dSign := by
  let N := selmerHostModulus target e q d
  let M := ((target.modulus : ℕ).lcm q).lcm d
  let _ : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let _ : NeZero M := ⟨(Nat.lcm_pos (Nat.lcm_pos target.modulus.pos q.pos) d.pos).ne'⟩
  have ht : (target.modulus : ℕ) ∣ selmerBaseModulus target e := Nat.dvd_lcm_right _ _
  have hMN : M ∣ N := Nat.lcm_dvd_lcm_of_dvd_left d (Nat.lcm_dvd_lcm_of_dvd_left q ht)
  unfold selmerHostInducingCharacter selmerTwistedCharacter
  rw [selmerHostDirichlet_eq_target_pow_mul_quadratic target e q d hq₄ hd₄ hq hd _ i qSign dSign
    (selmerSurvivor_apply target e i qSign dSign), ← BundledDirichletCharacter.primitiveOf_changeLevel hMN]
  simp only [map_mul, ← DirichletCharacter.changeLevel_trans]

end Riemann
