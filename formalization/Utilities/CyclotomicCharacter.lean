module

public import Utilities.CyclotomicFrobenius
public import Utilities.CyclotomicInertia

@[expose] public section

open IsCyclotomicExtension
open scoped NumberField Classical

namespace Utilities

/-- A cyclotomic character is trivial on inertia at `p` precisely when its
primitive conductor is prime to `p`. -/
theorem cyclotomic_character_trivialOnInertia_iff {R : Type*} [CommRing R] [Nontrivial R]
    {n p : ℕ} [NeZero n] [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (χ : DirichletCharacter R n) :
    (∀ σ ∈ P.inertia (K ≃ₐ[ℚ] K), χ (Rat.galEquivZMod n K σ) = 1) ↔
      ¬ p ∣ χ.conductor := by
  let γ := Rat.galEquivZMod n K
  let hdiv := Nat.ordCompl_dvd n p
  have hker : (∀ σ ∈ P.inertia (K ≃ₐ[ℚ] K), χ (γ σ) = 1) ↔
      (ZMod.unitsMap hdiv).ker ≤ χ.toUnitHom.ker := by
    rw [show (ZMod.unitsMap hdiv).ker = (P.inertia (K ≃ₐ[ℚ] K)).map γ.toMonoidHom from
      (cyclotomic_inertia_map_eq_ordCompl_ker (p := p) K P).symm]
    constructor
    · intro h w hw
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hw
      change χ.toUnitHom (γ σ) = 1
      apply Units.ext
      simpa only [MulChar.coe_toUnitHom, Units.val_one] using h σ hσ
    · intro h σ hσ
      have hu : χ.toUnitHom (γ σ) = 1 := h (Subgroup.mem_map_of_mem γ.toMonoidHom hσ)
      simpa only [MulChar.coe_toUnitHom, Units.val_one] using
        congrArg (fun z : Rˣ => (z : R)) hu
  rw [hker, ← DirichletCharacter.factorsThrough_iff_ker_unitsMap hdiv,
    ← χ.mem_conductorSet_iff, χ.mem_conductorSet_iff_conductor_dvd hdiv]
  exact ⟨fun h hpd => Nat.not_dvd_ordCompl Fact.out (NeZero.ne n) (hpd.trans h),
    Nat.dvd_ordCompl_of_dvd_not_dvd χ.conductor_dvd_level⟩

/-- The cyclotomic lift of a Dirichlet character is trivial on automorphisms
fixing the roots of unity of its primitive conductor. -/
theorem cyclotomic_character_eq_one_of_fixes_conductor_roots {R : Type*} [CommRing R]
    {n : ℕ} [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (χ : DirichletCharacter R n) (σ : Gal(K/ℚ))
    (hfix : ∀ z : K, z ^ χ.conductor = 1 → σ z = z) :
    χ (Rat.galEquivZMod n K σ) = 1 := by
  let d := χ.conductor
  let γ := Rat.galEquivZMod n K σ
  let _ : NeZero d := ⟨χ.conductor_ne_zero⟩
  obtain ⟨j, hj⟩ : d ∣ n := χ.conductor_dvd_level
  have hj₀ : j ≠ 0 := by
    intro h
    exact NeZero.ne n (by simp [hj, h])
  let z := IsCyclotomicExtension.zeta n ℚ K ^ j
  have hz : IsPrimitiveRoot z d := by
    have h := (zeta_spec n ℚ K).pow_of_dvd hj₀ (show j ∣ n from ⟨d, hj.trans (mul_comm _ _)⟩)
    have he : n / j = d := by rw [hj, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hj₀)]
    exact he ▸ h
  have hzn : z ^ n = 1 := by rw [hj, pow_mul, hz.pow_eq_one, one_pow]
  have hγ : z ^ (γ : ZMod n).val = z ^ (1 : ℕ) := by
    rw [← Rat.galEquivZMod_apply_of_pow_eq n K σ hzn, hfix z hz.pow_eq_one, pow_one]
  have hc : ZMod.cast (γ : ZMod n) = (1 : ZMod d) := by
    rw [ZMod.cast_eq_val, ← (Nat.cast_one : ((1 : ℕ) : ZMod d) = 1),
      ZMod.natCast_eq_natCast_iff']
    rwa [(hz.isOfFinOrder (NeZero.ne d)).pow_inj_mod, ← hz.eq_orderOf] at hγ
  have hval := χ.primitiveCharacter.changeLevel_eq_cast_of_dvd χ.conductor_dvd_level γ
  rw [χ.changeLevel_primitiveCharacter, hc, map_one] at hval
  exact hval

/-- The primitive character's prime-power coefficient is the Frobenius
value to the prescribed power when inertia is trivial, and zero otherwise. -/
theorem cyclotomic_primitiveCharacter_primePow {n p : ℕ} [NeZero n] [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (χ : DirichletCharacter ℂ n) {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ P)
    {k : ℕ} (hk : 0 < k) :
    χ.primitiveCharacter (((p ^ k : ℕ) : ZMod χ.conductor)) =
      if ∀ τ ∈ P.inertia (K ≃ₐ[ℚ] K), χ (Rat.galEquivZMod n K τ) = 1 then
        χ (Rat.galEquivZMod n K σ) ^ k else 0 := by
  classical
  let γ := Rat.galEquivZMod n K
  have hp : p.Prime := Fact.out
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simp only [cyclotomic_character_trivialOnInertia_iff (p := p) K P χ, Nat.cast_pow, map_pow]
  by_cases h : p ∣ χ.conductor
  · have hnonunit : ¬ IsUnit (p : ZMod χ.conductor) :=
      (ZMod.isUnit_iff_coprime p χ.conductor).not.mpr fun hcop =>
        (hp.coprime_iff_not_dvd.mp hcop) h
    rw [ite_eq_right (not_not_intro h), MulChar.map_nonunit _ hnonunit, zero_pow hk.ne']
  · have hcop := hp.coprime_iff_not_dvd.mpr h
    have hu := cyclotomic_frobenius_unitsMap_eq K P hσ χ.conductor_dvd_level hcop
    have hcast : ZMod.cast (γ σ : ZMod n) = (p : ZMod χ.conductor) := by
      rw [← ZMod.unitsMap_val χ.conductor_dvd_level, hu, ZMod.coe_unitOfCoprime]
    have hvalue := χ.primitiveCharacter.changeLevel_eq_cast_of_dvd χ.conductor_dvd_level (γ σ)
    rw [χ.changeLevel_primitiveCharacter, hcast] at hvalue
    rw [ite_eq_left h, hvalue]

end Utilities
