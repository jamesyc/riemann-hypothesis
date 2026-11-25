module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Utilities.AbsoluteCyclotomicInertia

@[expose] public section

namespace Utilities

variable {R : Type*} [CommRing R] [IsDomain R]
variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N]

omit [NeZero N] in
/-- A primitive root retains its order under residue reduction when its
order is prime to the residue characteristic. -/
theorem isPrimitiveRoot_residue_of_not_dvd (red : R →+* ZMod p) (hpN : ¬ p ∣ N)
    {ζ : R} (hζ : IsPrimitiveRoot ζ N) : IsPrimitiveRoot (red ζ) N := by
  let P := RingHom.ker red
  let _ : P.IsPrime := RingHom.ker_isPrime red
  have hN : (N : R) ∉ P := by
    change ¬ red (N : R) = 0
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact hpN
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun j hj => hζ.dvd_of_pow_eq_one j ?_⟩
  apply eq_of_pow_eq_one_of_sub_mem_prime P hN
  · rw [← pow_mul, mul_comm j N, pow_mul, hζ.pow_eq_one, one_pow]
  · exact one_pow _
  · change red (ζ ^ j - 1) = 0
    rw [map_sub, map_pow, hj, map_one, sub_self]

/-- A power character into the residue field lifts on its unit
values to roots of unity of the corresponding prime-to-characteristic order. -/
theorem exists_mulChar_of_residue_power (red : R →+* ZMod p) (hpN : ¬ p ∣ N)
    {ζ : R} (hζ : IsPrimitiveRoot ζ N) (d e : ℕ) (hd : p - 1 = N * d) (he : 0 < d * e) :
    ∃ χ : MulChar (ZMod p) R, (∀ x, red (χ x) = x ^ (d * e)) ∧
      ∀ x ≠ 0, (χ x) ^ N = 1 := by
  classical
  let P := RingHom.ker red
  let _ : P.IsPrime := RingHom.ker_isPrime red
  have hN : (N : R) ∉ P := by
    change ¬ red (N : R) = 0
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact hpN
  let f := Units.map red.toMonoidHom
  let F : rootsOfUnity N R →* rootsOfUnity N (ZMod p) :=
    (f.comp (rootsOfUnity N R).subtype).codRestrict _ (fun x =>
      map_rootsOfUnity f N (Subgroup.mem_map_of_mem f x.property))
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    apply eq_of_pow_eq_one_of_sub_mem_prime P hN
    · exact (mem_rootsOfUnity' _ _).mp x.property
    · exact (mem_rootsOfUnity' _ _).mp y.property
    · change red ((x.val : R) - (y.val : R)) = 0
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun z : rootsOfUnity N (ZMod p) => (z.val : ZMod p)) hxy
  let u := (hζ.isUnit (NeZero.ne N)).unit
  have hu : IsPrimitiveRoot u N := hζ.isUnit_unit (NeZero.ne N)
  have hur : IsPrimitiveRoot (f u) N := by
    apply IsPrimitiveRoot.of_map_of_injective (f := Units.coeHom (ZMod p)) _ Units.val_injective
    have hbar := isPrimitiveRoot_residue_of_not_dvd p N red hpN hζ
    change IsPrimitiveRoot (red (u : R)) N
    rw [show (u : R) = ζ from IsUnit.unit_spec _]
    exact hbar
  have hmap : (rootsOfUnity N R).map f = rootsOfUnity N (ZMod p) := by
    rw [← hu.zpowers_eq, MonoidHom.map_zpowers, hur.zpowers_eq]
  have hsurj : Function.Surjective F := by
    intro y
    have hy : y.val ∈ (rootsOfUnity N R).map f := by
      rw [hmap]
      exact y.property
    obtain ⟨x, hx, heq⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext heq⟩
  let eqv := MulEquiv.ofBijective F ⟨hF, hsurj⟩
  let w : (ZMod p)ˣ →* rootsOfUnity N (ZMod p) := (powMonoidHom (d * e)).codRestrict _ (fun x => by
    apply (mem_rootsOfUnity _ _).mpr
    change (x ^ (d * e)) ^ N = 1
    rw [← pow_mul, show d * e * N = (p - 1) * e by rw [hd]; ring, pow_mul,
      ZMod.units_pow_card_sub_one_eq_one, one_pow])
  let χ := MulChar.ofUnitHom ((rootsOfUnity N R).subtype.comp (eqv.symm.toMonoidHom.comp w))
  refine ⟨χ, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · rw [hx, χ.map_zero, map_zero, zero_pow he.ne']
    · let z : (ZMod p)ˣ := Units.mk0 x hx
      change red (χ (z : ZMod p)) = (z : ZMod p) ^ (d * e)
      rw [show χ (z : ZMod p) = ((eqv.symm (w z)).val : R) from MulChar.ofUnitHom_coe _ _]
      exact congrArg (fun y : rootsOfUnity N (ZMod p) => (y.val : ZMod p)) (eqv.apply_symm_apply (w z))
  · intro x hx
    let z : (ZMod p)ˣ := Units.mk0 x hx
    change χ (z : ZMod p) ^ N = 1
    rw [show χ (z : ZMod p) = ((eqv.symm (w z)).val : R) from MulChar.ofUnitHom_coe _ _]
    exact (mem_rootsOfUnity' _ _).mp (eqv.symm (w z)).property

end Utilities
