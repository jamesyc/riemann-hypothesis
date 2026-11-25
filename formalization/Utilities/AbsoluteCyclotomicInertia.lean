module

public import Utilities.PadicTateTwist
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

open scoped BigOperators NumberField

namespace Utilities

/-- Reduction modulo a prime is injective on roots of unity of order
prime to the residue characteristic, even for non-Noetherian domains. -/
theorem eq_of_pow_eq_one_of_sub_mem_prime {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) [P.IsPrime] {n : ℕ} (hn : (n : R) ∉ P) {x y : R}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  let q := Ideal.Quotient.mk P
  have hbar : q x = q y := Ideal.Quotient.eq.mpr hxy
  have hsum : (∑ j ∈ Finset.range n, x ^ j * y ^ (n - 1 - j)) = 0 := by
    have h := geom_sum₂_mul x y n
    rw [hx, hy, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hqsum := congrArg q hsum
  simp only [map_sum, map_mul, map_pow, hbar, map_zero] at hqsum
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      q y ^ j * q y ^ (n - 1 - j) = q y ^ (n - 1) := by
    rw [← pow_add]
    congr 1
    have hj' := Finset.mem_range.mp hj
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hqsum
  have hn₀ : n ≠ 0 := by intro h; subst n; exact hn (by simp)
  have hyq : q y ≠ 0 := by
    have h := (map_pow q y n).symm.trans (congrArg q hy)
    intro hzero
    rw [hzero, zero_pow hn₀, map_one] at h
    exact zero_ne_one h
  exact hn ((Ideal.Quotient.eq_zero_iff_mem).mp
    (show q (n : R) = 0 by rw [map_natCast]; exact
      (mul_eq_zero.mp hqsum).resolve_right (pow_ne_zero _ hyq)))

/-- Inertia on a field extension fixes roots whose order is invertible
modulo the prime. -/
theorem inertia_fixes_root_of_order_away (K L : Type*) [Field K] [Field L] [Algebra K L]
    {P : Ideal (𝓞 L)} [P.IsPrime] {n : ℕ} (hn : (n : 𝓞 L) ∉ P)
    {σ : Gal(L/K)} (hσ : σ ∈ P.inertia Gal(L/K))
    {x : L} (hx : x ^ n = 1) : σ x = x := by
  have hn₀ : n ≠ 0 := fun h => hn (by simp [h])
  have hInt : IsIntegral ℤ x := IsIntegral.of_pow (Nat.pos_of_ne_zero hn₀) (hx ▸ isIntegral_one)
  let y : 𝓞 L := ⟨x, hInt⟩
  have hy : y ^ n = 1 := NumberField.RingOfIntegers.ext hx
  have hσy : (σ • y) ^ n = 1 := by
    let g := MulSemiringAction.toRingAut Gal(L/K) (𝓞 L) σ
    change g y ^ n = 1
    rw [← map_pow, hy, map_one]
  have hEq := eq_of_pow_eq_one_of_sub_mem_prime P hn hσy hy ((Ideal.mem_inertia.mp hσ) y)
  exact congrArg (fun z : 𝓞 L => (z : L)) hEq

/-- An inertia automorphism away from a prime fixes every root of unity
of prime-power order for that prime. -/
theorem inertia_fixes_primePow_root (K L : Type*) [Field K] [Field L] [Algebra K L]
    {ℓ : ℕ} {P : Ideal (𝓞 L)} [P.IsPrime] (hℓ : (ℓ : 𝓞 L) ∉ P)
    {σ : Gal(L/K)} (hσ : σ ∈ P.inertia Gal(L/K))
    (n : ℕ) {x : L} (hx : x ^ (ℓ ^ n) = 1) : σ x = x := by
  have hn : ((ℓ ^ n : ℕ) : 𝓞 L) ∉ P := by
    rw [Nat.cast_pow]
    exact fun h => hℓ ((inferInstance : P.IsPrime).mem_of_pow_mem n h)
  exact inertia_fixes_root_of_order_away K L hn hσ hx

/-- A Galois automorphism in inertia away from ℓ fixes every ℓ-power root of unity. -/
theorem absoluteInertia_fix_pPower_root (F : Type) [Field F] [NumberField F]
    {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 (AlgebraicClosure F))} [P.IsPrime]
    (hℓ : (ℓ : 𝓞 (AlgebraicClosure F)) ∉ P)
    {σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F}
    (hσ : σ ∈ P.inertia (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
    (n : ℕ) {x : AlgebraicClosure F} (hx : x ^ (ℓ ^ n) = 1) : σ x = x :=
  inertia_fixes_primePow_root F (AlgebraicClosure F) hℓ hσ n hx

/-- The ℓ-adic cyclotomic character on a common closure is trivial on
inertia away from ℓ. -/
theorem cyclotomicCharacter_eq_one_of_mem_inertia (K L : Type*) [Field K] [Field L] [Algebra K L]
    (ℓ : ℕ) [Fact ℓ.Prime] [∀ n, HasEnoughRootsOfUnity L (ℓ ^ n)]
    {P : Ideal (𝓞 L)} [P.IsPrime] (hℓ : (ℓ : 𝓞 L) ∉ P)
    {σ : Gal(L/K)} (hσ : σ ∈ P.inertia Gal(L/K)) :
    cyclotomicCharacter L ℓ σ.toRingEquiv = 1 := by
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [Units.val_one, map_one, cyclotomicCharacter.toZModPow]
  by_cases hzero : n = 0
  · subst n
    change (_ : ZMod 1) = 1
    exact Subsingleton.elim _ _
  · let _ : Fact (1 < ℓ ^ n) := ⟨one_lt_pow₀ (Fact.out : ℓ.Prime).one_lt hzero⟩
    symm
    apply modularCyclotomicCharacter.unique
    intro t ht
    rw [ZMod.val_one, pow_one]
    exact inertia_fixes_primePow_root K L hℓ hσ n ((mem_rootsOfUnity' _ _).mp ht)

theorem cyclotomicCharacter_eq_one_of_mem_absoluteInertia (F : Type)
    [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime]
    {P : Ideal (𝓞 (AlgebraicClosure F))} [P.IsPrime]
    (hℓ : (ℓ : 𝓞 (AlgebraicClosure F)) ∉ P)
    {σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F}
    (hσ : σ ∈ P.inertia (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) :
    cyclotomicCharacter (AlgebraicClosure F) ℓ σ.toRingEquiv = 1 :=
  cyclotomicCharacter_eq_one_of_mem_inertia F (AlgebraicClosure F) ℓ hℓ hσ

theorem padicTateScalarIn_eq_one_of_mem_inertia (K L : Type) [Field K] [Field L] [Algebra K L]
    (ℓ : ℕ) [Fact ℓ.Prime] [∀ n, HasEnoughRootsOfUnity L (ℓ ^ n)] (i : ℕ)
    {P : Ideal (𝓞 L)} [P.IsPrime] (hℓ : (ℓ : 𝓞 L) ∉ P)
    {σ : Gal(L/K)} (hσ : σ ∈ P.inertia Gal(L/K)) :
    padicTateScalarIn K L ℓ i σ = 1 := by
  change padicTateScalarOnAut L ℓ i σ.toRingEquiv = 1
  simp [padicTateScalarOnAut, cyclotomicCharacter_eq_one_of_mem_inertia K L ℓ hℓ hσ]

theorem padicTateScalar_eq_one_of_mem_absoluteInertia (F : Type) [Field F] [NumberField F]
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)
    {P : Ideal (𝓞 (AlgebraicClosure F))} [P.IsPrime]
    (hℓ : (ℓ : 𝓞 (AlgebraicClosure F)) ∉ P)
    {σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F}
    (hσ : σ ∈ P.inertia (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) :
    padicTateScalar F ℓ i σ = 1 :=
  padicTateScalarIn_eq_one_of_mem_inertia F (AlgebraicClosure F) ℓ i hℓ hσ

end Utilities
