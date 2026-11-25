module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient

@[expose] public section

open groupCohomology

universe u

namespace Utilities

/-- The kernel of the modular cyclotomic character fixes every root of
its order. -/
theorem algEquiv_fixes_root_of_modularCyclotomic_eq_one {K L : Type*}
    [Field K] [Field L] [Algebra K L] (N : ℕ) [NeZero N] [HasEnoughRootsOfUnity L N]
    (hN : 1 < N) (σ : Gal(L/K))
    (hσ : modularCyclotomicCharacter L (HasEnoughRootsOfUnity.natCard_rootsOfUnity L N)
      σ.toRingEquiv = 1) {x : L} (hx : x ^ N = 1) : σ x = x := by
  let _ : Fact (1 < N) := ⟨hN⟩
  have hx₀ : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hx
    exact zero_ne_one hx
  let u : Lˣ := Units.mk0 x hx₀
  have hu : u ∈ rootsOfUnity N L := (mem_rootsOfUnity _ _).mpr (Units.ext hx)
  have h := modularCyclotomicCharacter.spec L (HasEnoughRootsOfUnity.natCard_rootsOfUnity L N)
    σ.toRingEquiv hu
  rwa [hσ, Units.val_one, ZMod.val_one, pow_one] at h

/-- Fixing the roots of order `N` and all prime-power roots for `p`
also fixes the roots at each level `N * p ^ m`. -/
theorem algEquiv_fixes_root_mul_prime_pow {K L : Type*}
    [Field K] [Field L] [Algebra K L] {N p : ℕ} (hN : N ≠ 0) (hp : p.Prime)
    (σ : Gal(L/K)) (hfix : ∀ ζ : L, ζ ^ N = 1 → σ ζ = ζ)
    (hprime : ∀ r (ζ : L), ζ ^ (p ^ r) = 1 → σ ζ = ζ)
    (m : ℕ) {ζ : L} (hζ : ζ ^ (N * p ^ m) = 1) : σ ζ = ζ := by
  let r := N.factorization p + m
  let a := p ^ r
  let b := ordCompl[p] N
  have hab : a * b = N * p ^ m := by
    calc
      a * b = p ^ m * (ordProj[p] N * b) := by
        dsimp only [a, r]
        rw [pow_add]
        ac_rfl
      _ = N * p ^ m := by rw [Nat.ordProj_mul_ordCompl_eq_self, Nat.mul_comm]
  have hcoprime : a.Coprime b := (Nat.coprime_ordCompl hp hN).pow_left r
  have hζne : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (mul_ne_zero hN (pow_ne_zero _ hp.ne_zero))] at hζ
    exact zero_ne_one hζ
  have hζa : (ζ ^ b) ^ a = 1 := by rw [← pow_mul, mul_comm b a, hab, hζ]
  have hζb : (ζ ^ a) ^ b = 1 := by rw [← pow_mul, hab, hζ]
  obtain ⟨k, hk⟩ := Nat.ordCompl_dvd N p
  have hζN : (ζ ^ a) ^ N = 1 := by rw [hk, pow_mul, hζb, one_pow]
  have ha : (σ ζ / ζ) ^ a = 1 := by
    rw [div_pow, ← map_pow σ, hfix _ hζN, div_self (pow_ne_zero _ hζne)]
  have hb : (σ ζ / ζ) ^ b = 1 := by
    rw [div_pow, ← map_pow σ, hprime r _ hζa, div_self (pow_ne_zero _ hζne)]
  have h := (pow_gcd_eq_one (a := σ ζ / ζ)).mpr ⟨ha, hb⟩
  rw [hcoprime.gcd_eq_one, pow_one] at h
  exact (div_eq_one_iff_eq hζne).mp h

/-- Taking the totient power makes an automorphism fix the roots of the
corresponding order. -/
theorem algEquiv_pow_totient_fixes_root {K L : Type*} [Field K] [Field L] [Algebra K L]
    (N : ℕ) [NeZero N] [HasEnoughRootsOfUnity L N] (hN : 1 < N)
    (σ : Gal(L/K)) {x : L} (hx : x ^ N = 1) : (σ ^ N.totient) x = x := by
  let χ := (modularCyclotomicCharacter L (HasEnoughRootsOfUnity.natCard_rootsOfUnity L N)).comp
    (MulSemiringAction.toRingAut Gal(L/K) L)
  have hcard : Nat.card (ZMod N)ˣ = N.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hχ : χ (σ ^ N.totient) = 1 := by
    rw [map_pow, ← hcard, pow_card_eq_one']
  exact algEquiv_fixes_root_of_modularCyclotomic_eq_one N hN _ hχ hx

/-- On a subgroup acting trivially on the coefficients, a cocycle that
vanishes on elements fixing the roots of order `N` is killed by `φ(N)`. -/
theorem totient_smul_cocycle_eq_zero_of_fixedRoots {K L A : Type u}
    [Field K] [Field L] [Algebra K L] [CommRing A]
    (N : ℕ) [NeZero N] [HasEnoughRootsOfUnity L N] (hN : 1 < N)
    (V : Rep.{u} A Gal(L/K)) (H : Subgroup Gal(L/K))
    (htriv : ∀ σ ∈ H, V.ρ σ = 1) (b : cocycles₁ V)
    (hzero : ∀ σ ∈ H, (∀ x : L, x ^ N = 1 → σ x = x) → b σ = 0)
    {σ : Gal(L/K)} (hσ : σ ∈ H) : N.totient • b σ = 0 := by
  have hpow (n : ℕ) : b (σ ^ n) = n • b σ := by
    induction n with
    | zero => rw [pow_zero, cocycles₁_map_one, zero_smul]
    | succ n ih =>
      have hc : b (σ ^ n * σ) = V.ρ (σ ^ n) (b σ) + b (σ ^ n) :=
        (mem_cocycles₁_iff b.val).mp b.property _ _
      rw [pow_succ, hc, htriv _ (H.pow_mem hσ n), one_apply_eq_self, ih, succ_nsmul, add_comm]
  rw [← hpow]
  exact hzero _ (H.pow_mem hσ _) fun _ hx => algEquiv_pow_totient_fixes_root N hN σ hx

end Utilities
