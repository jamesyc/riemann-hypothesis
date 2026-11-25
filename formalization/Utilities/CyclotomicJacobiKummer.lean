module

public import Utilities.CyclotomicJacobiRadicand
public import Utilities.KummerInertiaEvaluation
import Utilities.RationalPrime
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

open NumberField IsCyclotomicExtension IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors

namespace Utilities

variable (N : ℕ) [NeZero N] (E : Type) [Field E] [NumberField E]
  [IsCyclotomicExtension {N} ℚ E]

local notation "χ" => MulEquiv.symm (Rat.galEquivZMod N E)

/-- The initial Jacobi radicand gives a family of Kummer characters
whose values at one inertia element are the signed floor exponents. -/
theorem exists_initialJacobiKummerCharacters
    {L : Type} [Field L] [Algebra E L] [IsGalois E L] [IsAlgClosed L]
    (p : ℕ) [Fact p.Prime] {ℓ r : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (hlevel : ℓ ^ (r + 1) ∣ N) (v : HeightOneSpectrum (𝓞 E))
    (red : 𝓞 E →+* ZMod p) (hred : RingHom.ker red = v.asIdeal) (hpN : ¬ p ∣ N)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal] (b : ℕ) :
    ∃ (X ζ : Eˣ), X * Units.map (χ (-1)).toRingEquiv.toMonoidHom X = 1 ∧
      IsPrimitiveRoot (ζ : E) (ℓ ^ (r + 1)) ∧
      ∃ t ∈ P.inertia Gal(L/E), ∃ κ : (ZMod N)ˣ → (Additive Gal(L/E) →+ ZMod (ℓ ^ (r + 1))),
        ∀ s : (ZMod N)ˣ, IsLocallyConstant (fun g => κ s (Additive.ofMul g)) ∧
          κ s (Additive.ofMul t) = (cyclotomicSignedFloor N b s.val : ZMod (ℓ ^ (r + 1))) ∧
          ∃ β : L, β ^ (ℓ ^ (r + 1)) = algebraMap E L ((χ s) (X : E)) ∧
            ∀ g : Gal(L/E), g β = (algebraMap E L (ζ : E)) ^ (κ s (Additive.ofMul g)).val * β := by
  let M := ℓ ^ (r + 1)
  have hM : M ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  let _ : NeZero M := ⟨hM⟩
  obtain ⟨d, hd⟩ := hlevel
  let z := zeta N ℚ E ^ d
  have hz : IsPrimitiveRoot z M :=
    (zeta_spec N ℚ E).pow (NeZero.pos N) (hd.trans (mul_comm M d))
  let ζ : Eˣ := Units.mk0 z (hz.ne_zero hM)
  let _ : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_intPrime_of_residueMap E p red v hred
  let _ : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  have hmP : (M : 𝓞 L) ∉ P := by
    intro h
    have hdvd := (natCast_mem_iff_dvd_of_liesOver_rationalPrime P p M).mp h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd))
  obtain ⟨X, hX, hcount⟩ := exists_cyclotomicJacobiRadicand N E p red v hred hpN b
  obtain ⟨u, -, hu⟩ := exists_rat_prime_unit_of_cyclotomic_degreeOne N E p red v hred hpN
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E L (u : E)) (Nat.pos_of_ne_zero hM)
  obtain ⟨t, ht, htρ⟩ := exists_inertia_acts_on_primePower_radical hz v u hu P hρ
  have hf (s : (ZMod N)ˣ) :
      ∃ κ : Additive Gal(L/E) →+ ZMod M,
        IsLocallyConstant (fun g => κ (Additive.ofMul g)) ∧
          κ (Additive.ofMul t) = (cyclotomicSignedFloor N b s.val : ZMod M) ∧
          ∃ β : L, β ^ M = algebraMap E L ((χ s) (X : E)) ∧
            ∀ g : Gal(L/E), g β = (algebraMap E L z) ^ (κ (Additive.ofMul g)).val * β := by
    let a := Units.map (χ s).toRingEquiv.toMonoidHom X
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E L (a : E)) (Nat.pos_of_ne_zero hM)
    obtain ⟨κ, hκlc, hκ⟩ := exists_zmodCharacter_of_radical hz a hβ
    have he := zmodCharacter_inertia_value_eq_prime_exponent hz v P hmP a u hu hβ hρ t ht htρ κ hκ
    rw [hcount s] at he
    exact ⟨κ, hκlc, he, β, hβ, hκ⟩
  choose κ hκ using hf
  exact ⟨X, ζ, hX, hz, t, ht, κ, hκ⟩

end Utilities
