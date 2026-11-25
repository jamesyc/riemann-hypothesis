module

public import Riemann.SelmerTwistFiniteDescent
import Utilities.KummerRadicalEquivariance
import Utilities.PadicTateFiniteRestriction

@[expose] public section

open Utilities DiscreteGaloisModule groupCohomology
open scoped TensorProduct IsMulCommutative

namespace Riemann

variable (F : Type) [Field F] [NumberField F] [IsAbelianGalois ℚ F]
  (ℓ : ℕ) [Fact ℓ.Prime] (i r : ℕ) (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S]
  (ψ : Gal(F/ℚ) →* Sˣ) (E : IntermediateField ℚ (AlgebraicClosure F))

local notation "Ω" => AlgebraicClosure F
local notation "T" => numberFieldSelmerSharedInverseTwist F ℓ i S ψ
local notation "δ" => numberFieldTwistNormalizationElement F
local notation "G" => Gal(Ω/ℚ)
local notation "D" => numberFieldSelmerRestrictionsIn ℚ Ω ℓ
local notation "C" => normalizedSelmerCocycles T D δ
local notation "L" => numberFieldSelmerSharedTwistArithmeticLayer F ℓ i S ψ r
local instance : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- A nonzero normalized twist cocycle detects an automorphism fixing
the auxiliary radical when the twist and cyclotomic characters differ
by a unit at some ambient automorphism. -/
theorem sharedTwistArithmeticLayer_exists_nonzero_on_radical_stabilizer
    [IsAbelianGalois ℚ E]
    (hψ : ∀ σ : Gal(Ω/E), ψ ((σ.restrictScalars ℚ).restrictNormal F) = 1)
    (hroot : ∀ ζ : Ω, ζ ^ (ℓ ^ r) = 1 → ζ ∈ E)
    (hodd : ℓ ≠ 2) (hparity : (ψ ((δ).restrictNormal F) : S) = (-1 : S) ^ (i + 1))
    (c : L) (hc : c ≠ 0)
    {a : ℕ} (ha : a ≠ 0) {β : Ω} (hβ : β ^ (ℓ ^ r) = (a : Ω))
    (s : G)
    (hsep : IsUnit ((((ψ (s.restrictNormal F))⁻¹ : Sˣ) : S) *
      algebraMap ℤ_[ℓ] S (padicTateScalarIn ℚ Ω ℓ i s) -
      algebraMap ℤ_[ℓ] S (cyclotomicCharacter Ω ℓ s.toRingEquiv).val)) :
    ∃ u : Gal(Ω/E), u β = β ∧ c.val.val (u.restrictScalars ℚ) ≠ 0 := by
  classical
  let R := sharedTwistArithmeticLayer_restriction F ℓ i S ψ r E hψ hroot
  let f := R c
  have ht (g : G) : (ℓ : S) ^ r • c.val.val g = 0 :=
    congrArg (fun d : C => d.val g) c.property.1
  have hβ₀ : β ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)] at hβ
    exact ha (Nat.cast_eq_zero.mp hβ.symm)
  have hbase (g : G) : g (β ^ (ℓ ^ r)) = β ^ (ℓ ^ r) := by rw [hβ, map_natCast]
  have hroots (g : Gal(Ω/E)) (z : Ω) (hz : z ^ (ℓ ^ r) = 1) : g z = z :=
    g.commutes (⟨z, hroot z hz⟩ : E)
  let ε := (cyclotomicCharacter Ω ℓ s.toRingEquiv).val
  let k := (PadicInt.toZModPow r ε).val
  have hs (z : Ω) (hz : z ^ (ℓ ^ r) = 1) : s z = z ^ k :=
    cyclotomicCharacter.spec ℓ s.toRingEquiv z hz
  have hnsmul (x : (T).rep) (hx : (ℓ : S) ^ r • x = 0) :
      k • x = algebraMap ℤ_[ℓ] S ε • x := by
    let y : S ⊗[ℤ_[ℓ]] PadicTateQuotient ℓ := x
    change k • y = algebraMap ℤ_[ℓ] S ε • y
    rw [IsScalarTower.algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℤ_[ℓ]]
    apply padicInt_smul_eq_of_toZModPow_eq ℓ (r := r)
    · rw [map_natCast, ZMod.natCast_zmod_val]
    · rw [← IsScalarTower.algebraMap_smul S, map_pow, map_natCast]
      exact hx
  have hconj (u : Gal(Ω/E)) :
      f (Additive.ofMul (relativeGaloisConj ℚ E Ω s u)) =
        ((((ψ (s.restrictNormal F))⁻¹ : Sˣ) : S) *
          algebraMap ℤ_[ℓ] S (padicTateScalarIn ℚ Ω ℓ i s)) • f (Additive.ofMul u) := by
    let v := relativeGaloisConj ℚ E Ω s u
    have hrel : v.restrictScalars ℚ = s * u.restrictScalars ℚ * s⁻¹ :=
      relativeGaloisConj_restrictScalars ℚ E Ω s u
    have hfix := sharedTwist_action_eq_self_of_fixes_roots F ℓ i S ψ r
      (v.restrictScalars ℚ) (hψ v) (hroots v) (c.val.val s) (ht s)
    rw [hrel] at hfix
    let d : cocycles₁ (T).rep := ⟨c.val.val, c.val.property.1.1.1⟩
    have hd := (T).cocycle_apply_conj_eq_of_fixed d s (u.restrictScalars ℚ) hfix
    rw [← hrel] at hd
    change f (Additive.ofMul v) = (T).rep.ρ s (f (Additive.ofMul u)) at hd
    rwa [numberFieldSelmerSharedInverseTwist_ρ F ℓ i S ψ s, LinearMap.smul_apply, one_apply_eq_self] at hd
  have hf : f ≠ 0 := fun h =>
    hc ((sharedTwistArithmeticLayer_restriction_injective F ℓ i S ψ r E hψ hroot hodd hparity)
      (h.trans (map_zero R).symm))
  exact exists_nonzero_on_radical_stabilizer_of_smul_conjugation f hf hβ₀ hbase hroots s hs
    hsep hconj (fun u => hnsmul _ (ht (u.restrictScalars ℚ)))

end Riemann
