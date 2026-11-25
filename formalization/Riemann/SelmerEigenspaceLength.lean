module

public import Riemann.SelmerCohomology
public import Utilities.InvolutionEigenspaces
public import Utilities.PadicModuleCard

@[expose] public section

open Utilities

namespace Riemann

theorem primaryCardLength_congr {A B : Type*} (ℓ : ℕ) (e : A ≃ B) :
    primaryCardLength ℓ A = primaryCardLength ℓ B := by
  classical
  have hfinite : Finite A ↔ Finite B :=
    ⟨fun _ => Finite.of_injective e.symm e.symm.injective, fun _ => Finite.of_injective e e.injective⟩
  by_cases hA : Finite A
  · rw [primaryCardLength, primaryCardLength, ite_eq_left hA, ite_eq_left (hfinite.mp hA), Nat.card_congr e]
  · rw [primaryCardLength, primaryCardLength, ite_eq_right hA, ite_eq_right (mt hfinite.mpr hA)]

/-- The finite-cardinality convention agrees with Mathlib's composition length
on every module over the ℓ-adic integers. -/
theorem primaryCardLength_eq_moduleLength (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*)
    [AddCommGroup M] [Module ℤ_[ℓ] M] :
    primaryCardLength ℓ M = Module.length ℤ_[ℓ] M := by
  classical
  by_cases h : IsFiniteLength ℤ_[ℓ] M
  · have : Finite M := (padicModule_isFiniteLength_iff_finite ℓ M).mp h
    have hcard := card_eq_padic_prime_pow_of_isFiniteLength ℓ M h
    rw [primaryCardLength_of_card_pow ℓ _ (Fact.out : ℓ.Prime).one_lt _ hcard]
    exact ENat.natCast_toNat (Module.length_ne_top_iff.mpr h)
  · have hnfinite : ¬ Finite M := mt (padicModule_isFiniteLength_iff_finite ℓ M).mpr h
    rw [primaryCardLength, ite_eq_right hnfinite]
    exact (not_ne_iff.mp (mt Module.length_ne_top_iff.mp h)).symm

/-- The logarithmic cardinality convention is additive on products of
ℓ-adic modules, with infinite length recorded by `⊤`. -/
theorem primaryCardLength_prod (ℓ : ℕ) [Fact ℓ.Prime]
    (A B : Type*) [AddCommGroup A] [AddCommGroup B] [Module ℤ_[ℓ] A] [Module ℤ_[ℓ] B] :
    primaryCardLength ℓ (A × B) = primaryCardLength ℓ A + primaryCardLength ℓ B := by
  simp only [primaryCardLength_eq_moduleLength, Module.length_prod]
  rfl

/-- At an odd prime, the eigenspaces of an involution have additive length.
The twist parity can exchange the order of these two summands. -/
theorem primaryCardLength_of_involution (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2)
    {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    (T : Module.End ℤ_[ℓ] M) (hT : Function.Involutive T) :
    primaryCardLength ℓ M =
      primaryCardLength ℓ (T.eigenspace 1) + primaryCardLength ℓ (T.eigenspace (-1)) := by
  have htwo : IsUnit (2 : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr
    ((PadicInt.norm_natCast_eq_one_iff (n := 2)).mpr
      ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hℓ))
  let hcompl := involution_isCompl_eigenspaces T hT htwo
  let e := (T.eigenspace 1).prodEquivOfIsCompl (T.eigenspace (-1)) hcompl
  exact (primaryCardLength_congr ℓ e.symm.toEquiv).trans (primaryCardLength_prod ℓ _ _)

end Riemann
