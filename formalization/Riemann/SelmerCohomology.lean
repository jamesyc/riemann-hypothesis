module

public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Riemann.SelmerWindows
public import Utilities.PadicTateTwist

@[expose] public section

open Utilities
open scoped NumberField Pointwise

namespace Riemann

/-- The restrictions in Definition 17.2. Impose the conditions at every
prolongation of the finite place to the algebraic closure. -/
noncomputable def numberFieldSelmerRestrictions (F : Type) [Field F] [NumberField F]
    (ℓ : ℕ) : Set (Subgroup (Field.absoluteGaloisGroup F)) := by
  change Set (Subgroup (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  exact {D | ∃ (v : NumberField.FinitePlace F) (P : Ideal (𝓞 (AlgebraicClosure F))),
    P.IsPrime ∧
    P.comap (NumberField.RingOfIntegers.mapRingHom (algebraMap F (AlgebraicClosure F))) =
      v.maximalIdeal.asIdeal ∧
    (D = P.inertia (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ∨
      ((ℓ : 𝓞 F) ∈ v.maximalIdeal.asIdeal ∧ D = MulAction.stabilizer
        (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) P))}

/-- The relaxed classes are unramified outside the primes over `ℓ`. -/
noncomputable def numberFieldRelaxedSelmerRestrictions (F : Type) [Field F] [NumberField F]
    (ℓ : ℕ) : Set (Subgroup (Field.absoluteGaloisGroup F)) := by
  change Set (Subgroup (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  exact {D | ∃ (v : NumberField.FinitePlace F) (P : Ideal (𝓞 (AlgebraicClosure F))),
    (ℓ : 𝓞 F) ∉ v.maximalIdeal.asIdeal ∧ P.IsPrime ∧
      P.comap (NumberField.RingOfIntegers.mapRingHom (algebraMap F (AlgebraicClosure F))) =
        v.maximalIdeal.asIdeal ∧ D = P.inertia (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)}

theorem numberFieldRelaxedSelmerRestrictions_subset (F : Type) [Field F] [NumberField F]
    (ℓ : ℕ) :
    numberFieldRelaxedSelmerRestrictions F ℓ ⊆ numberFieldSelmerRestrictions F ℓ := by
  intro D hD
  obtain ⟨v, P, _, hp, hv, hD'⟩ := hD
  exact ⟨v, P, hp, hv, Or.inl hD'⟩

/-- The Selmer kernel with only the unramified conditions away from ℓ. -/
noncomputable abbrev numberFieldRelaxedSelmerKernel (F : Type) [Field F] [NumberField F]
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :=
  (padicTateTwist F ℓ i).selmerKernel (numberFieldRelaxedSelmerRestrictions F ℓ)

/-- For a finite ℓ-primary group, length is log base ℓ of its cardinality. -/
noncomputable def primaryCardLength (ℓ : ℕ) (A : Type*) : WithTop ℕ := by
  classical
  exact if Finite A then (Nat.log ℓ (Nat.card A) : WithTop ℕ) else ⊤

theorem primaryCardLength_ne_top_iff (ℓ : ℕ) (A : Type*) :
    primaryCardLength ℓ A ≠ ⊤ ↔ Finite A := by
  classical
  by_cases h : Finite A <;> simp [primaryCardLength, h]

theorem primaryCardLength_of_card_pow (ℓ n : ℕ) (hℓ : 1 < ℓ) (A : Type*) [Finite A]
    (hcard : Nat.card A = ℓ ^ n) : primaryCardLength ℓ A = n := by
  classical
  rw [primaryCardLength, ite_eq_left (inferInstance : Finite A), hcard, Nat.log_pow hℓ]

/-- The weighted-window length model from the actual Selmer restriction kernels. -/
noncomputable def numberFieldSelmerLengths : NumberFieldSelmerLengths := by
  classical
  intro F _ _ ℓ i
  exact if hℓ : ℓ.Prime then
    letI : Fact ℓ.Prime := ⟨hℓ⟩
    primaryCardLength ℓ ((padicTateTwist F ℓ i).selmerKernel (numberFieldSelmerRestrictions F ℓ))
  else ⊤

end Riemann
