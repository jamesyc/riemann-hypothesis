module

public import Riemann.SelmerCohomology
public import Utilities.CyclotomicLayer
public import Utilities.PadicCokernelGrowth

@[expose] public section

open Utilities

namespace Riemann

/-- The fixed layer used to compare the lengths at every depth in a tower. -/
def selmerCyclotomicReferenceDepth (ℓ R : ℕ) : ℕ := Nat.log ℓ R + 3

/-- Descent through the cyclotomic tower bounds the length at an arbitrary
depth by the length at the reference layer plus the cost of excess depth. -/
def SelmerCyclotomicTowerDepthBound (F : Type) [Field F] [NumberField F] (ℓ R : ℕ) : Prop :=
  ∀ (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra F L₀],
    IsPrimePowerCyclotomicLayer ℓ (selmerCyclotomicReferenceDepth ℓ R) F L₀ →
    ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [Algebra F L],
      IsPrimePowerCyclotomicLayer ℓ m F L → ∀ i : ℕ, 1 ≤ i →
        numberFieldSelmerLengths L ℓ i ≤ numberFieldSelmerLengths L₀ ℓ i +
          ((R * (m - selmerCyclotomicReferenceDepth ℓ R) : ℕ) : WithTop ℕ)

/-- The Selmer groups through the tower are presented by the twisted
cyclotomic generator on one p-adic module with at most `R` generators. -/
def SelmerCyclotomicCokernelPresentation (F : Type) [Field F] [NumberField F]
    (ℓ R : ℕ) (hℓ : ℓ.Prime) : Prop :=
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℤ_[ℓ] X)
      (π : (Fin R → ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] X) (γ : Module.End ℤ_[ℓ] X) (u : ℤ_[ℓ]),
    Function.Surjective π ∧ IsNilpotent (padicEndModPrime ℓ X γ - 1) ∧
      (ℓ : ℤ_[ℓ]) ∣ u - 1 ∧
      ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [Algebra F L],
        IsPrimePowerCyclotomicLayer ℓ m F L → ∀ i : ℕ, 1 ≤ i →
          numberFieldSelmerLengths L ℓ i = padicCokernelLength (p := ℓ) (X := X) ((u ^ i • γ) ^ (ℓ ^ m) - 1)

/-- The growth step for the twisted generator gives the comparison to the
reference layer, uniformly for every twist. -/
theorem selmerCyclotomicTowerDepthBound_of_cokernelPresentation
    {F : Type} [Field F] [NumberField F] {ℓ R : ℕ} (hℓ : ℓ.Prime)
    (h : SelmerCyclotomicCokernelPresentation F ℓ R hℓ) :
    SelmerCyclotomicTowerDepthBound F ℓ R := by
  let _ : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨X, _, _, π, γ, u, hπ, hγ, hu, hlength⟩ := h
  intro L₀ _ _ _ hL₀ m L _ _ _ hL i hi
  have hui : (ℓ : ℤ_[ℓ]) ∣ u ^ i - 1 :=
    hu.trans (by simpa using sub_dvd_pow_sub_pow u 1 i)
  have hnil : IsNilpotent (padicEndModPrime ℓ X (u ^ i • γ) - 1) := by
    rw [padicEndModPrime_smul_of_dvd_sub_one γ hui]
    exact hγ
  rw [hlength _ L hL i hi, hlength _ L₀ hL₀ i hi]
  exact padicCokernelLength_primePower_le_of_isNilpotent π hπ (u ^ i • γ) hnil
    (selmerCyclotomicReferenceDepth ℓ R) (by unfold selmerCyclotomicReferenceDepth; omega) m

end Riemann
