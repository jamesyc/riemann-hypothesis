module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Utilities.RelationTransfer

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace Riemann

/-- The proportionality step in Theorem 14.15 for the actual row, column,
and Poincaré maps. The relation-transfer hypothesis is the conclusion of
combining the seesaw relation in Hypothesis 14.10 with Corollary 14.7. -/
theorem exists_besselIdentity_of_relationTransfer
    {X V Y C H : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : V →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (s : Y →ₛₗ[starRingEnd ℂ] H)
    (J : V →ₗ[ℂ] C) (P : C →ₗ[ℂ] H) (R : H ≃ₗᵢ[ℂ] H)
    (ι : V × Y → X) (period : X → ℂ) (row : X → H) (column : X → C) {r : ℂ} (hr : r ≠ 0)
    (hperiodValue : ∀ z y, period (ι (z, y)) = B z y)
    (hrow : ∀ z y, row (ι (z, y)) = s y)
    (hcolumn : ∀ z y, column (ι (z, y)) = r • J z)
    (ht : ∀ n (x : Fin n → X) (a : Fin n → ℂ), (∑ i, a i * period (x i)) = 0 →
      (∑ i, a i * ⟪R (row (x i)), P (column (x i))⟫_ℂ) = 0)
    {x₀ : X} (hnonzero : ⟪R (row x₀), P (column x₀)⟫_ℂ ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ (z : V) (y : Y), B z y = a * ⟪R (s y), P (J z)⟫_ℂ := by
  obtain ⟨c, hc, h⟩ := Utilities.exists_scalar_of_linearRelationTransfer period
    (fun x => ⟪R (row x), P (column x)⟫_ℂ) ht hnonzero
  refine ⟨c⁻¹ * r, mul_ne_zero (inv_ne_zero hc) hr, fun z y => ?_⟩
  have he := h (ι (z, y))
  simp only [hrow, hcolumn, hperiodValue, map_smul, inner_smul_right] at he
  calc
    _ = c⁻¹ * (c * B z y) := by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ = _ := by rw [← he, mul_assoc]

end Riemann
