module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators Classical

namespace Utilities

/-- Pair the nodes with first coordinate zero with those with first coordinate
one, translating the second coordinate. Pairwise negatives sum to zero. -/
theorem sum_nodeWeights_eq_zero_of_pairing {H R : Type*} [AddGroup H] [Fintype H]
    [AddCommGroup R] (f : ZMod 2 × H → R) (h₀ : H)
    (hpair : ∀ h : H, f (1, h + h₀) = -f (0, h)) : (∑ ρ, f ρ) = 0 := by
  have hparts : (∑ ρ, f ρ) = (∑ h : H, f (0, h)) + (∑ h : H, f (1, h)) := by
    rw [Fintype.sum_prod_type]
    rw [← (ZMod.finEquiv 2).toEquiv.sum_comp (fun a : ZMod 2 => ∑ h : H, f (a, h))]
    change (∑ z : Fin 2, ∑ h : H, f (ZMod.finEquiv 2 z, h)) = _
    simp only [Fin.sum_univ_two, map_zero, map_one]
  have hshift : (∑ h : H, f (1, h + h₀)) = ∑ h : H, f (1, h) :=
    Equiv.sum_comp (Equiv.addRight h₀) (fun h : H => f (1, h))
  rw [hparts, ← hshift]
  simp only [hpair, Finset.sum_neg_distrib, add_neg_cancel]

noncomputable def modularNodeSum {I : Type*} [Fintype I] {W : ℕ}
    (κ : I → (ZMod W)ˣ) (weights : I → ℤ) : ZMod W :=
  ∑ ρ : I, (κ ρ : ZMod W) * (weights ρ : ZMod W)

theorem modularNodeSum_add {I : Type*} [Fintype I] {W : ℕ}
    (κ : I → (ZMod W)ˣ) (f g : I → ℤ) :
    modularNodeSum κ (fun ρ => f ρ + g ρ) = modularNodeSum κ f + modularNodeSum κ g := by
  simp only [modularNodeSum, Int.cast_add, mul_add, Finset.sum_add_distrib]

theorem modularNodeSum_const {I : Type*} [Fintype I] {W : ℕ}
    (κ : I → (ZMod W)ˣ) (a : ℤ) (hκ : (∑ ρ : I, (κ ρ : ZMod W)) = 0) :
    modularNodeSum κ (fun _ => a) = 0 := by
  unfold modularNodeSum
  rw [← Finset.sum_mul, hκ, zero_mul]

/-- Correct one base weight by a residue in `[0,W)` so that every
translated midpoint weight has weighted sum zero modulo W. -/
theorem exists_modular_node_base {I : Type*} [Fintype I] {W : ℕ} [NeZero W]
    (κ : I → (ZMod W)ˣ) (hκ : (∑ ρ : I, (κ ρ : ZMod W)) = 0)
    (raw : I → ℤ) (halfGap : ℤ) (chosen : I) :
    ∃ base : I → ℤ,
      (∀ ρ, ρ ≠ chosen → base ρ = raw ρ) ∧
      raw chosen ≤ base chosen ∧ base chosen < raw chosen + (W : ℤ) ∧
      ∀ j : ℕ, modularNodeSum κ (fun ρ => base ρ + (2 * (j : ℤ) + 1) * halfGap) = 0 := by
  classical
  let residual := modularNodeSum κ (fun ρ => raw ρ + halfGap)
  let shift : ZMod W := -(↑((κ chosen)⁻¹) : ZMod W) * residual
  let correction (ρ : I) : ℤ := if ρ = chosen then (shift.val : ℤ) else 0
  let base (ρ : I) : ℤ := raw ρ + correction ρ
  have hcancel : (κ chosen : ZMod W) * shift = -residual := by
    calc
      _ = -((κ chosen : ZMod W) * (↑((κ chosen)⁻¹) : ZMod W) * residual) := by
        dsimp [shift]
        ring
      _ = _ := by simp
  have hcorrection : modularNodeSum κ correction = -residual := by
    have hterm (ρ : I) : (κ ρ : ZMod W) * (correction ρ : ZMod W) =
        if ρ = chosen then (κ chosen : ZMod W) * shift else 0 := by
      by_cases hρ : ρ = chosen <;> simp [correction, hρ]
    unfold modularNodeSum
    simp_rw [hterm]
    simpa using hcancel
  have hchosenCorrection : correction chosen = (shift.val : ℤ) := by
    change (if chosen = chosen then (shift.val : ℤ) else 0) = (shift.val : ℤ)
    exact ite_eq_left rfl
  refine ⟨base, ?_, ?_, ?_, ?_⟩
  · intro ρ hρ
    simp [base, correction, hρ]
  · change raw chosen ≤ raw chosen + correction chosen
    rw [hchosenCorrection]
    omega
  · change raw chosen + correction chosen < raw chosen + (W : ℤ)
    have hlt : correction chosen < (W : ℤ) := by
      rw [hchosenCorrection]
      exact_mod_cast shift.val_lt
    linarith
  · intro j
    have hnode : (fun ρ => base ρ + (2 * (j : ℤ) + 1) * halfGap) =
        fun ρ => ((raw ρ + halfGap) + correction ρ) + 2 * (j : ℤ) * halfGap := by
      funext ρ
      dsimp [base]
      ring
    rw [hnode, modularNodeSum_add, modularNodeSum_add, hcorrection, modularNodeSum_const κ _ hκ]
    change residual + -residual + 0 = 0
    simp

end Utilities
