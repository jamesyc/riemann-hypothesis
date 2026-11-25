module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel

@[expose] public section

namespace Utilities

/-- An involution over a ring in which two is invertible splits its module
into the two sign eigenspaces, even for modules with torsion. -/
theorem involution_isCompl_eigenspaces {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (T : Module.End R M) (hT : Function.Involutive T) (h₂ : IsUnit (2 : R)) :
    IsCompl (T.eigenspace 1) (T.eigenspace (-1)) := by
  obtain ⟨u, hu⟩ := h₂
  have hun (x : M) : (↑u⁻¹ : R) • ((2 : R) • x) = x := by
    rw [← mul_smul, ← hu, Units.inv_mul, one_smul]
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · intro x hx hy
    have h₁ : T x = x := by simpa using Module.End.mem_eigenspace_iff.mp hx
    have h₂ : T x = -x := by simpa using Module.End.mem_eigenspace_iff.mp hy
    have hzero : (2 : R) • x = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr (h₁.symm.trans h₂)
    rw [← hun x, hzero, smul_zero]
  · apply top_unique
    intro x _
    let a := (↑u⁻¹ : R) • (x + T x)
    let b := (↑u⁻¹ : R) • (x - T x)
    have ha : a ∈ T.eigenspace 1 := by
      rw [Module.End.mem_eigenspace_iff, one_smul]
      simp only [a, map_smul, map_add, hT x, add_comm]
    have hb : b ∈ T.eigenspace (-1) := by
      rw [Module.End.mem_eigenspace_iff, neg_one_smul]
      simp only [b, map_smul, map_sub, hT x, ← smul_neg, neg_sub]
    have hab : a + b = x := by
      rw [show a + b = (↑u⁻¹ : R) • ((2 : R) • x) by
        dsimp [a, b]
        rw [← smul_add, two_smul]
        congr 1
        abel]
      exact hun x
    rw [← hab]
    exact Submodule.add_mem_sup ha hb

end Utilities
