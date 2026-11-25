module

public import Utilities.FiniteCharacterEigenspaces
public import Mathlib.RingTheory.Length
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.ENat.BigOperators

@[expose] public section

namespace Utilities

variable {R M G : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [CommGroup G] [Fintype G]

open scoped Classical in
/-- If an involution acts by a scalar sign on the whole module, the length
is the sum of the character lengths with that sign. -/
theorem length_eq_sum_characterEigenspace_of_scalar_involution
    [HasEnoughRootsOfUnity R (Monoid.exponent G)] [Fintype (G →* Rˣ)]
    (ρ : G →* Module.End R M) (horder : IsUnit (Fintype.card G : R))
    (htwo : IsUnit (2 : R)) (c : G) (hc : c ^ 2 = 1)
    (s : R) (hs : s ^ 2 = 1) (hρ : ρ c = s • 1) :
    Module.length R M = ∑ ψ : G →* Rˣ,
      if (ψ c : R) = s then Module.length R (characterEigenspace ρ ψ) else 0 := by
  classical
  rw [(characterEigenspaceDecomposition ρ horder).length_eq, Module.length_pi_of_fintype]
  apply Finset.sum_congr rfl
  intro ψ _
  by_cases hψ : (ψ c : R) = s
  · rw [ite_eq_left hψ]
  · rw [ite_eq_right hψ, Module.length_eq_zero_iff]
    have hsq : (ψ c : R) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hc, map_one, Units.val_one]
    have hneg : (ψ c : R) = -s := (sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans hs.symm)).resolve_left hψ
    have hsunit : IsUnit s := IsUnit.of_mul_eq_one s (by simpa only [pow_two] using hs)
    have hunit : IsUnit (s - (ψ c : R)) := by
      rw [hneg, sub_neg_eq_add, ← two_mul]
      exact htwo.mul hsunit
    have hz (x : characterEigenspace ρ ψ) : (x : M) = 0 := by
      apply hunit.smul_eq_zero.mp
      have h := mem_characterEigenspace.mp x.property c
      rw [hρ] at h
      change s • (x : M) = (ψ c : R) • (x : M) at h
      rw [sub_smul, h, sub_self]
    exact ⟨fun x y => Subtype.ext ((hz x).trans (hz y).symm)⟩

/-- Cancel the common positive length scaling in a sum of local bounds,
retaining the finiteness of the original length. -/
theorem length_log_bound_of_scaled_sum {ι : Type*} (S : Finset ι) (m : ℕ∞) {r : ℕ}
    (hr : 0 < r) (f : ι → ℕ∞) (g : ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h : m * (r : ℕ∞) ≤ ∑ j ∈ S, f j)
    (hf : ∀ j ∈ S, f j ≠ ⊤ ∧ ((f j).toNat : ℝ) * L ≤ (r : ℝ) * g j) :
    m ≠ ⊤ ∧ (m.toNat : ℝ) * L ≤ ∑ j ∈ S, g j := by
  have hfinite : (∑ j ∈ S, f j) ≠ ⊤ := ENat.sum_ne_top.mpr fun j hj => (hf j hj).1
  have hr₀ : (r : ℕ∞) ≠ 0 := by exact_mod_cast hr.ne'
  have hm : m ≠ ⊤ := by
    intro hm
    rw [hm, ENat.top_mul hr₀, top_le_iff] at h
    exact hfinite h
  refine ⟨hm, ?_⟩
  have hn := ENat.toNat_le_toNat h hfinite
  rw [ENat.toNat_mul, ENat.toNat_natCast, ENat.toNat_sum (fun j hj => (hf j hj).1)] at hn
  have hs : ((m.toNat : ℝ) * r) * L ≤ ∑ j ∈ S, (f j).toNat * L := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hL
  have ht : (∑ j ∈ S, (f j).toNat * L) ≤ (r : ℝ) * ∑ j ∈ S, g j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => (hf j hj).2
  apply le_of_mul_le_mul_left _ (by exact_mod_cast hr : (0 : ℝ) < r)
  rw [mul_comm (m.toNat : ℝ) (r : ℝ), mul_assoc] at hs
  exact hs.trans ht

end Utilities
