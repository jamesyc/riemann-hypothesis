module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.BigOperators.Module

@[expose] public section

open scoped BigOperators

namespace Utilities

variable {R M G : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [CommGroup G] [Fintype G]

private theorem sum_unitCharacter_eq_zero {ψ : G →* Rˣ} (hψ : ψ ≠ 1) :
    (∑ g : G, (ψ g : R)) = 0 := by
  obtain ⟨a, ha⟩ : ∃ a : G, ψ a ≠ 1 := by
    by_contra! h
    exact hψ (MonoidHom.ext h)
  apply eq_zero_of_mul_eq_self_left (Units.val_injective.ne ha)
  simp_rw [Finset.mul_sum, ← Units.val_mul, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)

private theorem sum_all_unitCharacters_eq_zero
    [HasEnoughRootsOfUnity R (Monoid.exponent G)] [Fintype (G →* Rˣ)]
    {g : G} (hg : g ≠ 1) :
    (∑ ψ : G →* Rˣ, (ψ g : R)) = 0 := by
  obtain ⟨θ, hθ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G R hg
  apply eq_zero_of_mul_eq_self_left (Units.val_injective.ne hθ)
  simp_rw [Finset.mul_sum, ← Units.val_mul, ← MonoidHom.mul_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft θ) _ _ (fun _ => rfl)

/-- The simultaneous eigenspace attributed to a character of the finite group. -/
def characterEigenspace (ρ : G →* Module.End R M) (ψ : G →* Rˣ) : Submodule R M :=
  ⨅ g : G, (ρ g).eigenspace (ψ g : R)

omit [IsDomain R] [Fintype G] in
theorem mem_characterEigenspace {ρ : G →* Module.End R M} {ψ : G →* Rˣ} {m : M} :
    m ∈ characterEigenspace ρ ψ ↔ ∀ g : G, ρ g m = (ψ g : R) • m := by
  simp [characterEigenspace]

/-- The averaging operator for a character, scaled by the inverse of group order. -/
noncomputable def characterProjector (ρ : G →* Module.End R M)
    (ψ : G →* Rˣ) (u : Rˣ) : Module.End R M :=
  (↑u⁻¹ : R) • ∑ g : G, (↑(ψ g)⁻¹ : R) • ρ g

omit [IsDomain R] in
theorem characterProjector_apply (ρ : G →* Module.End R M)
    (ψ : G →* Rˣ) (u : Rˣ) (m : M) :
    characterProjector ρ ψ u m =
      (↑u⁻¹ : R) • ∑ g : G, (↑(ψ g)⁻¹ : R) • ρ g m := by
  simp [characterProjector, LinearMap.sum_apply]

omit [IsDomain R] in
theorem characterProjector_mem_characterEigenspace (ρ : G →* Module.End R M)
    (ψ : G →* Rˣ) (u : Rˣ) (m : M) :
    characterProjector ρ ψ u m ∈ characterEigenspace ρ ψ := by
  apply mem_characterEigenspace.mpr
  intro g
  have hsum :
      (∑ h : G, (↑(ψ h)⁻¹ : R) • ρ (g * h) m) =
        ∑ h : G, (↑(ψ g) : R) • ((↑(ψ h)⁻¹ : R) • ρ h m) := by
    apply Fintype.sum_equiv (Equiv.mulLeft g) _ _
    intro h
    change (↑(ψ h)⁻¹ : R) • ρ (g * h) m =
      (↑(ψ g) : R) • ((↑(ψ (g * h))⁻¹ : R) • ρ (g * h) m)
    rw [smul_smul, ← Units.val_mul, map_mul ψ g h]
    congr 1
    congr 1
    rw [mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]
  rw [characterProjector_apply, map_smul, map_sum]
  simp_rw [map_smul, ← mul_apply_eq_comp, ← map_mul]
  rw [hsum, ← Finset.smul_sum, smul_comm]

open scoped Classical in
theorem characterProjector_apply_of_mem {ρ : G →* Module.End R M}
    {θ : G →* Rˣ} {m : M} (hm : m ∈ characterEigenspace ρ θ)
    (ψ : G →* Rˣ) {u : Rˣ} (hu : (u : R) = Fintype.card G) :
    characterProjector ρ ψ u m = if ψ = θ then m else 0 := by
  classical
  have hmem := mem_characterEigenspace.mp hm
  rw [characterProjector_apply]
  simp_rw [hmem, smul_smul, ← Units.val_mul, ← MonoidHom.inv_apply, ← MonoidHom.mul_apply]
  rw [← Finset.sum_smul, smul_smul]
  by_cases h : ψ = θ
  · subst ψ
    simp only [inv_mul_cancel, MonoidHom.one_apply, Units.val_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ← hu, Units.inv_mul, one_smul, ite_true]
  · have h' : ψ⁻¹ * θ ≠ 1 := fun z => h (inv_mul_eq_one.mp z)
    rw [sum_unitCharacter_eq_zero h', ite_eq_right h, mul_zero, zero_smul]

theorem sum_characterProjector_apply (ρ : G →* Module.End R M)
    [HasEnoughRootsOfUnity R (Monoid.exponent G)] [Fintype (G →* Rˣ)]
    (m : M) {u : Rˣ} (hu : (u : R) = Fintype.card G) :
    (∑ ψ : G →* Rˣ, characterProjector ρ ψ u m) = m := by
  classical
  have hcard : Fintype.card (G →* Rˣ) = Fintype.card G := by
    simpa only [Nat.card_eq_fintype_card] using
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G R
  have hinv (g : G) :
      (∑ ψ : G →* Rˣ, (↑(ψ g)⁻¹ : R)) = ∑ ψ : G →* Rˣ, (ψ g : R) :=
    Fintype.sum_equiv (Equiv.inv (G →* Rˣ)) _ _ (fun _ => rfl)
  simp_rw [characterProjector_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hinv]
  rw [Fintype.sum_eq_single (1 : G)]
  · simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      hcard, ← hu, one_apply_eq_self, smul_smul, Units.inv_mul, one_smul]
  · intro g hg
    rw [sum_all_unitCharacters_eq_zero (R := R) hg, zero_smul]

/-- When the group order is invertible, the character eigenspaces split a
representation even if the coefficient module has torsion. -/
noncomputable def characterEigenspaceDecomposition (ρ : G →* Module.End R M)
    [HasEnoughRootsOfUnity R (Monoid.exponent G)] [Fintype (G →* Rˣ)]
    (hunit : IsUnit (Fintype.card G : R)) :
    M ≃ₗ[R] (∀ ψ : G →* Rˣ, characterEigenspace ρ ψ) := by
  classical
  let u := hunit.unit
  have hu : (u : R) = Fintype.card G := hunit.unit_spec
  let T (ψ : G →* Rˣ) : M →ₗ[R] characterEigenspace ρ ψ :=
    (characterProjector ρ ψ u).codRestrict _ (characterProjector_mem_characterEigenspace ρ ψ u)
  refine
    { LinearMap.pi T with
      invFun := fun x => ∑ ψ, (x ψ).val
      left_inv := fun x => sum_characterProjector_apply ρ x hu
      right_inv := fun x => ?_ }
  funext ψ
  apply Subtype.ext
  change characterProjector ρ ψ u (∑ θ, (x θ).val) = (x ψ).val
  rw [map_sum]
  have hmem (θ : G →* Rˣ) : (x θ).val ∈ characterEigenspace ρ θ := (x θ).property
  simp_rw [characterProjector_apply_of_mem (hmem _) ψ hu]
  simp

end Utilities
