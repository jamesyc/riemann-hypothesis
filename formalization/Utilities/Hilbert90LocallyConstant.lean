module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open Filter groupCohomology
open scoped Topology

namespace Utilities

/-- A locally constant multiplicative cocycle on an algebraic Galois
group is a coboundary. Its finite image and an open fiber give a finite
layer on which to apply Hilbert 90. -/
theorem isMulCoboundary₁_of_locallyConstant {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] (f : Gal(L/K) → Lˣ) (hlc : IsLocallyConstant f)
    (hc : IsMulCocycle₁ f) : IsMulCoboundary₁ f := by
  have h1 : f 1 = 1 := by
    have h := hc 1 1
    rw [one_mul, one_smul] at h
    exact (mul_left_cancel (show f 1 * 1 = f 1 * f 1 from (mul_one _).trans h)).symm
  obtain ⟨D, hD, hDn, hDf⟩ := (krullTopology_mem_nhds_one_iff_of_normal K L _).mp
    ((hlc.isOpen_fiber 1).mem_nhds h1)
  let _ : FiniteDimensional K D := hD
  let _ : IsGalois K D :=
    isGalois_iff.mpr ⟨Algebra.isSeparable_tower_bot_of_isSeparable K D L, hDn⟩
  let D₀ : FiniteGaloisIntermediateField K L := ⟨D⟩
  let V := Set.range (fun s => (f s : L))
  let _ : Finite V := (hlc.comp (fun u : Lˣ => (u : L))).range_finite.to_subtype
  let E := D₀ ⊔ FiniteGaloisIntermediateField.adjoin K V
  let M := E.toIntermediateField
  let π : Gal(L/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  have hπ : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective L
  have hMv (s : Gal(L/K)) : (f s : L) ∈ M :=
    (show (FiniteGaloisIntermediateField.adjoin K V).toIntermediateField ≤ M from le_sup_right)
      (FiniteGaloisIntermediateField.subset_adjoin K V (Set.mem_range_self s))
  have hkill (s : Gal(L/K)) (hs : s ∈ π.ker) : f s = 1 := by
    change s ∈ (AlgEquiv.restrictNormalHom M).ker at hs
    rw [M.restrictNormalHom_ker] at hs
    exact hDf (D.fixingSubgroup_antitone (show D ≤ M from le_sup_left) hs)
  have hfiber (s t : Gal(L/K)) (h : π s = π t) : f s = f t := by
    have hst : s⁻¹ * t ∈ π.ker := by
      change π (s⁻¹ * t) = 1
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have he := hc s (s⁻¹ * t)
    rw [mul_inv_cancel_left, hkill _ hst, smul_one, one_mul] at he
    exact he.symm
  let F (s : Gal(L/K)) : Mˣ := Units.mk0 ⟨f s, hMv s⟩ (fun h => (f s).ne_zero (congrArg Subtype.val h))
  let ψ (s : Gal(M/K)) : Mˣ := F (Function.surjInv hπ s)
  have hψ (s : Gal(L/K)) : algebraMap M L (ψ (π s) : M) = (f s : L) :=
    congrArg (fun u : Lˣ => (u : L))
      (hfiber _ _ (Function.rightInverse_surjInv hπ (π s)))
  have hψc : IsMulCocycle₁ ψ := by
    intro s t
    obtain ⟨s, rfl⟩ := hπ s
    obtain ⟨t, rfl⟩ := hπ t
    apply Units.ext
    apply (algebraMap M L).injective
    change algebraMap M L (ψ (π s * π t) : M) =
      algebraMap M L (π s (ψ (π t) : M) * (ψ (π s) : M))
    have hcomm (z : M) : algebraMap M L (π s z) = s (algebraMap M L z) :=
      s.restrictNormal_commutes M z
    rw [← map_mul π, hψ, map_mul, hcomm, hψ, hψ]
    exact congrArg (fun u : Lˣ => (u : L)) (hc s t)
  obtain ⟨b, hb⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units ψ hψc
  let B := Units.map (algebraMap M L).toMonoidHom b
  refine ⟨B, fun s => ?_⟩
  apply Units.ext
  have h := congrArg (fun u : Mˣ => algebraMap M L (u : M)) (hb (π s))
  simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass] at h ⊢
  change s (algebraMap M L (b : M)) / algebraMap M L (b : M) = (f s : L)
  change algebraMap M L (π s (b : M) / (b : M)) = algebraMap M L (ψ (π s) : M) at h
  have hcomm : algebraMap M L (π s (b : M)) = s (algebraMap M L (b : M)) :=
    s.restrictNormal_commutes M (b : M)
  rwa [hψ, map_div₀, hcomm] at h

end Utilities
