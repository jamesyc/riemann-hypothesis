module

public import Utilities.SelmerKernelAction
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G G' : Type} [CommRing k] [Group G] [TopologicalSpace G]
  [Group G'] [TopologicalSpace G']
  (A : DiscreteGaloisModule k G) (B : DiscreteGaloisModule k G')
  (D : Set (Subgroup G)) (D' : Set (Subgroup G'))
  (e : G' ≃ₜ* G) (u : A.rep ≃ₗ[k] B.rep)
  (hu : ∀ g a, u (A.rep.ρ (e g) a) = B.rep.ρ g (u a))
  (hD : (fun J : Subgroup G' => J.map e.toMonoidHom) '' D' = D)

local notation "BA" => Submodule.comap (Submodule.subtype (locallyTrivialCocycles₁ A D))
  (coboundaries₁ (DiscreteGaloisModule.rep A))
local notation "BB" => Submodule.comap (Submodule.subtype (locallyTrivialCocycles₁ B D'))
  (coboundaries₁ (DiscreteGaloisModule.rep B))

/-- A topological group isomorphism and compatible coefficient isomorphism
give an equivalence of Selmer kernels for the transported local families. -/
def selmerKernelGroupEquiv : A.selmerKernel D ≃ₗ[k] B.selmerKernel D' := by
  have hmap (J : Subgroup G') (hJ : J ∈ D') : J.map e.toMonoidHom ∈ D :=
    hD ▸ Set.mem_image_of_mem _ hJ
  have hback (J : Subgroup G) (hJ : J ∈ D) : J.map e.symm.toMonoidHom ∈ D' := by
    obtain ⟨K, hK, rfl⟩ := hD.symm ▸ hJ
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G' :=
      MonoidHom.ext fun g => e.symm_apply_apply g
    rwa [Subgroup.map_map, hid, Subgroup.map_id]
  have hu' (g : G) (b : B.rep) : u.symm (B.rep.ρ (e.symm g) b) = A.rep.ρ g (u.symm b) := by
    apply u.injective
    have h := hu (e.symm g) (u.symm b)
    rw [e.apply_symm_apply, u.apply_symm_apply] at h
    exact (u.apply_symm_apply _).trans h.symm
  refine
    { A.pullbackSelmerKernelAlong D B D' e.toMonoidHom e.continuous_toFun u.toLinearMap hu hmap with
      invFun := B.pullbackSelmerKernelAlong D' A D e.symm.toMonoidHom e.symm.continuous_toFun
        u.symm.toLinearMap hu' hback
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective BA) x
    change (Submodule.mkQ BA) _ = (Submodule.mkQ BA) f
    apply congrArg (Submodule.mkQ BA)
    apply Subtype.ext
    funext g
    change u.symm (u (f.val (e (e.symm g)))) = f.val g
    rw [e.apply_symm_apply, u.symm_apply_apply]
  · intro x
    obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective BB) x
    change (Submodule.mkQ BB) _ = (Submodule.mkQ BB) f
    apply congrArg (Submodule.mkQ BB)
    apply Subtype.ext
    funext g
    change u (u.symm (f.val (e.symm (e g)))) = f.val g
    rw [e.symm_apply_apply, u.apply_symm_apply]

/-- The equivalence for transported coefficients and groups intertwines
compatible pullback actions. -/
theorem selmerKernelGroupEquiv_pullback
    (φ : G →* G) (φ' : G' →* G') (hφ : Continuous φ) (hφ' : Continuous φ')
    (v : Module.End k A.rep) (v' : Module.End k B.rep)
    (hv : ∀ g a, v (A.rep.ρ (φ g) a) = A.rep.ρ g (v a))
    (hv' : ∀ g b, v' (B.rep.ρ (φ' g) b) = B.rep.ρ g (v' b))
    (hgrp : ∀ J ∈ D, J.map φ ∈ D) (hgrp' : ∀ J ∈ D', J.map φ' ∈ D')
    (he : ∀ g, φ (e g) = e (φ' g)) (hvmap : ∀ a, u (v a) = v' (u a))
    (x : A.selmerKernel D) :
    selmerKernelGroupEquiv A B D D' e u hu hD (A.pullbackSelmerKernel D φ hφ v hv hgrp x) =
      B.pullbackSelmerKernel D' φ' hφ' v' hv' hgrp'
        (selmerKernelGroupEquiv A B D D' e u hu hD x) := by
  obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective BA) x
  change (Submodule.mkQ BB) _ = (Submodule.mkQ BB) _
  apply congrArg (Submodule.mkQ BB)
  apply Subtype.ext
  funext g
  change u (v (f.val (φ (e g)))) = v' (u (f.val (e (φ' g))))
  rw [he, hvmap]

end Utilities.DiscreteGaloisModule
