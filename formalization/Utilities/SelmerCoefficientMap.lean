module

public import Utilities.SelmerKernel

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
  {A B : DiscreteGaloisModule k G}

variable {k' : Type} [CommRing k'] {B' : DiscreteGaloisModule k' G}

/-- An additive intertwiner preserves the cocycle equations, local
constancy, and the local coboundary conditions. -/
theorem map_mem_locallyTrivialCocycles₁ (D : Set (Subgroup G)) (u : A.rep →+ B'.rep)
    (hu : ∀ g a, u (A.rep.ρ g a) = B'.rep.ρ g (u a))
    {f : G → A.rep} (hf : f ∈ A.locallyTrivialCocycles₁ D) :
    (fun g => u (f g)) ∈ B'.locallyTrivialCocycles₁ D := by
  refine ⟨⟨(mem_cocycles₁_iff _).mpr ?_, hf.1.2.comp u⟩, ?_⟩
  · intro g h
    rw [(mem_cocycles₁_iff _).mp hf.1.1, map_add, hu]
  · intro J hJ
    obtain ⟨a, ha⟩ := hf.2 J hJ
    refine ⟨u a, fun g hg => ?_⟩
    change u (f g) = B'.rep.ρ g (u a) - u a
    rw [ha g hg, map_sub, hu]

/-- Apply a coefficient intertwiner to each locally trivial cocycle. -/
def mapLocallyTrivialCocycles₁ (D : Set (Subgroup G)) (u : A.rep →ₗ[k] B.rep)
    (hu : ∀ g a, u (A.rep.ρ g a) = B.rep.ρ g (u a)) :
    A.locallyTrivialCocycles₁ D →ₗ[k] B.locallyTrivialCocycles₁ D where
  toFun f := ⟨fun g => u (f.val g), map_mem_locallyTrivialCocycles₁ D u.toAddMonoidHom hu f.property⟩
  map_add' f g := Subtype.ext (funext fun s => u.map_add (f.val s) (g.val s))
  map_smul' a f := Subtype.ext (funext fun s => u.map_smul a (f.val s))

/-- An intertwiner on the coefficients induces a map on Selmer kernels. -/
def mapSelmerKernel (D : Set (Subgroup G)) (u : A.rep →ₗ[k] B.rep)
    (hu : ∀ g a, u (A.rep.ρ g a) = B.rep.ρ g (u a)) :
    A.selmerKernel D →ₗ[k] B.selmerKernel D := by
  let BA := (coboundaries₁ A.rep).comap (A.locallyTrivialCocycles₁ D).subtype
  let BB := (coboundaries₁ B.rep).comap (B.locallyTrivialCocycles₁ D).subtype
  refine BA.mapQ BB (mapLocallyTrivialCocycles₁ D u hu) ?_
  intro f hf
  obtain ⟨a, ha⟩ := hf
  refine ⟨u a, funext fun g => ?_⟩
  change B.rep.ρ g (u a) - u a = u (f.val g)
  have hfg : f.val g = A.rep.ρ g a - a := (congrFun ha g).symm
  rw [hfg, map_sub, hu]

/-- An equivariant equivalence of coefficients induces an equivalence of
Selmer kernels with the same local family. -/
def selmerCoefficientEquiv (D : Set (Subgroup G)) (e : A.rep ≃ₗ[k] B.rep)
    (he : ∀ g a, e (A.rep.ρ g a) = B.rep.ρ g (e a)) :
    A.selmerKernel D ≃ₗ[k] B.selmerKernel D := by
  have he' (g : G) (b : B.rep) : e.symm (B.rep.ρ g b) = A.rep.ρ g (e.symm b) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  refine
    { mapSelmerKernel D e.toLinearMap he with
      invFun := mapSelmerKernel D e.symm.toLinearMap he'
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    let BA := (coboundaries₁ A.rep).comap (A.locallyTrivialCocycles₁ D).subtype
    obtain ⟨f, rfl⟩ := BA.mkQ_surjective x
    change BA.mkQ (mapLocallyTrivialCocycles₁ D e.symm.toLinearMap he'
      (mapLocallyTrivialCocycles₁ D e.toLinearMap he f)) = BA.mkQ f
    exact congrArg BA.mkQ (Subtype.ext (funext fun g => e.symm_apply_apply (f.val g)))
  · intro x
    let BB := (coboundaries₁ B.rep).comap (B.locallyTrivialCocycles₁ D).subtype
    obtain ⟨f, rfl⟩ := BB.mkQ_surjective x
    change BB.mkQ (mapLocallyTrivialCocycles₁ D e.toLinearMap he
      (mapLocallyTrivialCocycles₁ D e.symm.toLinearMap he' f)) = BB.mkQ f
    exact congrArg BB.mkQ (Subtype.ext (funext fun g => e.apply_symm_apply (f.val g)))

theorem selmerCoefficientEquiv_mk (D : Set (Subgroup G)) (e : A.rep ≃ₗ[k] B.rep)
    (he : ∀ g a, e (A.rep.ρ g a) = B.rep.ρ g (e a)) (f : A.locallyTrivialCocycles₁ D) :
    selmerCoefficientEquiv D e he (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (mapLocallyTrivialCocycles₁ D e.toLinearMap he f) :=
  rfl

end Utilities.DiscreteGaloisModule
