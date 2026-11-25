module

public import Utilities.SelmerKernel
public import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic.Abel

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
variable (A : DiscreteGaloisModule k G) (restrictionGroups : Set (Subgroup G))

section Along

variable {G' : Type} [Group G'] [TopologicalSpace G'] (B : DiscreteGaloisModule k G')
  (D' : Set (Subgroup G'))

/-- Pull back locally trivial cocycles along a continuous homomorphism,
using a compatible map of coefficients. -/
def pullbackLocallyTrivialCocyclesAlong (φ : G' →* G) (hφ : Continuous φ)
    (u : A.rep →ₗ[k] B.rep)
    (hu : ∀ g a, u (A.rep.ρ (φ g) a) = B.rep.ρ g (u a))
    (hgroups : ∀ J ∈ D', J.map φ ∈ restrictionGroups) :
    A.locallyTrivialCocycles₁ restrictionGroups →ₗ[k] B.locallyTrivialCocycles₁ D' where
  toFun f := ⟨fun g => u (f.val (φ g)), by
    refine ⟨⟨(mem_cocycles₁_iff _).mpr ?_, (f.property.1.2.comp_continuous hφ).comp u⟩, ?_⟩
    · intro g h
      rw [map_mul, (mem_cocycles₁_iff _).mp f.property.1.1, map_add, hu]
    · intro J hJ
      obtain ⟨a, ha⟩ := f.property.2 (J.map φ) (hgroups J hJ)
      refine ⟨u a, fun g hg => ?_⟩
      change u (f.val (φ g)) = B.rep.ρ g (u a) - u a
      rw [ha (φ g) (Subgroup.mem_map_of_mem φ hg), map_sub, hu]⟩
  map_add' f g := Subtype.ext (funext fun x => u.map_add (f.val (φ x)) (g.val (φ x)))
  map_smul' r f := Subtype.ext (funext fun x => u.map_smul r (f.val (φ x)))

/-- Pullback with compatible coefficients descends to Selmer kernels. -/
def pullbackSelmerKernelAlong (φ : G' →* G) (hφ : Continuous φ)
    (u : A.rep →ₗ[k] B.rep)
    (hu : ∀ g a, u (A.rep.ρ (φ g) a) = B.rep.ρ g (u a))
    (hgroups : ∀ J ∈ D', J.map φ ∈ restrictionGroups) :
    A.selmerKernel restrictionGroups →ₗ[k] B.selmerKernel D' := by
  let BA := (coboundaries₁ A.rep).comap (A.locallyTrivialCocycles₁ restrictionGroups).subtype
  let BB := (coboundaries₁ B.rep).comap (B.locallyTrivialCocycles₁ D').subtype
  apply BA.mapQ BB (pullbackLocallyTrivialCocyclesAlong A restrictionGroups B D' φ hφ u hu hgroups)
  intro f hf
  change f.val ∈ coboundaries₁ A.rep at hf
  obtain ⟨a, ha⟩ := hf
  refine ⟨u a, funext fun g => ?_⟩
  have hfg : f.val (φ g) = A.rep.ρ (φ g) a - a := (congrFun ha (φ g)).symm
  change B.rep.ρ g (u a) - u a = u (f.val (φ g))
  rw [hfg, map_sub, hu]

end Along

/-- The locally trivial cocycle pullback for an endomorphism. -/
def pullbackLocallyTrivialCocycles₁ (φ : G →* G) (hφ : Continuous φ)
    (u : A.rep →ₗ[k] A.rep)
    (hu : ∀ g a, u (A.rep.ρ (φ g) a) = A.rep.ρ g (u a))
    (hgroups : ∀ D ∈ restrictionGroups, D.map φ ∈ restrictionGroups) :
    A.locallyTrivialCocycles₁ restrictionGroups →ₗ[k] A.locallyTrivialCocycles₁ restrictionGroups :=
  A.pullbackLocallyTrivialCocyclesAlong restrictionGroups A restrictionGroups φ hφ u hu hgroups

/-- The Selmer pullback for an endomorphism. -/
def pullbackSelmerKernel (φ : G →* G) (hφ : Continuous φ)
    (u : A.rep →ₗ[k] A.rep)
    (hu : ∀ g a, u (A.rep.ρ (φ g) a) = A.rep.ρ g (u a))
    (hgroups : ∀ D ∈ restrictionGroups, D.map φ ∈ restrictionGroups) :
    A.selmerKernel restrictionGroups →ₗ[k] A.selmerKernel restrictionGroups :=
  A.pullbackSelmerKernelAlong restrictionGroups A restrictionGroups φ hφ u hu hgroups

theorem pullbackSelmerKernel_congr {φ ψ : G →* G} {hφ : Continuous φ} {hψ : Continuous ψ}
    {u v : A.rep →ₗ[k] A.rep}
    {hu : ∀ g a, u (A.rep.ρ (φ g) a) = A.rep.ρ g (u a)}
    {hv : ∀ g a, v (A.rep.ρ (ψ g) a) = A.rep.ρ g (v a)}
    {hgroupsφ : ∀ D ∈ restrictionGroups, D.map φ ∈ restrictionGroups}
    {hgroupsψ : ∀ D ∈ restrictionGroups, D.map ψ ∈ restrictionGroups}
    (h : φ = ψ) (h' : u = v) :
    A.pullbackSelmerKernel restrictionGroups φ hφ u hu hgroupsφ =
      A.pullbackSelmerKernel restrictionGroups ψ hψ v hv hgroupsψ := by
  subst ψ
  subst v
  rfl

/-- An involutive pullback on the group and on coefficients induces an
involution on the Selmer restriction kernel. -/
theorem pullbackSelmerKernel_involutive (φ : G →* G) (hφ : Continuous φ)
    (u : A.rep →ₗ[k] A.rep)
    (hu : ∀ g a, u (A.rep.ρ (φ g) a) = A.rep.ρ g (u a))
    (hgroups : ∀ D ∈ restrictionGroups, D.map φ ∈ restrictionGroups)
    (hφ₂ : Function.Involutive φ) (hu₂ : Function.Involutive u) :
    Function.Involutive (A.pullbackSelmerKernel restrictionGroups φ hφ u hu hgroups) := by
  intro z
  let C := A.locallyTrivialCocycles₁ restrictionGroups
  let B := (coboundaries₁ A.rep).comap C.subtype
  obtain ⟨f, rfl⟩ := B.mkQ_surjective z
  let U := A.pullbackLocallyTrivialCocycles₁ restrictionGroups φ hφ u hu hgroups
  change B.mkQ (U (U f)) = B.mkQ f
  congr 1
  apply Subtype.ext
  funext g
  change u (u (f.val (φ (φ g)))) = f.val g
  rw [hφ₂ g, hu₂]

/-- Conjugating a cocycle by an element of the underlying group, with its action
on coefficients, changes the cocycle by the coboundary of its value there. -/
theorem inner_pullback_sub_eq_coboundary (f : cocycles₁ A.rep) (s g : G) :
    A.rep.ρ s (f (s⁻¹ * g * s)) - f g = A.rep.ρ g (f s) - f s := by
  have hf (x y : G) : f (x * y) = A.rep.ρ x (f y) + f x :=
    (mem_cocycles₁_iff _).mp f.property x y
  have hmul (x y : G) (a : A.rep) : A.rep.ρ x (A.rep.ρ y a) = A.rep.ρ (x * y) a :=
    (DFunLike.congr_fun (map_mul A.rep.ρ x y) a).symm
  have hone (a : A.rep) : A.rep.ρ 1 a = a := DFunLike.congr_fun (map_one A.rep.ρ) a
  rw [hf (s⁻¹ * g) s, hf s⁻¹ g, map_add, map_add, hmul s (s⁻¹ * g),
    mul_inv_cancel_left, hmul s s⁻¹, mul_inv_cancel, hone, cocycles₁_map_inv]
  abel

/-- When the conjugate fixes the value at the conjugating element,
conjugation of a cocycle value is the coefficient action. -/
theorem cocycle_apply_conj_eq_of_fixed (f : cocycles₁ A.rep) (s u : G)
    (hfix : A.rep.ρ (s * u * s⁻¹) (f s) = f s) :
    f (s * u * s⁻¹) = A.rep.ρ s (f u) := by
  have h := A.inner_pullback_sub_eq_coboundary f s (s * u * s⁻¹)
  rw [show s⁻¹ * (s * u * s⁻¹) * s = u by group, hfix, sub_self] at h
  exact (sub_eq_zero.mp h).symm

/-- The action of an inner automorphism on the Selmer restriction kernel is trivial. -/
theorem inner_pullbackSelmerKernel_eq_id [IsTopologicalGroup G] (s : G)
    (hgroups : ∀ D ∈ restrictionGroups,
      D.map (MulAut.conj s⁻¹).toMonoidHom ∈ restrictionGroups) :
    let hφ : Continuous (MulAut.conj s⁻¹ : G → G) :=
      (continuous_const.mul continuous_id).mul continuous_const
    let hu : ∀ g a, A.rep.ρ s (A.rep.ρ (MulAut.conj s⁻¹ g) a) = A.rep.ρ g (A.rep.ρ s a) := by
      intro g a
      have hmul : s * MulAut.conj s⁻¹ g = g * s := by
        rw [MulAut.conj_apply, inv_inv, ← mul_assoc, mul_inv_cancel_left]
      have hρ : A.rep.ρ s * A.rep.ρ (MulAut.conj s⁻¹ g) = A.rep.ρ g * A.rep.ρ s := by
        rw [← map_mul, hmul, map_mul]
      exact DFunLike.congr_fun hρ a
    A.pullbackSelmerKernel restrictionGroups (MulAut.conj s⁻¹).toMonoidHom hφ
      (A.rep.ρ s) hu hgroups = LinearMap.id := by
  dsimp only
  apply LinearMap.ext
  intro z
  let C := A.locallyTrivialCocycles₁ restrictionGroups
  let B := (coboundaries₁ A.rep).comap C.subtype
  obtain ⟨f, rfl⟩ := B.mkQ_surjective z
  change B.mkQ _ = B.mkQ f
  rw [← sub_eq_zero, ← map_sub]
  apply (Submodule.Quotient.mk_eq_zero B).mpr
  let f' : cocycles₁ A.rep := ⟨f.val, f.property.1.1⟩
  refine ⟨f' s, funext fun g => ?_⟩
  change A.rep.ρ g (f' s) - f' s = A.rep.ρ s (f' (s⁻¹ * g * s⁻¹⁻¹)) - f' g
  rw [inv_inv]
  exact (A.inner_pullback_sub_eq_coboundary f' s g).symm

end Utilities.DiscreteGaloisModule
