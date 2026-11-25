module

public import Utilities.SelmerKernel
public import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section

open groupCohomology
open scoped IsMulCommutative

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
  (A : DiscreteGaloisModule k G) (D : Set (Subgroup G)) (δ : G)

local notation "C" => locallyTrivialCocycles₁ A D
local notation "B" => Submodule.comap (Submodule.subtype C) (coboundaries₁ (DiscreteGaloisModule.rep A))

/-- The locally trivial cocycles normalized to vanish at the chosen element. -/
def normalizedSelmerCocycles : Submodule k (G → A.rep) :=
  C ⊓ LinearMap.ker (LinearMap.proj δ)

@[simp]
theorem mem_normalizedSelmerCocycles (f : G → A.rep) :
    f ∈ normalizedSelmerCocycles A D δ ↔ f ∈ C ∧ f δ = 0 :=
  Iff.rfl

/-- Quotienting by the global coboundaries identifies the normalized
cocycles with the Selmer kernel when the evaluation of a coboundary at
the chosen element is bijective on the coefficient module. -/
noncomputable def normalizedSelmerCocyclesEquiv
    (hδ : Function.Bijective (A.rep.ρ δ - 1 : Module.End k A.rep)) :
    normalizedSelmerCocycles A D δ ≃ₗ[k] A.selmerKernel D := by
  let incl : normalizedSelmerCocycles A D δ →ₗ[k] C := Submodule.inclusion inf_le_left
  let L : normalizedSelmerCocycles A D δ →ₗ[k] A.selmerKernel D :=
    (Submodule.mkQ B).comp incl
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · intro x y hxy
    have hclass : (Submodule.mkQ B) (incl x) = (Submodule.mkQ B) (incl y) := hxy
    obtain ⟨a, ha⟩ := (Submodule.Quotient.eq B).mp hclass
    have hδa : (A.rep.ρ δ - 1 : Module.End k A.rep) a = 0 := by
      have h := congrFun ha δ
      change A.rep.ρ δ a - a = x.val δ - y.val δ at h
      have hx : x.val δ = 0 := ((mem_normalizedSelmerCocycles A D δ x.val).mp x.property).2
      have hy : y.val δ = 0 := ((mem_normalizedSelmerCocycles A D δ y.val).mp y.property).2
      rw [hx, hy, sub_self] at h
      exact h
    have ha₀ : a = 0 := hδ.injective (hδa.trans (map_zero _).symm)
    apply Subtype.ext
    funext g
    have h := congrFun ha g
    change A.rep.ρ g a - a = x.val g - y.val g at h
    rw [ha₀, map_zero, sub_self] at h
    exact sub_eq_zero.mp h.symm
  · intro x
    obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective B) x
    obtain ⟨a, ha⟩ := hδ.surjective (f.val δ)
    let d : C := ⟨(d₀₁ A.rep).hom a, A.coboundaries₁_le_locallyTrivial D ⟨a, rfl⟩⟩
    have hf : (f - d).val ∈ normalizedSelmerCocycles A D δ := by
      refine (mem_normalizedSelmerCocycles A D δ _).mpr ⟨(f - d).property, ?_⟩
      change f.val δ - (A.rep.ρ δ a - a) = 0
      change A.rep.ρ δ a - a = f.val δ at ha
      rw [ha, sub_self]
    refine ⟨⟨(f - d).val, hf⟩, ?_⟩
    have hd : (Submodule.mkQ B) d = 0 := (Submodule.Quotient.mk_eq_zero B).mpr ⟨a, rfl⟩
    change (Submodule.mkQ B) (f - d) = (Submodule.mkQ B) f
    rw [map_sub, hd, sub_zero]

/-- A normalized cocycle is determined by its restriction to the kernel
of a map to an abelian group, provided the normalizing action minus one
is injective. -/
theorem normalizedSelmerCocycles_eq_zero_of_vanishes_on_abelianKernel
    {Q : Type*} [Group Q] [IsMulCommutative Q] (π : G →* Q)
    (hδ : Function.Injective (A.rep.ρ δ - 1 : Module.End k A.rep))
    (c : normalizedSelmerCocycles A D δ) (hc : ∀ g ∈ π.ker, c.val g = 0) :
    c = 0 := by
  have hn : c.val δ = 0 := c.property.2
  have hmul := (mem_cocycles₁_iff c.val).mp c.property.1.1.1
  apply Subtype.ext
  funext g
  change c.val g = 0
  let u := (δ * g)⁻¹ * (g * δ)
  have hu : u ∈ π.ker := by
    change π ((δ * g)⁻¹ * (g * δ)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, mul_comm (π g) (π δ), inv_mul_cancel]
  have he : c.val (δ * g) = c.val (g * δ) := by
    calc
      c.val (δ * g) = c.val ((δ * g) * u) := by rw [hmul (δ * g) u, hc u hu, map_zero, zero_add]
      _ = c.val (g * δ) := by rw [show (δ * g) * u = g * δ from mul_inv_cancel_left _ _]
  simp only [hmul δ g, hmul g δ, hn, map_zero, add_zero, zero_add] at he
  apply hδ
  change A.rep.ρ δ (c.val g) - c.val g = (A.rep.ρ δ - 1 : Module.End k A.rep) 0
  rw [map_zero, he, sub_self]

/-- A scalar action whose difference from one is a unit allows normalization. -/
theorem subOne_bijective_of_scalar (s : k)
    (hs : A.rep.ρ δ = s • (1 : Module.End k A.rep)) (hu : IsUnit (s - 1)) :
    Function.Bijective (A.rep.ρ δ - 1 : Module.End k A.rep) := by
  obtain ⟨v, hv⟩ := hu
  have he : A.rep.ρ δ - 1 = (v : k) • (1 : Module.End k A.rep) := by
    rw [hs, hv, sub_smul, one_smul]
  rw [he]
  exact (MulAction.toPerm v : A.rep ≃ A.rep).bijective

end Utilities.DiscreteGaloisModule
