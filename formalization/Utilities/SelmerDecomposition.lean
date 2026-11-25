module

public import Utilities.SelmerLocalVanishing
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.Topology.Algebra.Group.Subgroup

@[expose] public section

open groupCohomology
open scoped Pointwise

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]

/-- Restrict the same continuous coefficient representation to a subgroup. -/
def restrictToSubgroup (A : DiscreteGaloisModule k G) (D : Subgroup G) :
    DiscreteGaloisModule k D where
  rep := A.rep.res D.subtype
  discreteOrbit a := (A.discreteOrbit a).comp_continuous continuous_subtype_val

theorem restrict_mem_continuousCocycles₁ (A : DiscreteGaloisModule k G)
    (D : Subgroup G) {f : G → A.rep} (hf : f ∈ A.continuousCocycles₁) :
    (fun d : D => f d.val) ∈ (A.restrictToSubgroup D).continuousCocycles₁ := by
  refine ⟨(mem_cocycles₁_iff _).mpr fun d e => ?_, hf.2.comp_continuous continuous_subtype_val⟩
  exact (mem_cocycles₁_iff _).mp hf.1 d.val e.val

variable {B : Type} [Ring B] [MulSemiringAction G B]

/-- For the actual decomposition subgroup at an ideal, normality of inertia
is supplied by Mathlib. This is the ramified local vanishing criterion. -/
theorem exists_coboundary_on_stabilizer_of_inertia_no_fixed
    (A : DiscreteGaloisModule k G) (P : Ideal B) {f : G → A.rep}
    (hf : f ∈ A.continuousCocycles₁)
    (hfixed : ∀ a : A.rep, (∀ d ∈ P.inertia G, A.rep.ρ d a = a) → a = 0)
    (hI : ∃ a : A.rep, ∀ d ∈ P.inertia G, f d = A.rep.ρ d a - a) :
    ∃ a : A.rep, ∀ d ∈ MulAction.stabilizer G P, f d = A.rep.ρ d a - a := by
  let D := MulAction.stabilizer G P
  let I := P.inertia D
  have hzero (a : A.rep) (ha : ∀ d ∈ I, A.rep.ρ d.val a = a) : a = 0 :=
    hfixed a fun g hg => ha ⟨g, P.inertia_le_stabilizer hg⟩ (P.coe_mem_inertia.mp hg)
  obtain ⟨a, ha⟩ := hI
  have hloc : ∃ a : A.rep, ∀ g ∈ I, f g.val = A.rep.ρ g.val a - a :=
    ⟨a, fun g hg => ha g.val (P.coe_mem_inertia.mpr hg)⟩
  obtain ⟨b, hb⟩ := exists_coboundary_of_trivial_on_normal_of_no_fixed
    (A.restrictToSubgroup D) (A.restrict_mem_continuousCocycles₁ D hf) I inferInstance
    hzero hloc
  exact ⟨b, fun g hg => hb ⟨g, hg⟩⟩

/-- The unramified local vanishing criterion on the decomposition subgroup.
The Frobenius element is specified in the quotient by its normal inertia subgroup. -/
theorem exists_coboundary_on_stabilizer_of_unramified [IsTopologicalGroup G]
    (A : DiscreteGaloisModule k G) (P : Ideal B) {f : G → A.rep}
    (hf : f ∈ A.continuousCocycles₁)
    (hact : ∀ d ∈ P.inertia G, ∀ a : A.rep, A.rep.ρ d a = a)
    (hI : ∃ a : A.rep, ∀ d ∈ P.inertia G, f d = A.rep.ρ d a - a)
    (φ : MulAction.stabilizer G P)
    (hdense : Dense (Subgroup.zpowers (QuotientGroup.mk' (P.inertia (MulAction.stabilizer G P)) φ) :
      Set (MulAction.stabilizer G P ⧸ P.inertia (MulAction.stabilizer G P))))
    (hFrob : Function.Surjective (fun a : A.rep => A.rep.ρ φ.val a - a)) :
    ∃ a : A.rep, ∀ d ∈ MulAction.stabilizer G P, f d = A.rep.ρ d a - a := by
  let D := MulAction.stabilizer G P
  let I := P.inertia D
  have htriv (g : D) (hg : g ∈ I) (a : A.rep) : A.rep.ρ g.val a = a :=
    hact g.val (P.coe_mem_inertia.mpr hg) a
  obtain ⟨a, ha⟩ := hI
  have hloc : ∃ a : A.rep, ∀ g ∈ I, f g.val = A.rep.ρ g.val a - a :=
    ⟨a, fun g hg => ha g.val (P.coe_mem_inertia.mpr hg)⟩
  obtain ⟨b, hb⟩ := exists_coboundary_of_trivial_inertia_of_frobenius_surjective
    (A.restrictToSubgroup D) (A.restrict_mem_continuousCocycles₁ D hf) I φ
    (dense_sup_zpowers_of_dense_quotient I φ hdense) htriv hFrob hloc
  exact ⟨b, fun g hg => hb ⟨g, hg⟩⟩

end Utilities.DiscreteGaloisModule
