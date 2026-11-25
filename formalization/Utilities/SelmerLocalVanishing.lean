module

public import Utilities.SelmerKernel
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]

/-- A cocycle vanishing on a normal subgroup has values invariant under that subgroup. -/
theorem cocycle_value_fixed_of_zero_on_normal
    (A : DiscreteGaloisModule k G) {f : G → A.rep} (hf : f ∈ cocycles₁ A.rep)
    (D : Subgroup G) (hD : D.Normal) (hz : ∀ d ∈ D, f d = 0) (g d : G) (hd : d ∈ D) :
    A.rep.ρ d (f g) = f g := by
  have h := (mem_cocycles₁_iff f).mp hf
  have hd' : g⁻¹ * d * g ∈ D := hD.conj_mem' d hd g
  rw [← add_zero (A.rep.ρ d (f g)), ← hz d hd, ← h d g,
    show d * g = g * (g⁻¹ * d * g) by group, h, hz _ hd']
  simp

private theorem coboundary_mem_continuousCocycles₁ (A : DiscreteGaloisModule k G) (a : A.rep) :
    (fun g => A.rep.ρ g a - a) ∈ A.continuousCocycles₁ :=
  ⟨d₀₁_apply_mem_cocycles₁ (A := A.rep) a, (A.discreteOrbit a).comp (· - a)⟩

/-- The ramified branch of local vanishing: triviality on inertia suffices
when the inertia fixed module is zero. -/
theorem exists_coboundary_of_trivial_on_normal_of_no_fixed
    (A : DiscreteGaloisModule k G) {f : G → A.rep} (hf : f ∈ A.continuousCocycles₁)
    (D : Subgroup G) (hD : D.Normal) (hfixed : ∀ a : A.rep, (∀ d ∈ D, A.rep.ρ d a = a) → a = 0)
    (hloc : ∃ a : A.rep, ∀ d ∈ D, f d = A.rep.ρ d a - a) :
    ∃ a : A.rep, ∀ g, f g = A.rep.ρ g a - a := by
  obtain ⟨a, ha⟩ := hloc
  let f' := f - fun g => A.rep.ρ g a - a
  have hf' : f' ∈ A.continuousCocycles₁ :=
    A.continuousCocycles₁.sub_mem hf (coboundary_mem_continuousCocycles₁ A a)
  have hz (d : G) (hd : d ∈ D) : f' d = 0 := sub_eq_zero.mpr (ha d hd)
  exact ⟨a, fun g => sub_eq_zero.mp (hfixed (f' g) fun d hd =>
    cocycle_value_fixed_of_zero_on_normal A hf'.1 D hD hz g d hd)⟩

/-- Dense generation by one element of the quotient gives dense generation
by that element together with the normal subgroup upstairs. -/
theorem dense_sup_zpowers_of_dense_quotient [IsTopologicalGroup G]
    (D : Subgroup G) [D.Normal] (φ : G)
    (hdense : Dense (Subgroup.zpowers (QuotientGroup.mk' D φ) : Set (G ⧸ D))) :
    Dense ((D ⊔ Subgroup.zpowers φ : Subgroup G) : Set G) := by
  rw [← QuotientGroup.dense_preimage_mk] at hdense
  change Dense (((Subgroup.zpowers (QuotientGroup.mk' D φ)).comap (QuotientGroup.mk' D) :
    Subgroup G) : Set G) at hdense
  rw [← MonoidHom.map_zpowers, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] at hdense
  exact hdense

/-- A locally constant cocycle that vanishes on a subgroup and one
element vanishes on the closed subgroup they generate. -/
theorem cocycle_eq_zero_of_vanishes_on_dense_generators
    (A : DiscreteGaloisModule k G) {f : G → A.rep} (hf : f ∈ A.continuousCocycles₁)
    (D : Subgroup G) (φ : G)
    (hdense : Dense ((D ⊔ Subgroup.zpowers φ : Subgroup G) : Set G))
    (hD : ∀ d ∈ D, f d = 0) (hφ : f φ = 0) (g : G) : f g = 0 := by
  have h := (mem_cocycles₁_iff f).mp hf.1
  have fone : f 1 = 0 := cocycles₁_map_one (⟨f, hf.1⟩ : cocycles₁ A.rep)
  let Z : Subgroup G :=
    { carrier := {g | f g = 0}
      one_mem' := fone
      mul_mem' := fun {g g'} hg hg' => by
        change f g = 0 at hg
        change f g' = 0 at hg'
        change f (g * g') = 0
        simp [h, hg, hg']
      inv_mem' := fun {g} hg => by
        change f g⁻¹ = 0
        have h' := h g⁻¹ g
        change f g = 0 at hg
        simpa [hg, fone] using h'.symm }
  have hle : (D ⊔ Subgroup.zpowers φ : Subgroup G) ≤ Z :=
    sup_le hD (Subgroup.zpowers_le.mpr hφ)
  have hclosed : IsClosed (Z : Set G) := hf.2.isClosed_fiber 0
  exact (hclosed.closure_subset_iff.mpr hle) (hdense g)

/-- The unramified branch of local vanishing: the quotient is generated
densely by Frobenius and the Frobenius minus identity map is surjective. -/
theorem exists_coboundary_of_trivial_inertia_of_frobenius_surjective
    (A : DiscreteGaloisModule k G) {f : G → A.rep} (hf : f ∈ A.continuousCocycles₁)
    (D : Subgroup G) (φ : G)
    (hdense : Dense ((D ⊔ Subgroup.zpowers φ : Subgroup G) : Set G))
    (hact : ∀ d ∈ D, ∀ a : A.rep, A.rep.ρ d a = a)
    (hFrob : Function.Surjective (fun a : A.rep => A.rep.ρ φ a - a))
    (hloc : ∃ a : A.rep, ∀ d ∈ D, f d = A.rep.ρ d a - a) :
    ∃ a : A.rep, ∀ g, f g = A.rep.ρ g a - a := by
  obtain ⟨a, ha⟩ := hFrob (f φ)
  obtain ⟨b, hb⟩ := hloc
  let f' := f - fun g => A.rep.ρ g a - a
  have hf' : f' ∈ A.continuousCocycles₁ :=
    A.continuousCocycles₁.sub_mem hf (coboundary_mem_continuousCocycles₁ A a)
  have hDZ : ∀ d ∈ D, f' d = 0 := by
    intro d hd
    change f d - (A.rep.ρ d a - a) = 0
    simp [hb d hd, hact d hd a, hact d hd b]
  have hφ : f' φ = 0 := sub_eq_zero.mpr ha.symm
  exact ⟨a, fun g => sub_eq_zero.mp
    (cocycle_eq_zero_of_vanishes_on_dense_generators A hf' D φ hdense hDZ hφ g)⟩

end Utilities.DiscreteGaloisModule
