module

public import Utilities.FiniteIndexCocycle
public import Utilities.SelmerKernelTorsion
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section

open groupCohomology Filter

namespace Utilities

/-- Locally constant homomorphisms to an additive coefficient group that
vanish on the specified subgroups. -/
def locallyTrivialContinuousHom (G M : Type) [Group G] [TopologicalSpace G]
    [AddCommGroup M] (S : Set (Subgroup G)) : Set (G →* Multiplicative M) :=
  {f | IsLocallyConstant f ∧ ∀ D ∈ S, ∀ g ∈ D, f g = 1}

/-- Transport the continuous homomorphisms and their local triviality
conditions along a topological group isomorphism. -/
def locallyTrivialContinuousHomCongr {G G' M : Type} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] [AddCommGroup M] (e : G ≃ₜ* G')
    {S : Set (Subgroup G)} {T : Set (Subgroup G')}
    (hT : (fun D => D.map e.toMonoidHom) '' S = T) :
    locallyTrivialContinuousHom G M S ≃ locallyTrivialContinuousHom G' M T where
  toFun f := ⟨f.val.comp e.symm.toMonoidHom, f.property.1.comp_continuous e.symm.continuous_toFun,
    fun D hD g hg => by
      obtain ⟨I, hI, rfl⟩ := hT.symm ▸ hD
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
      change f.val (e.symm (e x)) = 1
      rw [e.symm_apply_apply]
      exact f.property.2 I hI x hx⟩
  invFun f := ⟨f.val.comp e.toMonoidHom, f.property.1.comp_continuous e.continuous_toFun,
    fun D hD g hg => f.property.2 (D.map e.toMonoidHom) (hT ▸ Set.mem_image_of_mem _ hD)
      (e g) (Subgroup.mem_map_of_mem _ hg)⟩
  left_inv f := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    change f.val (e.symm (e x)) = f.val x
    rw [e.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    change f.val (e (e.symm x)) = f.val x
    rw [e.apply_symm_apply]

namespace DiscreteGaloisModule

variable {R G : Type} [CommRing R] [Group G] [TopologicalSpace G]

/-- Choose scalar-killed representatives and restrict to a subgroup on which
their values form a homomorphism. Finite-index averaging proves injectivity,
without requiring the choice of representatives to be canonical. -/
theorem exists_injective_torsionBy_to_locallyTrivialContinuousHom
    (A : DiscreteGaloisModule R G) (S : Set (Subgroup G))
    (H : Subgroup G) [Finite (G ⧸ H)] (T : Set (Subgroup H)) (a : R)
    (hdiv : Function.Surjective (fun x : A.rep => a • x))
    (hindex : IsUnit (H.index : R))
    (htriv : ∀ g ∈ H, ∀ x : A.rep, a • x = 0 → A.rep.ρ g x = x)
    (hloc : ∀ D ∈ T, ∃ I ∈ S, D.map H.subtype ≤ I ∧ ∀ g ∈ D, A.rep.ρ (g : G) = 1) :
    ∃ f : Submodule.torsionBy R (A.selmerKernel S) a →
      locallyTrivialContinuousHom H (Submodule.torsionBy R A.rep a) T, Function.Injective f := by
  classical
  let C := A.locallyTrivialCocycles₁ S
  let B := (coboundaries₁ A.rep).comap C.subtype
  let V := Submodule.torsionBy R (A.selmerKernel S) a
  let D := Submodule.torsionBy R C a
  let M := Submodule.torsionBy R A.rep a
  have hmap : D.map B.mkQ = V := A.map_torsionBy_mkQ_eq S a hdiv
  have hrepresentative (z : V) : ∃ f : D, B.mkQ f.val = z.val := by
    have hz : z.val ∈ D.map B.mkQ := hmap.symm ▸ z.property
    obtain ⟨f, hDf, hf⟩ := hz
    exact ⟨⟨f, hDf⟩, hf⟩
  choose c hc using hrepresentative
  have htors (z : V) (g : G) : a • (c z).val.val g = 0 := by
    have h : a • (c z).val = 0 := (c z).property
    exact congrFun (congrArg (fun u : C => u.val) h) g
  let v (z : V) (g : H) : M := ⟨(c z).val.val g, htors z g⟩
  let φ (z : V) : H →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (v z g)
      map_one' := by
        change v z (1 : H) = 0
        apply Subtype.ext
        let f : cocycles₁ A.rep := ⟨(c z).val.val, (c z).val.property.1.1⟩
        exact cocycles₁_map_one f
      map_mul' := by
        intro g h
        change v z (g * h) = v z g + v z h
        apply Subtype.ext
        change (c z).val.val ((g : G) * (h : G)) = (c z).val.val g + (c z).val.val h
        have hcoc := (mem_cocycles₁_iff ((c z).val.val)).mp (c z).val.property.1.1
        rw [hcoc, htriv g g.property _ (htors z h), add_comm] }
  have hlocal (z : V) : φ z ∈ locallyTrivialContinuousHom H M T := by
    constructor
    · have hLC : IsLocallyConstant (fun g : H => (c z).val.val g) :=
        (c z).val.property.1.2.comp_continuous continuous_subtype_val
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      filter_upwards [((IsLocallyConstant.iff_eventually_eq _).mp hLC g)] with h hh
      change v z h = v z g
      exact Subtype.ext hh
    · intro D hD g hg
      obtain ⟨I, hI, hsub, hρ⟩ := hloc D hD
      obtain ⟨b, hb⟩ := (c z).val.property.2 I hI
      change v z g = 0
      apply Subtype.ext
      change (c z).val.val g = 0
      have hm := hb g (hsub (Subgroup.mem_map_of_mem H.subtype hg))
      rw [hρ g hg, one_apply_eq_self, sub_self] at hm
      exact hm
  refine ⟨fun z => ⟨φ z, hlocal z⟩, ?_⟩
  intro z w hw
  have hφ : φ z = φ w := congrArg Subtype.val hw
  let d : C := (c z).val - (c w).val
  have hz (g : G) (hg : g ∈ H) : d.val g = 0 := by
    have heq := congrArg (fun ψ : H →* Multiplicative M =>
      (Multiplicative.toAdd (ψ ⟨g, hg⟩)).val) hφ
    change (c z).val.val g = (c w).val.val g at heq
    change (c z).val.val g - (c w).val.val g = 0
    exact sub_eq_zero.mpr heq
  have hboundary : d.val ∈ coboundaries₁ A.rep :=
    cocycle_mem_coboundaries_of_vanishing_on_finiteIndex A.rep H d.val d.property.1.1 hz hindex
  apply Subtype.ext
  rw [← hc z, ← hc w, ← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero B).mpr hboundary

end DiscreteGaloisModule
end Utilities
