module

public import Utilities.ContinuousCohomologyDescent
public import Utilities.SelmerKernelAction

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
  (A : DiscreteGaloisModule k G) (H : Subgroup G)

local notation "Aₕ" => A.restrictToSubgroup H
local notation "ρ" => A.rep.ρ

/-- Local conditions on a subgroup obtained by intersecting with the
local conditions on the ambient group. -/
def subgroupSelmerFamily (D : Set (Subgroup G)) : Set (Subgroup H) :=
  (fun J : Subgroup G => J.comap H.subtype) '' D

/-- Restriction of locally trivial cocycles to the intersection family. -/
def restrictLocallyTrivialCocycles (D : Set (Subgroup G)) :
    A.locallyTrivialCocycles₁ D →ₗ[k] (Aₕ).locallyTrivialCocycles₁ (subgroupSelmerFamily H D) where
  toFun f := ⟨fun h => f.val h.val, A.restrict_mem_continuousCocycles₁ H f.property.1, by
    rintro _ ⟨J, hJ, rfl⟩
    obtain ⟨a, ha⟩ := f.property.2 J hJ
    exact ⟨a, fun x hx => ha x.val hx⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction on the Selmer kernel, with local conditions intersected
with the subgroup. -/
def restrictSelmerKernel (D : Set (Subgroup G)) :
    A.selmerKernel D →ₗ[k] (Aₕ).selmerKernel (subgroupSelmerFamily H D) := by
  let C := A.locallyTrivialCocycles₁ D
  let C' := (Aₕ).locallyTrivialCocycles₁ (subgroupSelmerFamily H D)
  let B := (coboundaries₁ A.rep).comap C.subtype
  let B' := (coboundaries₁ (Aₕ).rep).comap C'.subtype
  refine B.mapQ B' (restrictLocallyTrivialCocycles A H D) ?_
  intro f hf
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, funext fun h => congrFun ha h.val⟩

variable [H.Normal]

/-- With invertible subgroup index the Selmer restriction is injective. -/
theorem restrictSelmerKernel_injective [Finite (G ⧸ H)]
    (hunit : IsUnit (Nat.card (G ⧸ H) : k)) (D : Set (Subgroup G)) :
    Function.Injective (restrictSelmerKernel A H D) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  let C := A.locallyTrivialCocycles₁ D
  let C' := (Aₕ).locallyTrivialCocycles₁ (subgroupSelmerFamily H D)
  let B := (coboundaries₁ A.rep).comap C.subtype
  let B' := (coboundaries₁ (Aₕ).rep).comap C'.subtype
  obtain ⟨f, rfl⟩ := B.mkQ_surjective x
  have hzero : B'.mkQ (restrictLocallyTrivialCocycles A H D f) = 0 := hx
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero B').mp hzero
  let z : cocycles₁ A.rep := ⟨f.val, f.property.1.1⟩
  obtain ⟨b, hb⟩ := exists_coboundary_of_restriction_eq_coboundary A H hunit z
    ⟨a, fun h => (congrFun ha h).symm⟩
  rw [Submodule.mem_bot]
  exact (Submodule.Quotient.mk_eq_zero B).mpr ⟨b, funext fun g => (hb g).symm⟩

/-- The conjugation homomorphism on a normal subgroup. -/
def normalSubgroupConjugateHom (g : G) : H →* H where
  toFun := normalSubgroupConjugate H g
  map_one' := by apply Subtype.ext; change g * 1 * g⁻¹ = 1; simp
  map_mul' x y := by
    apply Subtype.ext
    change g * (x.val * y.val) * g⁻¹ = (g * x.val * g⁻¹) * (g * y.val * g⁻¹)
    group

omit [TopologicalSpace G] in
/-- Intersecting local conditions with a normal subgroup commutes with
conjugating them by an ambient element. -/
theorem map_comap_normalSubgroupConjugateHom (J : Subgroup G) (g : G) :
    (J.comap H.subtype).map (normalSubgroupConjugateHom H g) =
      (J.map (MulAut.conj g).toMonoidHom).comap H.subtype := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y.val, hy, congrArg Subtype.val he⟩
  · rintro ⟨y, hy, he⟩
    have hc : g * y * g⁻¹ = x.val := he
    have hinv : g⁻¹ * x.val * g = y := by
      rw [← hc]
      group
    have hyH : y ∈ H := by
      rw [← hinv]
      simpa only [inv_inv] using (inferInstance : H.Normal).conj_mem _ x.property g⁻¹
    exact ⟨⟨y, hyH⟩, hy, Subtype.ext hc⟩

omit [TopologicalSpace G] in
theorem subgroupSelmerFamily_stable_under_conjugation (D : Set (Subgroup G))
    (hD : ∀ g : G, ∀ J ∈ D, J.map (MulAut.conj g).toMonoidHom ∈ D)
    (g : G) {J : Subgroup H} (hJ : J ∈ subgroupSelmerFamily H D) :
    J.map (normalSubgroupConjugateHom H g) ∈ subgroupSelmerFamily H D := by
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  rw [map_comap_normalSubgroupConjugateHom]
  exact ⟨J₀.map (MulAut.conj g).toMonoidHom, hD g J₀ hJ₀, rfl⟩

theorem continuous_normalSubgroupConjugateHom [IsTopologicalGroup G] (g : G) :
    Continuous (normalSubgroupConjugateHom H g) := by
  apply Continuous.subtype_mk
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem normalSubgroupConjugation_intertwines (g : G) (h : H) (a : (Aₕ).rep) :
    ρ g ((Aₕ).rep.ρ (normalSubgroupConjugateHom H g⁻¹ h) a) =
      (Aₕ).rep.ρ h (ρ g a) := by
  let v : A.rep := a
  let φ := normalSubgroupConjugateHom H g⁻¹
  change ρ g (ρ (φ h).val v) = ρ h.val (ρ g v)
  have he : g * (φ h).val = h.val * g := by
    change g * (g⁻¹ * h.val * (g⁻¹)⁻¹) = h.val * g
    group
  calc
    _ = ρ (g * (φ h).val) v := (DFunLike.congr_fun (map_mul ρ _ _) v).symm
    _ = ρ (h.val * g) v := by rw [he]
    _ = _ := DFunLike.congr_fun (map_mul ρ _ _) v

/-- Ambient conjugation on locally trivial cocycles of a normal subgroup. -/
@[no_expose]
def normalSubgroupConjugateCocycle [IsTopologicalGroup G] (D' : Set (Subgroup H)) (g : G)
    (hgroups : ∀ J ∈ D', J.map (normalSubgroupConjugateHom H g⁻¹) ∈ D') :
    (Aₕ).locallyTrivialCocycles₁ D' →ₗ[k] (Aₕ).locallyTrivialCocycles₁ D' :=
  (Aₕ).pullbackLocallyTrivialCocycles₁ D' (normalSubgroupConjugateHom H g⁻¹)
    (continuous_normalSubgroupConjugateHom H _) (ρ g)
    (normalSubgroupConjugation_intertwines A H g) hgroups

theorem normalSubgroupConjugateCocycle_apply [IsTopologicalGroup G] (D' : Set (Subgroup H)) (g : G)
    (hgroups : ∀ J ∈ D', J.map (normalSubgroupConjugateHom H g⁻¹) ∈ D')
    (f : (Aₕ).locallyTrivialCocycles₁ D') (h : H) :
    (normalSubgroupConjugateCocycle A H D' g hgroups f).val h =
      ρ g (f.val (normalSubgroupConjugate H g⁻¹ h)) := by
  unfold normalSubgroupConjugateCocycle
  rfl

/-- Conjugation by an ambient group element on a normal-subgroup Selmer
kernel with a conjugation-invariant local family. -/
@[no_expose]
def normalSubgroupSelmerConjugation [IsTopologicalGroup G] (D' : Set (Subgroup H)) (g : G)
    (hgroups : ∀ J ∈ D', J.map (normalSubgroupConjugateHom H g⁻¹) ∈ D') :
    (Aₕ).selmerKernel D' →ₗ[k] (Aₕ).selmerKernel D' :=
  (Aₕ).pullbackSelmerKernel D' (normalSubgroupConjugateHom H g⁻¹)
    (continuous_normalSubgroupConjugateHom H _) (ρ g)
    (normalSubgroupConjugation_intertwines A H g) hgroups

theorem normalSubgroupSelmerConjugation_eq_pullback [IsTopologicalGroup G]
    (D' : Set (Subgroup H)) (g : G)
    (hgroups : ∀ J ∈ D', J.map (normalSubgroupConjugateHom H g⁻¹) ∈ D') :
    normalSubgroupSelmerConjugation A H D' g hgroups =
      (Aₕ).pullbackSelmerKernel D' (normalSubgroupConjugateHom H g⁻¹)
        (continuous_normalSubgroupConjugateHom H _) (ρ g)
        (normalSubgroupConjugation_intertwines A H g) hgroups := by
  unfold normalSubgroupSelmerConjugation
  rfl

theorem normalSubgroupSelmerConjugation_mk [IsTopologicalGroup G] (D' : Set (Subgroup H)) (g : G)
    (hgroups : ∀ J ∈ D', J.map (normalSubgroupConjugateHom H g⁻¹) ∈ D')
    (f : (Aₕ).locallyTrivialCocycles₁ D') :
    normalSubgroupSelmerConjugation A H D' g hgroups (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (normalSubgroupConjugateCocycle A H D' g hgroups f) := by
  unfold normalSubgroupSelmerConjugation normalSubgroupConjugateCocycle
  rfl

/-- Every invariant Selmer class for the intersection family descends
to the ambient group when the finite index is invertible. -/
theorem mem_range_restrictSelmerKernel_of_invariant [Finite (G ⧸ H)] [IsTopologicalGroup G]
    (hopen : IsOpen (H : Set G)) (hunit : IsUnit (Nat.card (G ⧸ H) : k))
    (D : Set (Subgroup G))
    (hgroups : ∀ (g : G) (J : Subgroup H), J ∈ subgroupSelmerFamily H D →
      J.map (normalSubgroupConjugateHom H g⁻¹) ∈ subgroupSelmerFamily H D)
    (x : (Aₕ).selmerKernel (subgroupSelmerFamily H D))
    (hinv : ∀ g : G, normalSubgroupSelmerConjugation A H _ g (hgroups g) x = x) :
    x ∈ LinearMap.range (restrictSelmerKernel A H D) := by
  let D' := subgroupSelmerFamily H D
  let B := (coboundaries₁ A.rep).comap (A.locallyTrivialCocycles₁ D).subtype
  let B' := (coboundaries₁ (Aₕ).rep).comap ((Aₕ).locallyTrivialCocycles₁ D').subtype
  obtain ⟨f, rfl⟩ := B'.mkQ_surjective x
  have hfixed (g : G) : ∃ a : A.rep, ∀ h : H,
      ρ g (f.val (normalSubgroupConjugate H g⁻¹ h)) =
        (show A.rep from f.val h) + (ρ h.val a - a) := by
    have h := hinv g
    change B'.mkQ _ = B'.mkQ f at h
    rw [← sub_eq_zero, ← map_sub] at h
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero B').mp h
    refine ⟨a, fun v => ?_⟩
    let z : (Aₕ).rep := ρ g (f.val (normalSubgroupConjugate H g⁻¹ v))
    let d : (Aₕ).rep := (Aₕ).rep.ρ v a - a
    have hv : d = z - f.val v := congrFun ha v
    have hz : z = f.val v + d := by
      rw [hv, add_comm (f.val v), sub_add_cancel]
    exact hz
  obtain ⟨z, hz⟩ := exists_locallyTrivialCocycle_of_invariant_restriction A H hopen hunit D D'
    (fun J hJ => ⟨J, hJ, rfl⟩) f hfixed
  refine ⟨B.mkQ z, ?_⟩
  change B'.mkQ (restrictLocallyTrivialCocycles A H D z) = B'.mkQ f
  exact congrArg B'.mkQ (Subtype.ext (funext hz))

/-- Restricted Selmer classes are fixed by ambient conjugation. The
coboundary witnessing this is the value of the ambient cocycle at the
conjugating element. -/
theorem restrictSelmerKernel_fixed_by_conjugation [IsTopologicalGroup G]
    (D : Set (Subgroup G)) (g : G)
    (hgroups : ∀ J ∈ subgroupSelmerFamily H D,
      J.map (normalSubgroupConjugateHom H g⁻¹) ∈ subgroupSelmerFamily H D)
    (x : A.selmerKernel D) :
    normalSubgroupSelmerConjugation A H _ g hgroups (restrictSelmerKernel A H D x) =
      restrictSelmerKernel A H D x := by
  let D' := subgroupSelmerFamily H D
  let B := (coboundaries₁ A.rep).comap (A.locallyTrivialCocycles₁ D).subtype
  let B' := (coboundaries₁ (Aₕ).rep).comap ((Aₕ).locallyTrivialCocycles₁ D').subtype
  obtain ⟨f, rfl⟩ := B.mkQ_surjective x
  change B'.mkQ _ = B'.mkQ (restrictLocallyTrivialCocycles A H D f)
  rw [← sub_eq_zero, ← map_sub]
  apply (Submodule.Quotient.mk_eq_zero B').mpr
  let z : cocycles₁ A.rep := ⟨f.val, f.property.1.1⟩
  refine ⟨f.val g, funext fun h => ?_⟩
  change ρ h.val (f.val g) - f.val g =
    ρ g (f.val (g⁻¹ * h.val * (g⁻¹)⁻¹)) - f.val h.val
  rw [inv_inv]
  exact (A.inner_pullback_sub_eq_coboundary z g h.val).symm

/-- For invertible index, the image of Selmer restriction consists exactly
of the classes fixed by ambient conjugation. -/
theorem mem_range_restrictSelmerKernel_iff_invariant [Finite (G ⧸ H)] [IsTopologicalGroup G]
    (hopen : IsOpen (H : Set G)) (hunit : IsUnit (Nat.card (G ⧸ H) : k))
    (D : Set (Subgroup G))
    (hgroups : ∀ (g : G) (J : Subgroup H), J ∈ subgroupSelmerFamily H D →
      J.map (normalSubgroupConjugateHom H g⁻¹) ∈ subgroupSelmerFamily H D)
    (x : (Aₕ).selmerKernel (subgroupSelmerFamily H D)) :
    x ∈ LinearMap.range (restrictSelmerKernel A H D) ↔
      ∀ g : G, normalSubgroupSelmerConjugation A H _ g (hgroups g) x = x := by
  constructor
  · rintro ⟨z, rfl⟩ g
    exact restrictSelmerKernel_fixed_by_conjugation A H D g (hgroups g) z
  · exact mem_range_restrictSelmerKernel_of_invariant A H hopen hunit D hgroups x

/-- Restriction identifies the ambient Selmer kernel with the fixed
submodule of the normal-subgroup Selmer kernel. -/
noncomputable def selmerRestrictionEquivInvariants [Finite (G ⧸ H)] [IsTopologicalGroup G]
    (hopen : IsOpen (H : Set G)) (hunit : IsUnit (Nat.card (G ⧸ H) : k))
    (D : Set (Subgroup G))
    (hgroups : ∀ (g : G) (J : Subgroup H), J ∈ subgroupSelmerFamily H D →
      J.map (normalSubgroupConjugateHom H g⁻¹) ∈ subgroupSelmerFamily H D) :
    A.selmerKernel D ≃ₗ[k] ↥(⨅ g : G,
      LinearMap.ker (normalSubgroupSelmerConjugation A H _ g (hgroups g) - LinearMap.id)) := by
  have he : LinearMap.range (restrictSelmerKernel A H D) =
      ⨅ g : G, LinearMap.ker (normalSubgroupSelmerConjugation A H _ g (hgroups g) - LinearMap.id) := by
    ext x
    rw [mem_range_restrictSelmerKernel_iff_invariant A H hopen hunit D hgroups, Submodule.mem_iInf]
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact (LinearEquiv.ofInjective _ (restrictSelmerKernel_injective A H hunit D)).trans
    (LinearEquiv.ofEq _ _ he)

end Utilities.DiscreteGaloisModule
