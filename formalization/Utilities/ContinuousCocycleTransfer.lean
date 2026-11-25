module

public import Utilities.SelmerDecomposition
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Algebra.BigOperators.Module
import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
  (A : DiscreteGaloisModule k G) (H : Subgroup G) [H.Normal]

local notation "Q" => G ⧸ H
local notation "p" => QuotientGroup.mk' H
local notation "ρ" => A.rep.ρ

/-- Conjugation preserves a normal subgroup. -/
def normalSubgroupConjugate (g : G) (h : H) : H :=
  ⟨g * h.val * g⁻¹, (inferInstance : H.Normal).conj_mem _ h.property g⟩

variable (s : (G ⧸ H) → G) (hs : Function.RightInverse s (QuotientGroup.mk' H))
include hs

/-- The subgroup element recording the action on a chosen quotient representative. -/
def cocycleTransferAdjustment (g : G) (q : Q) : H :=
  ⟨(s (p g * q))⁻¹ * g * s q, (QuotientGroup.eq_one_iff _).mp (by
    change p ((s (p g * q))⁻¹ * g * s q) = 1
    have hrep (q : Q) : p (s q) = q := hs q
    simp only [map_mul, map_inv, hrep]
    group)⟩

local notation "δ" => cocycleTransferAdjustment H s hs

omit [TopologicalSpace G] in
theorem representative_mul_cocycleTransferAdjustment (g : G) (q : Q) :
    s (p g * q) * (δ g q).val = g * s q := by
  change s (p g * q) * ((s (p g * q))⁻¹ * g * s q) = _
  rw [← mul_assoc, mul_inv_cancel_left]

omit [TopologicalSpace G] in
theorem cocycleTransferAdjustment_mul (g g' : G) (q : Q) :
    δ (g * g') q = δ g (p g' * q) * δ g' q := by
  apply Subtype.ext
  change (s (p (g * g') * q))⁻¹ * (g * g') * s q =
    ((s (p g * (p g' * q)))⁻¹ * g * s (p g' * q)) * ((s (p g' * q))⁻¹ * g' * s q)
  rw [map_mul, mul_assoc (p g)]
  group

variable [Fintype (G ⧸ H)]

/-- Transfer a continuous degree-one cocycle from an open normal subgroup
of finite index. The formula uses any section of the group quotient. -/
noncomputable def continuousCocycleTransfer [IsTopologicalGroup G] (hopen : IsOpen (H : Set G))
    (f : (A.restrictToSubgroup H).continuousCocycles₁) : A.continuousCocycles₁ := by
  let z : H → A.rep := f.val
  let b (g : G) := ∑ q : Q, ρ (s (p g * q)) (z (δ g q))
  have hterm (g g' : G) (q : Q) :
      ρ (s (p (g * g') * q)) (z (δ (g * g') q)) =
        ρ g (ρ (s (p g' * q)) (z (δ g' q))) +
          ρ (s (p g * (p g' * q))) (z (δ g (p g' * q))) := by
    have hf : z (δ g (p g' * q) * δ g' q) =
        ρ (δ g (p g' * q)).val (z (δ g' q)) + z (δ g (p g' * q)) :=
      (mem_cocycles₁_iff _).mp f.property.1 _ _
    have hmul (r : Q) (v : A.rep) :
        ρ (s (p g * r)) (ρ (δ g r).val v) = ρ g (ρ (s r) v) := by
      calc
        _ = ρ (s (p g * r) * (δ g r).val) v :=
          (DFunLike.congr_fun (map_mul ρ _ _) v).symm
        _ = ρ (g * s r) v := by rw [representative_mul_cocycleTransferAdjustment]
        _ = _ := DFunLike.congr_fun (map_mul ρ _ _) v
    rw [cocycleTransferAdjustment_mul, hf, map_add, map_mul p, mul_assoc (p g),
      hmul (p g' * q)]
  refine ⟨b, (mem_cocycles₁_iff b).mpr ?_, ?_⟩
  · intro g g'
    dsimp only [b]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, map_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft (p g')) _ _ (fun _ => rfl)
  · let _ : DiscreteTopology Q := QuotientGroup.discreteTopology hopen
    have hLC (q : Q) : IsLocallyConstant fun g : G => ρ (s (p g * q)) (z (δ g q)) := by
      have hq : Continuous (p : G → Q) := QuotientGroup.continuous_mk
      have hp : Continuous fun g : G => p g * q := hq.mul continuous_const
      have hrep : Continuous fun g : G => s (p g * q) := continuous_of_discreteTopology.comp hp
      have hadj : Continuous fun g : G => δ g q := by
        apply Continuous.subtype_mk
        exact (hrep.inv.mul continuous_id).mul continuous_const
      exact ((IsLocallyConstant.of_discrete s).comp_continuous hp).comp₂
        ((show IsLocallyConstant z from f.property.2).comp_continuous hadj) (fun t x => ρ t x)
    change IsLocallyConstant fun g : G => ∑ q ∈ (Finset.univ : Finset Q), ρ (s (p g * q)) (z (δ g q))
    generalize (Finset.univ : Finset Q) = S
    classical
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (show IsLocallyConstant (fun _ : G => (0 : A.rep)) from IsLocallyConstant.const 0)
    | insert q S hq ih =>
        simp only [Finset.sum_insert hq]
        exact (hLC q).comp₂ ih (· + ·)

/-- Restriction of transfer back to the normal subgroup is the sum
of the conjugate cocycles indexed by the quotient. -/
theorem continuousCocycleTransfer_apply_of_mem [IsTopologicalGroup G]
    (hopen : IsOpen (H : Set G)) (f : (A.restrictToSubgroup H).continuousCocycles₁) (h : H) :
    (continuousCocycleTransfer A H s hs hopen f).val h.val =
      ∑ q : Q, ρ (s q) (f.val (normalSubgroupConjugate H (s q)⁻¹ h)) := by
  change (∑ q : Q, ρ (s (p h.val * q)) (f.val (δ h.val q))) = _
  apply Finset.sum_congr rfl
  intro q _
  have hp₁ : p h.val = 1 := (QuotientGroup.eq_one_iff h.val).mpr h.property
  have hp : p h.val * q = q := by rw [hp₁, one_mul]
  have hadj : δ h.val q = normalSubgroupConjugate H (s q)⁻¹ h := by
    apply Subtype.ext
    change (s (p h.val * q))⁻¹ * h.val * s q = (s q)⁻¹ * h.val * ((s q)⁻¹)⁻¹
    rw [hp, inv_inv]
  rw [hp, hadj]

end Utilities.DiscreteGaloisModule
