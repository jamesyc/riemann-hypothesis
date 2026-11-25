module

public import Utilities.SelmerDecomposition
public import Utilities.SelmerKernelAction
import Mathlib.Tactic.Abel

@[expose] public section

open groupCohomology
open scoped Pointwise

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
  (A : DiscreteGaloisModule k G)

local notation "ρ" => A.rep.ρ

/-- Cochains that are coboundaries on each specified subgroup with
witnesses annihilated by the same scalar. -/
def boundedLocalWitnesses (D : Set (Subgroup G)) (a : k) : Submodule k (G → A.rep) where
  carrier := {f | ∀ J ∈ D, ∃ b : A.rep, a • b = 0 ∧ ∀ g ∈ J, f g = ρ g b - b}
  zero_mem' := fun _ _ => ⟨0, smul_zero _, fun _ _ => by simp⟩
  add_mem' hf hg := by
    intro J hJ
    obtain ⟨b, hb, hfb⟩ := hf J hJ
    obtain ⟨c, hc, hgc⟩ := hg J hJ
    refine ⟨b + c, by rw [smul_add, hb, hc, add_zero], fun g hgJ => ?_⟩
    change _ + _ = ρ g (b + c) - (b + c)
    rw [hfb g hgJ, hgc g hgJ, map_add]
    abel
  smul_mem' r f hf := by
    intro J hJ
    obtain ⟨b, hb, hfb⟩ := hf J hJ
    refine ⟨r • b, by rw [smul_comm a r, hb, smul_zero], fun g hgJ => ?_⟩
    change r • f g = ρ g (r • b) - r • b
    rw [hfb g hgJ, map_smul, smul_sub]

theorem boundedLocalWitnesses_mono {D : Set (Subgroup G)} {a b : k} (hab : a ∣ b) :
    A.boundedLocalWitnesses D a ≤ A.boundedLocalWitnesses D b := by
  obtain ⟨c, rfl⟩ := hab
  intro f hf J hJ
  obtain ⟨x, hx, h⟩ := hf J hJ
  exact ⟨x, by rw [mul_comm, mul_smul, hx, smul_zero], h⟩

/-- A coboundary witness on a conjugate subgroup is obtained by subtracting
the value of the cocycle at the conjugating element. -/
theorem coboundary_on_conjugate_subgroup (f : cocycles₁ A.rep)
    (J : Subgroup G) (s : G) (b : A.rep)
    (h : ∀ g ∈ J, f.val g = ρ g b - b) :
    ∀ g ∈ J.map (MulAut.conj s).toMonoidHom,
      f.val g = ρ g (ρ s b - f.val s) - (ρ s b - f.val s) := by
  intro g hg
  obtain ⟨t, ht, he⟩ := Subgroup.mem_map.mp hg
  change s * t * s⁻¹ = g at he
  have hc : s⁻¹ * g * s = t := by rw [← he]; group
  have hm : s * t = g * s := by rw [← he]; group
  have hcomp : ρ s (ρ t b) = ρ g (ρ s b) := by
    calc
      _ = ρ (s * t) b := (DFunLike.congr_fun (map_mul ρ s t) b).symm
      _ = ρ (g * s) b := by rw [hm]
      _ = _ := DFunLike.congr_fun (map_mul ρ g s) b
  have hinner := A.inner_pullback_sub_eq_coboundary f s g
  change ρ s (f.val (s⁻¹ * g * s)) - f.val g = ρ g (f.val s) - f.val s at hinner
  rw [hc, h t ht, map_sub, hcomp] at hinner
  rw [map_sub]
  calc
    f.val g = (ρ g (ρ s b) - ρ s b) - (ρ g (f.val s) - f.val s) := by
      apply eq_sub_of_add_eq
      exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hinner).symm
    _ = _ := by abel

variable {R : Type} [Ring R] [MulSemiringAction G R]

/-- If one inertia element acts with an injective difference from the
identity, local triviality on inertia gives a bounded decomposition witness. -/
theorem exists_bounded_witness_on_stabilizer_of_inertia
    (P : Ideal R) {f : G → A.rep} (hf : f ∈ A.continuousCocycles₁)
    (a : k) (hkill : ∀ g, a • f g = 0)
    (hI : ∃ b : A.rep, ∀ g ∈ P.inertia G, f g = ρ g b - b)
    (s : G) (hs : s ∈ P.inertia G)
    (hinj : Function.Injective (ρ s - 1 : Module.End k A.rep)) :
    ∃ b : A.rep, a • b = 0 ∧ ∀ g ∈ MulAction.stabilizer G P, f g = ρ g b - b := by
  let d : Module.End k A.rep := ρ s - 1
  have hfixed (x : A.rep) (hx : ∀ g ∈ P.inertia G, ρ g x = x) : x = 0 := by
    apply hinj
    change ρ s x - x = d 0
    rw [hx s hs, sub_self, map_zero]
  obtain ⟨b, hb⟩ := A.exists_coboundary_on_stabilizer_of_inertia_no_fixed P hf hfixed hI
  refine ⟨b, ?_, hb⟩
  apply hinj
  change d (a • b) = d 0
  have hsb : d b = f s := (hb s (P.inertia_le_stabilizer hs)).symm
  rw [map_smul, hsb, hkill, map_zero]

end Utilities.DiscreteGaloisModule
