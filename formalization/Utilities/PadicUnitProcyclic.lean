module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open scoped Topology

namespace Utilities

private theorem nonempty_iInter_of_antitone_closed {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (S : ℕ → Set X) (hmono : Antitone S) (hclosed : ∀ n, IsClosed (S n))
    (hne : ∀ n, (S n).Nonempty) : (⋂ n, S n).Nonempty :=
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S
    (fun m n => ⟨max m n, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
    hne (fun n => (hclosed n).isCompact) hclosed

private theorem isLocallyConstant_padicInt_toZModPow (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) n) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  let δ := (p : ℝ) ^ (-(n : ℤ))
  refine ⟨{y | ‖y - x‖ < δ}, isOpen_lt (continuous_id.sub continuous_const).norm continuous_const,
    ?_, ?_⟩
  · change ‖x - x‖ < δ
    simpa only [sub_self, norm_zero] using zpow_pos hp (-(n : ℤ))
  · intro y hy
    have hle : ‖y - x‖ ≤ δ := le_of_lt hy
    have hker := (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) n).mp hle
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hker
    exact hker

/-- A closed subgroup of the units of the odd p-adic integers has a dense
cyclic subgroup. Choose compatible generators using compactness, and use
all finite reductions to verify density. -/
theorem exists_denseRange_zpow_closedSubgroup_padicUnits (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (H : Subgroup ℤ_[p]ˣ) (hH : IsClosed (H : Set ℤ_[p]ˣ)) :
    ∃ x : H, DenseRange (fun j : ℤ => x ^ j) := by
  let _ : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let r (n : ℕ) : H →* (ZMod (p ^ n))ˣ :=
    (Units.map (PadicInt.toZModPow (p := p) n).toMonoidHom).comp H.subtype
  have hloc (n : ℕ) : IsLocallyConstant (r n) := by
    have hv : IsLocallyConstant (fun x : H => PadicInt.toZModPow (p := p) n ((x : ℤ_[p]ˣ) : ℤ_[p])) :=
      (isLocallyConstant_padicInt_toZModPow p n).comp_continuous
        (Units.continuous_val.comp continuous_subtype_val)
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    exact (hv.eventually_eq x).mono fun _ h => Units.ext h
  have hred {m n : ℕ} (hmn : m ≤ n) (x : H) :
      ZMod.unitsMap (pow_dvd_pow p hmn) (r n x) = r m x := by
    apply Units.ext
    rw [ZMod.unitsMap_val]
    exact PadicInt.cast_toZModPow m n hmn ((x : ℤ_[p]ˣ) : ℤ_[p])
  have heq_red {m n : ℕ} (hmn : m ≤ n) {x y : H} (h : r n x = r n y) :
      r m x = r m y := by
    rw [← hred hmn x, ← hred hmn y, h]
  let S (n : ℕ) : Set H := {x | ∀ y : H, ∃ j : ℤ, r n (x ^ j) = r n y}
  have hSclosed (n : ℕ) : IsClosed (S n) := by
    have hS : S n = (r n) ⁻¹' {a | ∀ y : H, ∃ j : ℤ, a ^ j = r n y} := by
      ext x
      simp [S, map_zpow]
    rw [hS, ← isOpen_compl_iff, ← Set.preimage_compl]
    exact hloc n _
  have hSmono : Antitone S := by
    intro m n hmn x hx y
    obtain ⟨j, hj⟩ := hx y
    exact ⟨j, heq_red hmn hj⟩
  have hSnonempty (n : ℕ) : (S n).Nonempty := by
    let _ : IsCyclic (ZMod (p ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow p Fact.out hp n
    obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (r n).range)
    obtain ⟨x, hx⟩ := (r n).rangeRestrict_surjective u
    refine ⟨x, fun y => ?_⟩
    obtain ⟨j, hj⟩ := hu ((r n).rangeRestrict y)
    refine ⟨j, ?_⟩
    have hh := congrArg (fun z : (r n).range => z.val) hj
    change u.val ^ j = r n y at hh
    rw [map_zpow, show r n x = u.val from congrArg (fun z : (r n).range => z.val) hx]
    exact hh
  obtain ⟨x, hx⟩ := nonempty_iInter_of_antitone_closed S hSmono hSclosed hSnonempty
  have hx' := Set.mem_iInter.mp hx
  refine ⟨x, fun y => ?_⟩
  let C := closure (Set.range fun j : ℤ => x ^ j)
  let D (n : ℕ) := C ∩ {z : H | r n z = r n y}
  have hDclosed (n : ℕ) : IsClosed (D n) := isClosed_closure.inter ((hloc n).isClosed_fiber _)
  have hDmono : Antitone D := by
    intro m n hmn z hz
    exact ⟨hz.1, heq_red hmn hz.2⟩
  have hDnonempty (n : ℕ) : (D n).Nonempty := by
    obtain ⟨j, hj⟩ := hx' n y
    exact ⟨x ^ j, subset_closure ⟨j, rfl⟩, hj⟩
  obtain ⟨z, hz⟩ := nonempty_iInter_of_antitone_closed D hDmono hDclosed hDnonempty
  have hz' := Set.mem_iInter.mp hz
  have heq : z = y := by
    apply Subtype.ext
    apply Units.ext
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    exact congrArg (fun u : (ZMod (p ^ n))ˣ => u.val) (hz' n).2
  exact heq ▸ (hz' 0).1

end Utilities
