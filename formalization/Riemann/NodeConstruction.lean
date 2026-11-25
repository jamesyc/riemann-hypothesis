module

public import Riemann.ExcessAverage
public import Utilities.ModularWeights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Utilities
open scoped BigOperators Classical

namespace Riemann

namespace ExcessAverageData

variable {H : Type*} [AddCommGroup H] [Fintype H]

def IsTop (d : ExcessAverageData H) (ρ : ExcessNode H) : Prop :=
  ρ.1 = 0 ∧ ρ.2 ∈ d.tops

/-- The three prescribed base-height cases and the modular condition in
Proposition 18.7, with indices `j` starting at zero. -/
structure CanonicalNodeBases (d : ExcessAverageData H) (u : H) {W : ℕ}
    (κ : ExcessNode H → (ZMod W)ˣ) (topBase : H → ℤ) (thickBase thinBase halfGap : ℤ)
    (base : ExcessNode H → ℤ) : Prop where
  top_eq : ∀ t ∈ d.tops, base (0, t) = topBase t
  thick_interval : ∀ ρ, d.IsThick u ρ → thickBase ≤ base ρ ∧ base ρ < thickBase + (W : ℤ)
  thin_eq : ∀ ρ, ¬d.IsTop ρ → ¬d.IsThick u ρ → base ρ = thinBase
  midpoint_sum : ∀ j : ℕ, modularNodeSum κ (fun ρ => base ρ + (2 * (j : ℤ) + 1) * halfGap) = 0

theorem exists_canonicalNodeBases (d : ExcessAverageData H) (u : H) {W : ℕ} [NeZero W]
    (κ : ExcessNode H → (ZMod W)ˣ) (hκ : (∑ ρ : ExcessNode H, (κ ρ : ZMod W)) = 0)
    (topBase : H → ℤ) (thickBase thinBase halfGap : ℤ) (hthick : d.thickPositions.Nonempty) :
    ∃ base : ExcessNode H → ℤ, d.CanonicalNodeBases u κ topBase thickBase thinBase halfGap base := by
  classical
  obtain ⟨v, hv⟩ := hthick
  let chosen : ExcessNode H := (1, v + u)
  have hchosen : d.IsThick u chosen := by simp [IsThick, chosen, hv]
  have hdisjoint (ρ : ExcessNode H) (hρ : d.IsThick u ρ) : ¬d.IsTop ρ := by
    intro htop
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1) (htop.1.symm.trans hρ.1)
  let raw (ρ : ExcessNode H) := if d.IsTop ρ then topBase ρ.2
    else if d.IsThick u ρ then thickBase else thinBase
  obtain ⟨base, hunchanged, hlo, hhi, hsum⟩ := exists_modular_node_base κ hκ raw halfGap chosen
  have hraw (ρ : ExcessNode H) (hρ : d.IsThick u ρ) : raw ρ = thickBase := by
    simp [raw, hdisjoint ρ hρ, hρ]
  refine ⟨base, ⟨?_, ?_, ?_, hsum⟩⟩
  · intro t ht
    have htop : d.IsTop (0, t) := ⟨rfl, ht⟩
    have hne : ((0, t) : ExcessNode H) ≠ chosen := by
      intro heq
      exact hdisjoint chosen hchosen (heq ▸ htop)
    rw [hunchanged _ hne]
    simp [raw, htop]
  · intro ρ hρ
    by_cases heq : ρ = chosen
    · subst ρ
      simpa only [hraw _ hchosen] using And.intro hlo hhi
    · rw [hunchanged _ heq, hraw _ hρ]
      have hW : (0 : ℤ) < (W : ℤ) := by exact_mod_cast (NeZero.pos W)
      exact ⟨le_rfl, by linarith⟩
  · intro ρ htop hρ
    have hne : ρ ≠ chosen := by
      intro heq
      exact hρ (heq.symm ▸ hchosen)
    rw [hunchanged _ hne]
    simp [raw, htop, hρ]

/-- The three base-height cases give the midpoint bounds in Corollary 18.8
once the common offset is small compared with the thin scale. -/
theorem CanonicalNodeBases.midpoint_bounds (d : ExcessAverageData H) {u : H} {W : ℕ}
    {κ : ExcessNode H → (ZMod W)ˣ} {bt : H → ℤ} {base : ExcessNode H → ℤ}
    {x : ℝ} {gap : ℤ}
    (hbase : d.CanonicalNodeBases u κ (fun t => bt t + Int.floor (d.thinScale / x))
      (Int.ceil d.b) (Int.ceil (d.thinScale / (x * Fintype.card H))) gap base)
    (hx : 3 ≤ x) (hcard : 0 < Fintype.card H) (hgap : 0 ≤ gap) (hthin : 4 ≤ d.thinScale)
    (hshift : (d.steps : ℝ) * (2 * gap) ≤ d.thinScale / 4)
    (hbt : ∀ t ∈ d.tops, d.thinScale ≤ (bt t : ℝ) ∧ (bt t : ℝ) ≤ (5 / 4 : ℝ) * d.thinScale)
    (j : Fin d.steps) (ρ : ExcessNode H) :
    let w := base ρ + (2 * (j.val : ℤ) + 1) * gap
    (d.IsThick u ρ → d.b ≤ (w : ℝ) ∧
      (w : ℝ) ≤ d.b + W + (d.steps : ℝ) * (2 * gap)) ∧
    (¬d.IsThick u ρ → 1 ≤ w ∧ (w : ℝ) ≤ 2 * d.thinScale) := by
  let s : ℤ := (2 * (j.val : ℤ) + 1) * gap
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hj : 2 * (j.val : ℤ) + 1 ≤ (d.steps : ℤ) * 2 := by omega
  have hs' : (s : ℝ) ≤ (d.steps : ℝ) * (2 * gap) := by
    have he := mul_le_mul_of_nonneg_right hj hgap
    rw [mul_assoc] at he
    exact_mod_cast he
  have hs₀ : 0 ≤ (s : ℝ) := by exact_mod_cast hs
  have hx' : 0 < x := by linarith
  have hn : (1 : ℝ) ≤ Fintype.card H := by exact_mod_cast hcard
  have hden : 3 ≤ x * Fintype.card H := by nlinarith [mul_le_mul_of_nonneg_left hn hx'.le]
  have hthin' : 0 < d.thinScale := by linarith
  have hdiv : d.thinScale / x ≤ d.thinScale / 3 :=
    div_le_div_of_nonneg_left hthin'.le (by norm_num) hx
  have hdiv' : d.thinScale / (x * Fintype.card H) ≤ d.thinScale / 3 :=
    div_le_div_of_nonneg_left hthin'.le (by norm_num) hden
  change (d.IsThick u ρ → d.b ≤ ((base ρ + s : ℤ) : ℝ) ∧
    ((base ρ + s : ℤ) : ℝ) ≤ d.b + W + (d.steps : ℝ) * (2 * gap)) ∧
    (¬d.IsThick u ρ → 1 ≤ base ρ + s ∧ ((base ρ + s : ℤ) : ℝ) ≤ 2 * d.thinScale)
  constructor
  · intro hρ
    obtain ⟨hl, hr⟩ := hbase.thick_interval ρ hρ
    have hl' : ((Int.ceil d.b : ℤ) : ℝ) ≤ base ρ := by exact_mod_cast hl
    have hr' : ((base ρ : ℤ) : ℝ) ≤ (Int.ceil d.b : ℝ) + W - 1 := by
      exact_mod_cast (show base ρ ≤ Int.ceil d.b + W - 1 by omega)
    push_cast
    constructor <;> linarith [Int.le_ceil d.b, Int.ceil_lt_add_one d.b]
  · intro hρ
    by_cases ht : d.IsTop ρ
    · obtain ⟨hfst, ht⟩ := ht
      have heq : ρ = (0, ρ.2) := Prod.ext hfst rfl
      have hb := hbase.top_eq ρ.2 ht
      rw [← heq] at hb
      have hbt₀ : 0 < bt ρ.2 := by exact_mod_cast (hthin'.trans_le (hbt _ ht).1)
      have hfloor : 0 ≤ Int.floor (d.thinScale / x) :=
        Int.floor_nonneg.mpr (by positivity)
      constructor
      · omega
      · rw [hb]
        push_cast
        linarith [(hbt _ ht).2, Int.floor_le (d.thinScale / x), hs'.trans hshift]
    · have hb := hbase.thin_eq ρ ht hρ
      have hceil : 0 < Int.ceil (d.thinScale / (x * Fintype.card H)) :=
        Int.ceil_pos.mpr (by positivity)
      constructor
      · omega
      · rw [hb]
        push_cast
        linarith [Int.ceil_lt_add_one (d.thinScale / (x * Fintype.card H)), hs'.trans hshift]

end ExcessAverageData

end Riemann
