module

public import Utilities.FiniteFourier
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Riemann.SmoothedSums
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open Utilities
open scoped BigOperators Classical

namespace Riemann

abbrev ExcessNode (H : Type*) := ZMod 2 × H
abbrev ExcessGroup (H : Type*) := ZMod 2 × ExcessNode H
abbrev ExcessCharacter (H : Type*) [AddCommGroup H] := AddChar (ExcessGroup H) ℂ

/-- Translation from the complement of Φ to Φ, using the last two coordinates. -/
def translateExcessNode {H : Type*} [AddCommGroup H] (t : H)
    (g : ExcessNode H) : ExcessNode H :=
  (g.1 + 1, g.2 + t)

/-- The sum (3.9), indexing the complement of Φ by its last two coordinates. -/
noncomputable def excessSum {H : Type*} [AddCommGroup H] [Fintype H]
    (G : ExcessCharacter H → ℝ → ℂ) (a : ℝ) (t : H) (w : ExcessNode H → ℝ) : ℂ :=
  (Fintype.card (ExcessNode H) : ℂ)⁻¹ * ∑ g : ExcessNode H,
    let node := w (translateExcessNode t g)
    ∑ ψ : ExcessCharacter H, star (ψ (1, g)) * (node : ℂ) * G ψ (a / node)

theorem excessSum_add {H : Type*} [AddCommGroup H] [Fintype H]
    (F G : ExcessCharacter H → ℝ → ℂ) (a : ℝ) (t : H) (w : ExcessNode H → ℝ) :
    excessSum (fun ψ x => F ψ x + G ψ x) a t w = excessSum F a t w + excessSum G a t w := by
  simp only [excessSum, mul_add, Finset.sum_add_distrib]

noncomputable def averageLogNode {H : Type*} [Fintype H] (w : ExcessNode H → ℝ) : ℝ :=
  (∑ ρ : ExcessNode H, Real.log (w ρ)) / Fintype.card (ExcessNode H)

noncomputable def excessMainTerm {H : Type*} [Fintype H] (a ell : ℝ)
    (w : ExcessNode H → ℝ) : ℝ :=
  a * (Real.log a - 1 - Real.eulerMascheroniConstant + ell - averageLogNode w)

/-- Frobenius and inertia data for Proposition 3.3. -/
structure PrimeExcessData (H : Type*) [AddCommGroup H] where
  exceptional : ℕ
  excluded : Finset ℕ
  frobenius : ℕ → ExcessGroup H
  inertia : ℕ → AddSubgroup (ExcessGroup H)
  quadratic : ExcessCharacter H
  logDerivativeAtOne : ExcessCharacter H → ℂ

namespace PrimeExcessData

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def coefficient (d : PrimeExcessData H) (ψ : ExcessCharacter H) (n : ℕ) : ℂ := by
  classical
  exact if IsPrimePow n then
    let p := n.minFac
    characterCosetAverage (d.inertia p) (n.factorization p • d.frobenius p) ψ
  else 0

theorem coefficient_orthogonality (d : PrimeExcessData H) {n : ℕ}
    (hn : IsPrimePow n) (x : ExcessGroup H) :
    let p := n.minFac
    (∑ ψ : ExcessCharacter H, star (ψ x) * d.coefficient ψ n) =
      if x - n.factorization p • d.frobenius p ∈ d.inertia p then
        (Fintype.card (ExcessGroup H) : ℂ) / (subgroupElements (d.inertia p)).card else 0 := by
  simpa only [coefficient, ite_eq_left hn] using
    characterCosetAverage_orthogonality (d.inertia n.minFac)
      (n.factorization n.minFac • d.frobenius n.minFac) x

noncomputable def smoothed (d : PrimeExcessData H) (ψ : ExcessCharacter H) (x : ℝ) : ℂ := by
  classical
  exact if ψ = 0 then (smoothedZetaSum x : ℂ)
    else smoothedTwist (d.coefficient ψ) (d.logDerivativeAtOne ψ) x

@[simp] theorem smoothed_zero (d : PrimeExcessData H) (x : ℝ) :
    d.smoothed 0 x = (smoothedZetaSum x : ℂ) := by
  simp [smoothed]

theorem coefficient_zero_of_primePow (d : PrimeExcessData H) {n : ℕ} (hn : IsPrimePow n) :
    d.coefficient 0 n = 1 := by
  simp only [coefficient, ite_eq_left hn, characterCosetAverage_zero]

noncomputable def smoothingCorrection (d : PrimeExcessData H) (ψ : ExcessCharacter H) (x : ℝ) : ℂ :=
  if ψ = 0 then (zetaCorrection x : ℂ) else d.logDerivativeAtOne ψ * (x : ℂ)

theorem smoothed_eq_raw_add_correction (d : PrimeExcessData H) (ψ : ExcessCharacter H) (x : ℝ) :
    d.smoothed ψ x = smoothedMangoldt (d.coefficient ψ) x + d.smoothingCorrection ψ x := by
  by_cases hψ : ψ = 0
  · subst ψ
    simp only [smoothed_zero, smoothingCorrection, smoothedZetaSum,
      Complex.ofReal_add, smoothedMangoldt_one_real]
    congr 1
    apply smoothedMangoldt_congr_on_primePowers
    intro n hn
    exact (d.coefficient_zero_of_primePow hn).symm
  · simp only [smoothed, smoothingCorrection, ite_eq_right hψ, smoothedTwist]

/-- The multiplier on the prime power at the outside node `(1, g)`. -/
noncomputable def primePowerWeight (d : PrimeExcessData H) (g : ExcessNode H) (n : ℕ) : ℕ :=
  let p := n.minFac
  let frob := n.factorization p • d.frobenius p
  if p = d.exceptional then
    if frob.2 = g then 1 else 0
  else if p ∉ d.excluded ∧ frob = (1, g) then 2 else 0

/-- The prime side of (3.10), truncated at each node's cutoff. The exceptional
coset has one element outside Φ. Its final two coordinates are those of Frobenius. -/
noncomputable def primeSide (d : PrimeExcessData H) (a : ℝ) (t : H)
    (w : ExcessNode H → ℝ) : ℝ := by
  classical
  exact ∑ g : ExcessNode H,
    let node := w (translateExcessNode t g)
    ∑ n ∈ Finset.Icc 1 (Nat.floor (a / node)),
      if IsPrimePow n then
        (d.primePowerWeight g n : ℝ) * (Real.log (n.minFac : ℝ) * (a / (n : ℝ) - node))
      else 0

end PrimeExcessData

structure PrimeExcessHypotheses {H : Type*} [AddCommGroup H]
    (d : PrimeExcessData H) : Prop where
  exceptional_prime : d.exceptional.Prime
  exceptional_not_excluded : d.exceptional ∉ d.excluded
  unramified : ∀ p : ℕ, p.Prime → p ∉ d.excluded → p ≠ d.exceptional →
    d.inertia p = ⊥
  excluded_inertia : ∀ p ∈ d.excluded, p.Prime →
    ∀ g ∈ d.inertia p, g.1 = 0
  excluded_frobenius : ∀ p ∈ d.excluded, p.Prime → (d.frobenius p).1 = 0
  exceptional_inertia : ∀ g, g ∈ d.inertia d.exceptional ↔ g = 0 ∨ g = (1, 0, 0)
  quadratic_value : ∀ g, d.quadratic g = if g.1 = 0 then 1 else -1

private theorem outside_mem_exceptional_coset_iff {H : Type*} [AddCommGroup H]
    {d : PrimeExcessData H} (hd : PrimeExcessHypotheses d) (g : ExcessNode H) (frob : ExcessGroup H) :
    ((1, g) : ExcessGroup H) - frob ∈ d.inertia d.exceptional ↔ frob.2 = g := by
  rw [hd.exceptional_inertia]
  constructor
  · rintro (h | h)
    · have hlast : g - frob.2 = 0 := congrArg Prod.snd h
      exact (sub_eq_zero.mp hlast).symm
    · have hlast : g - frob.2 = 0 := congrArg Prod.snd h
      exact (sub_eq_zero.mp hlast).symm
  · intro hg
    have hlast : (((1, g) : ExcessGroup H) - frob).2 = 0 := by
      change g - frob.2 = 0
      rw [hg, sub_self]
    have hbinary (b : ZMod 2) : b = 0 ∨ b = 1 := by
      fin_cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hbinary (((1, g) : ExcessGroup H) - frob).1 with h | h
    · exact Or.inl (Prod.ext h hlast)
    · exact Or.inr (Prod.ext h hlast)

private theorem exceptional_inertia_card {H : Type*} [AddCommGroup H] [Fintype H]
    {d : PrimeExcessData H} (hd : PrimeExcessHypotheses d) :
    (subgroupElements (d.inertia d.exceptional)).card = 2 := by
  let e : ExcessGroup H := (1, 0, 0)
  have he : subgroupElements (d.inertia d.exceptional) = {0, e} := by
    ext g
    simp only [mem_subgroupElements, hd.exceptional_inertia, Finset.mem_insert, Finset.mem_singleton, e]
  have hne : (0 : ExcessGroup H) ≠ e := fun h =>
    (zero_ne_one : (0 : ZMod 2) ≠ 1) (congrArg Prod.fst h)
  rw [he, Finset.card_pair hne]

/-- Fourier inversion at an outside node gives the prime-side multiplier,
including the change from weight two to weight one at the exceptional prime. -/
theorem PrimeExcessData.coefficient_outside_fourier {H : Type*} [AddCommGroup H] [Fintype H]
    (d : PrimeExcessData H) (hd : PrimeExcessHypotheses d) {n : ℕ} (hn : IsPrimePow n) (g : ExcessNode H) :
    (∑ ψ : ExcessCharacter H, star (ψ (1, g)) * d.coefficient ψ n) =
      (Fintype.card (ExcessNode H) : ℂ) * (d.primePowerWeight g n : ℂ) := by
  let p := n.minFac
  let frob := n.factorization p • d.frobenius p
  have hp : p.Prime := Nat.minFac_prime hn.ne_one
  have hcard : (Fintype.card (ExcessGroup H) : ℂ) = 2 * (Fintype.card (ExcessNode H) : ℂ) := by
    change (Fintype.card (ZMod 2 × ExcessNode H) : ℂ) = _
    rw [Fintype.card_prod, ZMod.card, Nat.cast_mul]
    norm_num
  rw [d.coefficient_orthogonality hn]
  change (if ((1, g) : ExcessGroup H) - frob ∈ d.inertia p then
    (Fintype.card (ExcessGroup H) : ℂ) / (subgroupElements (d.inertia p)).card else 0) = _
  have hweight : d.primePowerWeight g n =
      (if p = d.exceptional then (if frob.2 = g then 1 else 0)
      else if p ∉ d.excluded ∧ frob = (1, g) then 2 else 0) := rfl
  rw [hweight]
  by_cases he : p = d.exceptional
  · have hmem : ((1, g) : ExcessGroup H) - frob ∈ d.inertia p ↔ frob.2 = g := by
      rw [he]
      exact outside_mem_exceptional_coset_iff hd g frob
    have hsize : (subgroupElements (d.inertia p)).card = 2 := by rw [he, exceptional_inertia_card hd]
    rw [hmem, hsize, hcard]
    by_cases hg : frob.2 = g <;> simp [he, hg]
  · by_cases hx : p ∈ d.excluded
    · have hfrob : frob.1 = 0 := by
        change (n.factorization p) • (d.frobenius p).1 = 0
        rw [hd.excluded_frobenius p hx hp, nsmul_zero]
      have hnot : ((1, g) : ExcessGroup H) - frob ∉ d.inertia p := by
        intro hi
        have hzero := hd.excluded_inertia p hx hp _ hi
        change (1 : ZMod 2) - frob.1 = 0 at hzero
        rw [hfrob, sub_zero] at hzero
        exact one_ne_zero hzero
      simp [he, hx, hnot]
    · rw [hd.unramified p hp hx he, subgroupElements_bot, Finset.card_singleton, hcard,
        AddSubgroup.mem_bot, sub_eq_zero]
      by_cases hg : frob = (1, g)
      · simp [he, hx, hg, mul_comm]
      · simp [he, hx, hg, Ne.symm hg]

private theorem PrimeExcessData.outside_rawSum_eq {H : Type*} [AddCommGroup H] [Fintype H]
    (d : PrimeExcessData H) (hd : PrimeExcessHypotheses d) (g : ExcessNode H)
    (a : ℝ) {node : ℝ} (hnode : 0 < node) :
    (Fintype.card (ExcessNode H) : ℂ)⁻¹ * (∑ ψ : ExcessCharacter H,
      star (ψ (1, g)) * (node : ℂ) * smoothedMangoldt (d.coefficient ψ) (a / node)) =
    ∑ n ∈ Finset.Icc 1 (Nat.floor (a / node)),
      ((if IsPrimePow n then (d.primePowerWeight g n : ℝ) *
        (Real.log (n.minFac : ℝ) * (a / (n : ℝ) - node)) else 0 : ℝ) : ℂ) := by
  let f := (Fintype.card (ExcessNode H) : ℂ)
  have hf : f ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcancel (z : ℂ) : f⁻¹ * (f * z) = z := by rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]
  let indices := Finset.Icc 1 (Nat.floor (a / node))
  let kernel (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n * ((a / node) / (n : ℝ) - 1) : ℝ) : ℂ)
  change f⁻¹ * (∑ ψ : ExcessCharacter H,
    star (ψ (1, g)) * (node : ℂ) * smoothedMangoldt (d.coefficient ψ) (a / node)) = _
  calc
    _ = f⁻¹ * (∑ ψ : ExcessCharacter H, ∑ n ∈ indices,
          star (ψ (1, g)) * (node : ℂ) * (kernel n * d.coefficient ψ n)) := by
      simp only [smoothedMangoldt, indices, kernel, Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn₀ : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
      have hscale : (node : ℂ) * kernel n =
          ((ArithmeticFunction.vonMangoldt n * (a / (n : ℝ) - node) : ℝ) : ℂ) := by
        dsimp only [kernel]
        rw [← Complex.ofReal_mul]
        congr 1
        have hnRe : (n : ℝ) ≠ 0 := by exact_mod_cast hn₀
        field_simp [hnode.ne', hnRe]
      calc
        _ = f⁻¹ * (∑ ψ : ExcessCharacter H,
              ((node : ℂ) * kernel n) * (star (ψ (1, g)) * d.coefficient ψ n)) := by
          congr 1
          exact Finset.sum_congr rfl fun ψ _ => by ring
        _ = ((node : ℂ) * kernel n) *
            (f⁻¹ * ∑ ψ : ExcessCharacter H, star (ψ (1, g)) * d.coefficient ψ n) := by
          rw [← Finset.mul_sum]
          ring
        _ = _ := by
          rw [hscale, ArithmeticFunction.vonMangoldt_apply]
          by_cases hnPow : IsPrimePow n
          · rw [d.coefficient_outside_fourier hd hnPow g]
            change (((if IsPrimePow n then Real.log (n.minFac : ℝ) else 0) * (a / (n : ℝ) - node) : ℝ) : ℂ) *
              (f⁻¹ * (f * (d.primePowerWeight g n : ℂ))) = _
            rw [hcancel]
            simp only [ite_eq_left hnPow, Complex.ofReal_mul, Complex.ofReal_natCast]
            ring
          · simp [hnPow]

theorem primeSide_eq_rawExcessSum {H : Type*} [AddCommGroup H] [Fintype H]
    {d : PrimeExcessData H} (hd : PrimeExcessHypotheses d)
    (a : ℝ) (t : H) {w : ExcessNode H → ℝ} (hw : ∀ ρ, 0 < w ρ) :
    (d.primeSide a t w : ℂ) = excessSum (fun ψ => smoothedMangoldt (d.coefficient ψ)) a t w := by
  unfold PrimeExcessData.primeSide excessSum
  rw [Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Complex.ofReal_sum]
  exact (d.outside_rawSum_eq hd g a (hw (translateExcessNode t g))).symm

private theorem rawTrivialCorrection_eq {H : Type*} [AddCommGroup H] [Fintype H]
    {a : ℝ} (ha : 0 < a) (t : H) {w : ExcessNode H → ℝ} (hw : ∀ ρ, 0 < w ρ) :
    (excessSum (fun ψ x => if ψ = 0 then (zetaCorrection x : ℂ) else 0) a t w).re =
      -excessMainTerm a 0 w := by
  let node (g : ExcessNode H) := w (translateExcessNode t g)
  have htrivial : excessSum (fun ψ x => if ψ = 0 then (zetaCorrection x : ℂ) else 0) a t w =
      (Fintype.card (ExcessNode H) : ℂ)⁻¹ * ∑ g, (node g : ℂ) * (zetaCorrection (a / node g) : ℂ) := by
    unfold excessSum
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      AddChar.zero_apply, star_one, one_mul, node]
  have hweighted (g : ExcessNode H) : node g * zetaCorrection (a / node g) =
      a * (-Real.log a + (1 + Real.eulerMascheroniConstant)) + a * Real.log (node g) := by
    have hg : 0 < node g := hw _
    rw [zetaCorrection, Real.log_div ha.ne' hg.ne']
    field_simp [hg.ne']
    ring
  have hlog : (∑ g, Real.log (node g)) = ∑ g : ExcessNode H, Real.log (w g) :=
    Equiv.sum_comp ((Equiv.addRight (1 : ZMod 2)).prodCongr (Equiv.addRight t)) (fun g => Real.log (w g))
  have hsum : (∑ g, node g * zetaCorrection (a / node g)) =
      (Fintype.card (ExcessNode H) : ℝ) * (a * (-Real.log a + (1 + Real.eulerMascheroniConstant))) +
        a * (∑ g : ExcessNode H, Real.log (w g)) := by
    simp only [hweighted, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      ← Finset.mul_sum, hlog]
  have hcard : (Fintype.card (ExcessNode H) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [htrivial]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re, hsum, excessMainTerm, averageLogNode, add_zero]
  field_simp [hcard]
  ring

private theorem rawLogCorrection_eq {H : Type*} [AddCommGroup H] [Fintype H]
    {d : PrimeExcessData H} (hd : PrimeExcessHypotheses d)
    (a : ℝ) (t : H) {w : ExcessNode H → ℝ} (hw : ∀ ρ, 0 < w ρ) :
    excessSum (fun ψ x => if ψ = 0 then 0 else d.logDerivativeAtOne ψ * (x : ℂ)) a t w =
      -((a : ℂ) * d.logDerivativeAtOne d.quadratic) := by
  let count := (Fintype.card (ExcessNode H) : ℂ)
  let node (g : ExcessNode H) := w (translateExcessNode t g)
  let scale (ψ : ExcessCharacter H) := (a : ℂ) * d.logDerivativeAtOne ψ
  have hcount : count ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hquad : d.quadratic ≠ 0 := by
    intro heq
    have hvalue := hd.quadratic_value ((1, 0) : ExcessGroup H)
    norm_num [heq] at hvalue
  have hpoint (g : ExcessNode H) (ψ : ExcessCharacter H) :
      star (ψ (1, g)) * (node g : ℂ) *
        (if ψ = 0 then 0 else d.logDerivativeAtOne ψ * ((a / node g : ℝ) : ℂ)) =
          if ψ = 0 then 0 else scale ψ * star (ψ (1, g)) := by
    by_cases hψ : ψ = 0
    · simp [hψ]
    · simp only [ite_eq_right hψ, Complex.ofReal_div, scale]
      have hg : (node g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw _).ne'
      field_simp [hg]
  have hinside (ψ : ExcessCharacter H) :
      (∑ g : ExcessNode H, if ψ = 0 then 0 else scale ψ * star (ψ (1, g))) =
        if ψ = 0 then 0 else scale ψ * ∑ g : ExcessNode H, star (ψ (1, g)) := by
    by_cases hψ : ψ = 0 <;> simp [hψ, Finset.mul_sum]
  have hsum :
      (∑ ψ : ExcessCharacter H, if ψ = 0 then 0 else scale ψ *
        ((if ψ = 0 then count else 0) - (if ψ = d.quadratic then count else 0))) =
      -(scale d.quadratic * count) := by
    rw [Finset.sum_eq_single d.quadratic]
    · simp [hquad]
    · intro ψ _ hne
      by_cases hψ : ψ = 0 <;> simp [hψ, hne]
    · simp
  calc
    _ = count⁻¹ * ∑ g : ExcessNode H, ∑ ψ : ExcessCharacter H,
        if ψ = 0 then 0 else scale ψ * star (ψ (1, g)) := by
      unfold excessSum
      congr 1
      exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun ψ _ => hpoint g ψ
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [hinside, sum_star_character_on_zmodTwo_one d.quadratic _ hd.quadratic_value]
      rw [hsum]
      field_simp [hcount]
      ring

/-- Proposition 3.3 in the real form used by Corollary 3.4. -/
theorem primeSide_eq_main_add_excess {H : Type*} [AddCommGroup H] [Fintype H]
    {d : PrimeExcessData H} (hd : PrimeExcessHypotheses d)
    {a : ℝ} (ha : 0 < a) (t : H) {w : ExcessNode H → ℝ} (hw : ∀ ρ, 0 < w ρ) :
    d.primeSide a t w = excessMainTerm a (d.logDerivativeAtOne d.quadratic).re w +
      (excessSum d.smoothed a t w).re := by
  let base (ψ : ExcessCharacter H) (x : ℝ) := if ψ = 0 then (zetaCorrection x : ℂ) else 0
  let logs (ψ : ExcessCharacter H) (x : ℝ) := if ψ = 0 then 0 else d.logDerivativeAtOne ψ * (x : ℂ)
  have hc : d.smoothed = fun ψ x => (smoothedMangoldt (d.coefficient ψ) x + base ψ x) + logs ψ x := by
    funext ψ x
    rw [d.smoothed_eq_raw_add_correction]
    by_cases hψ : ψ = 0 <;> simp [PrimeExcessData.smoothingCorrection, base, logs, hψ]
  rw [hc, excessSum_add, excessSum_add, ← primeSide_eq_rawExcessSum hd a t hw,
    Complex.add_re, Complex.add_re, Complex.ofReal_re,
    rawTrivialCorrection_eq ha t hw, rawLogCorrection_eq hd a t hw]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, excessMainTerm, add_zero]
  ring

end Riemann
