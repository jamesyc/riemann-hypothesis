module

public import Riemann.AuxiliaryPrimePool
public import Riemann.HostAveraging
public import Riemann.AuxiliaryMangoldtMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter Utilities
open scoped Classical

namespace Riemann

/-- The cutoff of §5.5 and §5.6, rounded up and large enough to include
the last dyadic block. -/
noncomputable def auxiliarySmoothedCutoff (X : ℝ) : ℕ :=
  max ⌈2 * X⌉₊ ⌈X ^ (400 : ℕ)⌉₊

theorem two_mul_le_auxiliarySmoothedCutoff (X : ℝ) : 2 * X ≤ auxiliarySmoothedCutoff X :=
  (Nat.le_ceil (2 * X)).trans (by exact_mod_cast le_max_left _ _)

/-- The first-prime twist, extended to a total family for finset expressions.
The fallback is outside the search pool. -/
noncomputable def firstAuxiliaryTestCharacter (target : BundledDirichletCharacter)
    (q : ℕ) (i : Fin (orderOf target.character)) : BundledDirichletCharacter :=
  if h : q.Prime ∧ q % 4 = 3 then
    let q' : ℕ+ := ⟨q, h.1.pos⟩
    letI : Fact (q' : ℕ).Prime := ⟨h.1⟩
    selmerFirstTwistedCharacter target q' h.2 i true
  else target

/-- The twists involving the second prime, extended outside the search pool
as in the first-prime family. -/
noncomputable def secondAuxiliaryTestCharacter (target : BundledDirichletCharacter)
    (q d : ℕ) (i : Fin (orderOf target.character) × Bool) : BundledDirichletCharacter :=
  if h : q.Prime ∧ d.Prime ∧ q % 4 = 3 ∧ d % 4 = 3 then
    let q' : ℕ+ := ⟨q, h.1.pos⟩
    let d' : ℕ+ := ⟨d, h.2.1.pos⟩
    letI : Fact (q' : ℕ).Prime := ⟨h.1⟩
    letI : Fact (d' : ℕ).Prime := ⟨h.2.1⟩
    selmerTwistedCharacter target q' d' h.2.2.1 h.2.2.2 i.1 i.2 true
  else target

set_option backward.isDefEq.respectTransparency false in
theorem firstAuxiliaryTestCharacter_coe (target : BundledDirichletCharacter) (q : ℕ+)
    [Fact (q : ℕ).Prime] (hq₄ : (q : ℕ) % 4 = 3) (i : Fin (orderOf target.character)) :
    firstAuxiliaryTestCharacter target q i = selmerFirstTwistedCharacter target q hq₄ i true := by
  have hgood : (q : ℕ).Prime ∧ (q : ℕ) % 4 = 3 := ⟨Fact.out, hq₄⟩
  rw [firstAuxiliaryTestCharacter, dite_eq_left hgood]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem secondAuxiliaryTestCharacter_coe (target : BundledDirichletCharacter) (q d : ℕ+)
    [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime] (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3)
    (i : Fin (orderOf target.character) × Bool) :
    secondAuxiliaryTestCharacter target q d i =
      selmerTwistedCharacter target q d hq₄ hd₄ i.1 i.2 true := by
  have hgood : (q : ℕ).Prime ∧ (d : ℕ).Prime ∧ (q : ℕ) % 4 = 3 ∧ (d : ℕ) % 4 = 3 :=
    ⟨Fact.out, Fact.out, hq₄, hd₄⟩
  rw [secondAuxiliaryTestCharacter, dite_eq_left hgood]
  rfl

/-- The needed smoothed-sum conclusion of Theorem 5.10. -/
def FirstAuxiliarySmoothedGood (target : BundledDirichletCharacter) (ε J base : ℝ)
    (q : ℕ) : Prop :=
  ∀ x ∈ Set.Icc base (base ^ J), ∀ i : Fin (orderOf target.character),
    ‖complexSmoothedCharacterSum (firstAuxiliaryTestCharacter target q i) x‖ ≤
      x ^ (1 / 2 + ε)

/-- The needed smoothed-sum conclusion of Theorem 5.12. -/
def SecondAuxiliarySmoothedGood (target : BundledDirichletCharacter) (ε J base : ℝ)
    (q d : ℕ) : Prop :=
  ∀ x ∈ Set.Icc base (base ^ J), ∀ i : Fin (orderOf target.character) × Bool,
    ‖complexSmoothedCharacterSum (secondAuxiliaryTestCharacter target q d i) x‖ ≤
      x ^ (1 / 2 + ε)

/-- The real-axis consequence of the zero-free box for the fixed
testing level in Corollary 5.13. -/
def FirstAuxiliaryRealGood (target : BundledDirichletCharacter) (q : ℕ) : Prop :=
  ∀ (hq : q.Prime) (hq₄ : q % 4 = 3),
    let q' : ℕ+ := ⟨q, hq.pos⟩
    letI : Fact (q' : ℕ).Prime := ⟨hq⟩
    ∀ ξ : BundledDirichletCharacter, ξ.character.IsPrimitive →
      (ξ.modulus : ℕ) ∣ 8 * (target.modulus : ℕ) →
      ∀ β ∈ Set.Ioo (1 - (1 / 400 : ℝ)) 1,
        DirichletCharacter.LFunction
          (selmerFirstTwistedCharacter ξ q' hq₄ 1 true).character (β : ℂ) ≠ 0

/-- The corresponding real-axis test for twists involving the second prime. -/
def SecondAuxiliaryRealGood (target : BundledDirichletCharacter) (q d : ℕ) : Prop :=
  ∀ (hq : q.Prime) (hd : d.Prime) (hq₄ : q % 4 = 3) (hd₄ : d % 4 = 3),
    let q' : ℕ+ := ⟨q, hq.pos⟩
    let d' : ℕ+ := ⟨d, hd.pos⟩
    letI : Fact (q' : ℕ).Prime := ⟨hq⟩
    letI : Fact (d' : ℕ).Prime := ⟨hd⟩
    ∀ ξ : BundledDirichletCharacter, ξ.character.IsPrimitive →
      (ξ.modulus : ℕ) ∣ 8 * (target.modulus : ℕ) →
      ∀ (qSign : Bool) (β : ℝ), β ∈ Set.Ioo (1 - (1 / 400 : ℝ)) 1 →
        DirichletCharacter.LFunction
          (selmerTwistedCharacter ξ q' d' hq₄ hd₄ 1 qSign true).character (β : ℂ) ≠ 0

/-- Nonemptiness of the second progression, uniformly in the choice of
first prime. This is the prime-counting conclusion of Proposition 5.11. -/
theorem eventually_secondAuxiliaryPrimePool_nonempty {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ base : ℝ in atTop,
      let z := base ^ (ε / 5)
      ∀ q ∈ firstAuxiliaryPrimePool z,
        (secondAuxiliaryPrimePool z (z * Real.log base ^ (2 : ℕ)) q).Nonempty := by
  sorry

/-- The first-pool correlations of Proposition 5.7 and the coefficient
factorization for a first-prime twist. -/
theorem eventually_firstAuxiliaryLegendreInput
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε J : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) (hJ : 2 ≤ J) :
    ∀ᶠ base : ℝ in atTop,
      let X := base ^ J
      Nonempty (AuxiliaryLegendreMomentInput (firstAuxiliaryPrimePool (base ^ (ε / 5)))
        (firstAuxiliaryTestCharacter target) (auxiliarySmoothedCutoff X) X 2) := by
  sorry

/-- The second-pool correlations of Proposition 5.11 and the coefficient
factorization with the first-prime twist held fixed. -/
theorem eventually_secondAuxiliaryLegendreInput
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε J : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) (hJ : 2 ≤ J) :
    ∀ᶠ base : ℝ in atTop,
      let X := base ^ J
      let z := base ^ (ε / 5)
      ∀ q ∈ firstAuxiliaryPrimePool z,
        Nonempty (AuxiliaryLegendreMomentInput
          (secondAuxiliaryPrimePool z (z * Real.log base ^ (2 : ℕ)) q)
          (secondAuxiliaryTestCharacter target q) (auxiliarySmoothedCutoff X) X z) := by
  sorry

/-- The two pointwise moments for the first-prime family, uniform in the scale. -/
theorem eventually_firstAuxiliarySmoothed_moments
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε J : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) (hJ : 2 ≤ J) :
    ∃ C ≥ (0 : ℝ), ∀ᶠ base : ℝ in atTop,
      let X := base ^ J
      AuxiliarySmoothedMomentBounds (firstAuxiliaryPrimePool (base ^ (ε / 5)))
        (firstAuxiliaryTestCharacter target) (auxiliarySmoothedCutoff X) base X C := by
  obtain ⟨D, hD, hmass⟩ := exists_auxiliaryExceptionalMangoldtMass
  refine ⟨D + 2 * (Real.log 4 + 4) ^ (2 : ℕ), by positivity, ?_⟩
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [eventually_firstAuxiliaryLegendreInput target hprim hε hsmall hJ,
    eventually_ge_atTop B, eventually_ge_atTop (3 : ℝ)] with base ⟨h⟩ hb hbase
  have hX : 0 ≤ base ^ J := Real.rpow_nonneg (by linarith) _
  have hcut := two_mul_le_auxiliarySmoothedCutoff (base ^ J)
  apply auxiliarySmoothedMoments_of_legendreInput h hbase hX hcut
  intro y hy
  have hy₁ : 1 ≤ y := by linarith [hbase.trans hy.1]
  have hy₀ : 0 < y := by linarith
  have hby := hB y (hb.trans hy.1)
  rw [Real.norm_of_nonneg (Real.log_nonneg hy₁), Real.norm_of_nonneg (Real.rpow_nonneg hy₀.le _)] at hby
  apply hmass _ _ _ _ (hbase.trans hy.1) (hy.2.trans hcut) le_rfl ?_ h.exception_pos h.exception_support
  rw [Real.sqrt_eq_rpow]
  linarith

/-- The same moment calculation for the second pool, with a constant
independent of the first prime. -/
theorem eventually_secondAuxiliarySmoothed_moments
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε J : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) (hJ : 2 ≤ J) :
    ∃ C ≥ (0 : ℝ), ∀ᶠ base : ℝ in atTop,
      let X := base ^ J
      let z := base ^ (ε / 5)
      ∀ q ∈ firstAuxiliaryPrimePool z,
        AuxiliarySmoothedMomentBounds (secondAuxiliaryPrimePool z (z * Real.log base ^ (2 : ℕ)) q)
          (secondAuxiliaryTestCharacter target q) (auxiliarySmoothedCutoff X) base X C := by
  obtain ⟨D, hD, hmass⟩ := exists_auxiliaryExceptionalMangoldtMass
  refine ⟨D + 2 * (Real.log 4 + 4) ^ (2 : ℕ), by positivity, ?_⟩
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((isLittleO_log_rpow_atTop (show 0 < (1 / 2 : ℝ) - ε / 5 by linarith)).bound zero_lt_one)
  filter_upwards [eventually_secondAuxiliaryLegendreInput target hprim hε hsmall hJ,
    eventually_ge_atTop B, eventually_ge_atTop (3 : ℝ),
    (tendsto_rpow_atTop (show 0 < ε / 5 by positivity)).eventually_ge_atTop (2 : ℝ)]
    with base hinput hb hbase hz
  intro X z q hq
  obtain ⟨h⟩ := hinput q hq
  have hbase₀ : 0 ≤ base := by linarith
  have hX : 0 ≤ X := Real.rpow_nonneg hbase₀ _
  have hcut := two_mul_le_auxiliarySmoothedCutoff X
  apply auxiliarySmoothedMoments_of_legendreInput h hbase hX hcut
  intro y hy
  have hy₁ : 1 ≤ y := by linarith [hbase.trans hy.1]
  have hy₀ : 0 < y := by linarith
  have hlog := Real.log_nonneg hy₁
  have hby := hB y (hb.trans hy.1)
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (Real.rpow_nonneg hy₀.le _), one_mul] at hby
  apply hmass _ _ _ _ (hbase.trans hy.1) (hy.2.trans hcut) hz ?_ h.exception_pos h.exception_support
  calc
    z * Real.log y ≤ y ^ (ε / 5) * Real.log y :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hbase₀ hy.1 (by positivity)) hlog
    _ ≤ y ^ (ε / 5) * y ^ (1 / 2 - ε / 5) :=
      mul_le_mul_of_nonneg_left hby (by positivity)
    _ = Real.sqrt y := by
      rw [← Real.rpow_add hy₀, Real.sqrt_eq_rpow]
      congr 1
      ring

/-- The tail estimate and its exceptional set for the first-prime family. -/
theorem eventually_firstAuxiliarySmoothed_tail
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε J : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) (hJ : 2 ≤ J) :
    ∀ᶠ base : ℝ in atTop,
      let X := base ^ J
      let pool := firstAuxiliaryPrimePool (base ^ (ε / 5))
      ∃ bad : Finset ℕ, (bad.card : ℝ) ≤ (1 / 2 : ℝ) * base ^ (-ε) * pool.card ∧
        ∀ q ∈ pool, q ∉ bad → FirstAuxiliaryRealGood target q ∧
          ∀ i : Fin (orderOf target.character), ∀ y ∈ Set.Icc base X,
          let χ := firstAuxiliaryTestCharacter target q i
          ‖complexSmoothedCharacterSum χ y -
            truncatedAuxiliarySmoothedSum (auxiliarySmoothedCoefficients χ) (auxiliarySmoothedCutoff X) y‖ ≤
              (1 / 2 : ℝ) * y ^ (1 / 2 + ε) := by
  sorry

/-- The tail estimate and its exceptional set for the second-prime family,
uniformly over the first prime in its search pool. -/
theorem eventually_secondAuxiliarySmoothed_tail
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε J : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) (hJ : 2 ≤ J) :
    ∀ᶠ base : ℝ in atTop,
      let X := base ^ J
      let z := base ^ (ε / 5)
      ∀ q ∈ firstAuxiliaryPrimePool z,
        let pool := secondAuxiliaryPrimePool z (z * Real.log base ^ (2 : ℕ)) q
        ∃ bad : Finset ℕ, (bad.card : ℝ) ≤ (1 / 2 : ℝ) * base ^ (-ε) * pool.card ∧
          ∀ d ∈ pool, d ∉ bad → SecondAuxiliaryRealGood target q d ∧
            ∀ i : Fin (orderOf target.character) × Bool, ∀ y ∈ Set.Icc base X,
            let χ := secondAuxiliaryTestCharacter target q d i
            ‖complexSmoothedCharacterSum χ y -
              truncatedAuxiliarySmoothedSum (auxiliarySmoothedCoefficients χ) (auxiliarySmoothedCutoff X) y‖ ≤
                (1 / 2 : ℝ) * y ^ (1 / 2 + ε) := by
  sorry

/-- First-prime exceptional count for the smoothed sums in Theorem 5.10. -/
theorem eventually_firstAuxiliarySmoothed_exceptional_count
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε J : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) (hJ : 2 ≤ J) :
    ∀ᶠ base : ℝ in atTop,
      let Q := firstAuxiliaryPrimePool (base ^ (ε / 5))
      ((Q.filter fun q => ¬ (FirstAuxiliarySmoothedGood target ε J base q ∧ FirstAuxiliaryRealGood target q)).card : ℝ) ≤
        base ^ (-ε) * Q.card := by
  obtain ⟨C, hC, hm⟩ := eventually_firstAuxiliarySmoothed_moments target hprim hε hsmall hJ
  filter_upwards [hm, eventually_firstAuxiliarySmoothed_tail target hprim hε hsmall hJ,
    eventually_ge_atTop (1 : ℝ), eventually_auxiliarySmoothedFamily_budget hε hC
      (Fintype.card (Fin (orderOf target.character)))] with base hmoment htail hbase hbudget
  obtain ⟨bad, hcard, hb⟩ := htail
  exact auxiliarySmoothedFamily_exceptional_count _ bad _ (FirstAuxiliaryRealGood target) hbase hε hC
    (two_mul_le_auxiliarySmoothedCutoff _) hmoment hbudget hcard
    (fun p hp hn => (hb p hp hn).2) (fun p hp hn => (hb p hp hn).1)

/-- Second-prime exceptional count for the smoothed sums in Theorem 5.12. -/
theorem eventually_secondAuxiliarySmoothed_exceptional_count
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε J : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) (hJ : 2 ≤ J) :
    ∀ᶠ base : ℝ in atTop,
      let z := base ^ (ε / 5)
      ∀ q ∈ firstAuxiliaryPrimePool z,
        let D := secondAuxiliaryPrimePool z (z * Real.log base ^ (2 : ℕ)) q
        ((D.filter fun d => ¬ (SecondAuxiliarySmoothedGood target ε J base q d ∧ SecondAuxiliaryRealGood target q d)).card : ℝ) ≤
          base ^ (-ε) * D.card := by
  obtain ⟨C, hC, hm⟩ := eventually_secondAuxiliarySmoothed_moments target hprim hε hsmall hJ
  filter_upwards [hm, eventually_secondAuxiliarySmoothed_tail target hprim hε hsmall hJ,
    eventually_ge_atTop (1 : ℝ), eventually_auxiliarySmoothedFamily_budget hε hC
      (Fintype.card (Fin (orderOf target.character) × Bool))] with base hmoment htail hbase hbudget
  intro z q hq D
  obtain ⟨bad, hcard, hb⟩ := htail q hq
  exact auxiliarySmoothedFamily_exceptional_count D bad _ (SecondAuxiliaryRealGood target q) hbase hε hC
    (two_mul_le_auxiliarySmoothedCutoff _) (hmoment q hq) hbudget hcard
    (fun p hp hn => (hb p hp hn).2) (fun p hp hn => (hb p hp hn).1)

/-- Choose the same pair for the first-prime and second-prime smoothed-sum
tests, keeping the modulus in the prescribed small-prime range. -/
theorem eventually_exists_smoothedAuxiliaryPrimePair
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    {ε J : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) (hJ : 2 ≤ J) :
    ∀ᶠ base : ℝ in atTop, ∃ q d : ℕ+,
      SelmerWindowPair ε base q d ∧ ((target.modulus : ℕ) : ℝ) ≤ base ^ (ε / 5) ∧
        FirstAuxiliarySmoothedGood target ε J base q ∧
        SecondAuxiliarySmoothedGood target ε J base q d ∧
          FirstAuxiliaryRealGood target q ∧ SecondAuxiliaryRealGood target q d := by
  filter_upwards [eventually_exists_selmerWindowPair_of_exceptional_counts hε hε,
    eventually_firstAuxiliarySmoothed_exceptional_count target hprim hε hsmall hJ,
    eventually_secondAuxiliarySmoothed_exceptional_count target hprim hε hsmall hJ,
    eventually_secondAuxiliaryPrimePool_nonempty hε hsmall,
    (tendsto_rpow_atTop (show 0 < ε / 5 by positivity)).eventually_ge_atTop
      ((target.modulus : ℕ) : ℝ)] with base hchoose hbadQ hbadD hnonempty hmod
  obtain ⟨q, d, hpair, hq, hd⟩ := hchoose
    (fun q => FirstAuxiliarySmoothedGood target ε J base q ∧ FirstAuxiliaryRealGood target q)
    (fun q d => SecondAuxiliarySmoothedGood target ε J base q d ∧ SecondAuxiliaryRealGood target q d)
    (by convert hbadQ using 2; exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _))
    (fun q hq _ => ⟨hnonempty q hq, by
      convert hbadD q hq using 2; exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)⟩)
  exact ⟨q, d, hpair, hmod, hq.1, hd.1, hq.2, hd.2⟩

end Riemann
