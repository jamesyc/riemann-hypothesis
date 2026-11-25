module

public import Riemann.SelmerWindows
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.WeakPNT

@[expose] public section

open Filter
open scoped BigOperators Classical Topology

namespace Riemann

/-- The search pool for the first auxiliary prime in Theorem 5.10. -/
noncomputable def firstAuxiliaryPrimePool (z : ℝ) : Finset ℕ :=
  (Finset.Ioc (Nat.floor (Real.exp (z / 2))) (Nat.floor (Real.exp z))).filter
    fun p => p.Prime ∧ p % 8 = 3

theorem mem_firstAuxiliaryPrimePool {z : ℝ} {p : ℕ} :
    p ∈ firstAuxiliaryPrimePool z ↔
      p.Prime ∧ p % 8 = 3 ∧ z / 2 < Real.log p ∧ Real.log p ≤ z := by
  rw [firstAuxiliaryPrimePool, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp, hmod⟩
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact ⟨hp, hmod, (Real.lt_log_iff_exp_lt hp₀).mpr ((Nat.floor_lt' hp.ne_zero).mp hlo),
      (Real.log_le_iff_le_exp hp₀).mpr ((Nat.le_floor_iff' hp.ne_zero).mp hhi)⟩
  · rintro ⟨hp, hmod, hlo, hhi⟩
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact ⟨⟨(Nat.floor_lt' hp.ne_zero).mpr ((Real.lt_log_iff_exp_lt hp₀).mp hlo),
      (Nat.le_floor_iff' hp.ne_zero).mpr ((Real.log_le_iff_le_exp hp₀).mp hhi)⟩, hp, hmod⟩

/-- The fixed-modulus prime number theorem gives the quantitative pool
size needed by Theorem 5.10 before removing exceptional primes. -/
theorem eventually_firstAuxiliaryPrimePool_card_lower :
    ∀ᶠ z : ℝ in atTop, Real.exp z / (5 * z) ≤ (firstAuxiliaryPrimePool z).card := by
  let A (z : ℝ) := (Finset.Ioc 0 (Nat.floor (Real.exp z))).filter
    fun p => p.Prime ∧ p % 8 = 3
  let B (z : ℝ) := Finset.Ioc 0 (Nat.floor (Real.exp (z / 2)))
  have hAP := Nat.tendsto_card_prime_modEq_mul_log_div_atTop (q := 8) (a := 3)
    (by decide : Nat.Coprime 3 8)
  have hφ : Nat.totient 8 = 4 := by decide
  rw [hφ] at hAP
  have hlarge : ∀ᶠ z : ℝ in atTop, (9 / 40 : ℝ) ≤ (A z).card * z / Real.exp z := by
    have ht := (hAP.comp Real.tendsto_exp_atTop).eventually_const_le
      (by norm_num : (9 / 40 : ℝ) < ((4 : ℕ) : ℝ)⁻¹)
    filter_upwards [ht] with z hz
    simpa only [Function.comp_apply, Real.log_exp, Nat.ModEq, show (3 : ℕ) % 8 = 3 by decide, A]
      using hz
  have hsmall := (isLittleO_rpow_exp_pos_mul_atTop 1 (b := 1 / 2) (by norm_num)).bound
    (by norm_num : (0 : ℝ) < 1 / 40)
  filter_upwards [hlarge, hsmall, eventually_gt_atTop (0 : ℝ)] with z hAz hgrowth hz
  have hAz' := (le_div_iff₀ (Real.exp_pos z)).mp hAz
  have hsmall' : z ≤ (1 / 40 : ℝ) * Real.exp (z / 2) := by
    convert hgrowth using 2 <;>
      simp [Real.rpow_one, Real.norm_of_nonneg hz.le, Real.norm_of_nonneg (Real.exp_pos _).le,
        div_eq_mul_inv, mul_comm]
  have hB : (B z).card ≤ Real.exp (z / 2) := by
    simpa only [B, Nat.card_Ioc, Nat.sub_zero] using Nat.floor_le (Real.exp_pos (z / 2)).le
  have hs : Real.exp (z / 2) * z ≤ Real.exp z / 40 := by
    have he := mul_le_mul_of_nonneg_left hsmall' (Real.exp_pos (z / 2)).le
    rw [← mul_assoc, mul_comm (Real.exp (z / 2)) (1 / 40 : ℝ), mul_assoc, ← Real.exp_add,
      show z / 2 + z / 2 = z by ring] at he
    linarith
  have hBz := (mul_le_mul_of_nonneg_right hB hz.le).trans hs
  have hpool : A z \ B z = firstAuxiliaryPrimePool z := by
    ext p
    simp only [A, B, firstAuxiliaryPrimePool, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hp₀, hpz⟩, hp, hmod⟩, hnot⟩
      exact ⟨⟨by omega, hpz⟩, hp, hmod⟩
    · rintro ⟨⟨hplo, hphi⟩, hp, hmod⟩
      exact ⟨⟨⟨hp.pos, hphi⟩, hp, hmod⟩, by omega⟩
  have hcard : ((A z).card : ℝ) ≤ (firstAuxiliaryPrimePool z).card + (B z).card := by
    exact_mod_cast (show (A z).card ≤ (firstAuxiliaryPrimePool z).card + (B z).card from
      hpool ▸ Finset.card_le_card_sdiff_add_card)
  have hsum := mul_le_mul_of_nonneg_right hcard hz.le
  rw [add_mul] at hsum
  apply (div_le_iff₀ (by positivity : 0 < 5 * z)).mpr
  linarith

theorem eventually_firstAuxiliaryPrimePool_nonempty {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ base : ℝ in atTop, (firstAuxiliaryPrimePool (base ^ (ε / 5))).Nonempty := by
  have hgrow := tendsto_rpow_atTop (show 0 < ε / 5 by positivity)
  filter_upwards [hgrow.eventually eventually_firstAuxiliaryPrimePool_card_lower,
    hgrow.eventually (eventually_gt_atTop (0 : ℝ))] with base hcard hz
  apply Finset.card_pos.mp
  have hpos : 0 < Real.exp (base ^ (ε / 5)) / (5 * base ^ (ε / 5)) := by positivity
  exact_mod_cast hpos.trans_le hcard

noncomputable def smallOddPrimes (z : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 0 (Nat.floor z)).filter fun p => p.Prime ∧ Odd p

noncomputable def secondAuxiliaryPrimeOddFactor (z : ℝ) (q : ℕ) : ℕ :=
  q * ∏ p ∈ smallOddPrimes z, p

/-- The modulus of the progression for the second auxiliary prime. -/
noncomputable def secondAuxiliaryPrimeModulus (z : ℝ) (q : ℕ) : ℕ := 16 * secondAuxiliaryPrimeOddFactor z q

/-- The progression has a direct representative since its odd factor is odd.
Multiplication by eight gives residue eight modulo sixteen and zero at every odd factor. -/
noncomputable def secondAuxiliaryPrimeResidue (z : ℝ) (q : ℕ) : ℕ := 8 * secondAuxiliaryPrimeOddFactor z q - 1

private theorem secondAuxiliaryPrimeOddFactor_odd (z : ℝ) {q : ℕ} (hq : Odd q) : Odd (secondAuxiliaryPrimeOddFactor z q) := by
  apply hq.mul
  exact Finset.prod_induction id Odd (fun _ _ => Odd.mul) (by decide)
    (fun p hp => ((Finset.mem_filter.mp hp).2).2)

private theorem secondAuxiliaryPrimeResidue_succ (z : ℝ) {q : ℕ} (hq : Odd q) :
    secondAuxiliaryPrimeResidue z q + 1 = 8 * secondAuxiliaryPrimeOddFactor z q := by
  obtain ⟨k, hk⟩ := secondAuxiliaryPrimeOddFactor_odd z hq
  unfold secondAuxiliaryPrimeResidue
  omega

theorem secondAuxiliaryPrimeResidue_mod (z : ℝ) {q : ℕ} (hq : Odd q) :
    secondAuxiliaryPrimeResidue z q % 16 = 7 := by
  obtain ⟨k, hk⟩ := secondAuxiliaryPrimeOddFactor_odd z hq
  unfold secondAuxiliaryPrimeResidue
  omega

theorem secondAuxiliaryPrimeResidue_coprime (z : ℝ) {q : ℕ} (hq : Odd q) :
    (secondAuxiliaryPrimeResidue z q).Coprime (secondAuxiliaryPrimeModulus z q) := by
  let a := secondAuxiliaryPrimeResidue z q
  let M := secondAuxiliaryPrimeOddFactor z q
  have h16 : a.Coprime 16 := by
    have ha : Odd a := by
      apply Nat.odd_iff.mpr
      have h := secondAuxiliaryPrimeResidue_mod z hq
      omega
    exact ha.coprime_two_right.pow_right 4
  have hM : a.Coprime M := by
    have ha1 : a.Coprime (a + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    rw [secondAuxiliaryPrimeResidue_succ z hq] at ha1
    exact ha1.of_dvd_right (dvd_mul_left _ _)
  exact h16.mul_right hM

theorem secondAuxiliaryPrimeModulus_log_le {z : ℝ} {q : ℕ}
    (hz : 0 ≤ z) (hq : q.Prime) (hqsize : Real.log q ≤ z) :
    Real.log (secondAuxiliaryPrimeModulus z q) ≤ Real.log 16 + (1 + Real.log 4) * z := by
  let s := smallOddPrimes z
  have hp (p : ℕ) (hp : p ∈ s) : p.Prime := ((Finset.mem_filter.mp hp).2).1
  have hterm (p : ℕ) (hm : p ∈ s) : 0 < (p : ℝ) := by exact_mod_cast (hp p hm).pos
  have hq₀ : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hprod : 0 < ∏ p ∈ s, (p : ℝ) := Finset.prod_pos hterm
  have hsum : (∑ p ∈ s, Real.log p) ≤ Real.log 4 * z := by
    apply le_trans _ (Chebyshev.theta_le_log4_mul_x hz)
    unfold Chebyshev.theta
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp'
      obtain ⟨hpI, hpP, _⟩ := Finset.mem_filter.mp hp'
      exact Finset.mem_filter.mpr ⟨hpI, hpP⟩
    · intro p hp' _
      exact Real.log_nonneg (by exact_mod_cast ((Finset.mem_filter.mp hp').2).pos)
  change Real.log ((16 * (q * ∏ p ∈ s, p) : ℕ) : ℝ) ≤ _
  push_cast
  rw [Real.log_mul (by norm_num) (mul_pos hq₀ hprod).ne', Real.log_mul hq₀.ne' hprod.ne',
    Real.log_prod (fun p hp => (hterm p hp).ne')]
  linarith

/-- The search pool for the second auxiliary prime in Theorem 5.12. -/
noncomputable def secondAuxiliaryPrimePool (z z' : ℝ) (q : ℕ) : Finset ℕ :=
  (Finset.Ioc (Nat.floor (Real.exp (z' / 2))) (Nat.floor (Real.exp z'))).filter
    fun p => p.Prime ∧ p ≡ secondAuxiliaryPrimeResidue z q [MOD secondAuxiliaryPrimeModulus z q]

theorem mem_secondAuxiliaryPrimePool {z z' : ℝ} {q d : ℕ} :
    d ∈ secondAuxiliaryPrimePool z z' q ↔
      d.Prime ∧ d ≡ secondAuxiliaryPrimeResidue z q [MOD secondAuxiliaryPrimeModulus z q] ∧
        z' / 2 < Real.log d ∧ Real.log d ≤ z' := by
  rw [secondAuxiliaryPrimePool, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hd, hmod⟩
    have hd₀ : (0 : ℝ) < d := by exact_mod_cast hd.pos
    exact ⟨hd, hmod, (Real.lt_log_iff_exp_lt hd₀).mpr ((Nat.floor_lt' hd.ne_zero).mp hlo),
      (Real.log_le_iff_le_exp hd₀).mpr ((Nat.le_floor_iff' hd.ne_zero).mp hhi)⟩
  · rintro ⟨hd, hmod, hlo, hhi⟩
    have hd₀ : (0 : ℝ) < d := by exact_mod_cast hd.pos
    exact ⟨⟨(Nat.floor_lt' hd.ne_zero).mpr ((Real.lt_log_iff_exp_lt hd₀).mp hlo),
      (Nat.le_floor_iff' hd.ne_zero).mpr ((Real.log_le_iff_le_exp hd₀).mp hhi)⟩, hd, hmod⟩

/-- All congruence and size conditions of the Selmer pair follow from the two
search pools. The analytic selection must still produce a good prime in each pool. -/
theorem selmerWindowPair_of_mem_auxiliaryPrimePools {ε base : ℝ} {q d : ℕ+}
    (hbase : 2 ≤ base) (hq : (q : ℕ) ∈ firstAuxiliaryPrimePool (base ^ (ε / 5)))
    (hd : (d : ℕ) ∈ secondAuxiliaryPrimePool (base ^ (ε / 5))
      (base ^ (ε / 5) * Real.log base ^ (2 : ℕ)) q) :
    SelmerWindowPair ε base q d := by
  obtain ⟨hqprime, hqmod, hqlo, hqhi⟩ := mem_firstAuxiliaryPrimePool.mp hq
  obtain ⟨hdprime, hdmod, hdlo, hdhi⟩ := mem_secondAuxiliaryPrimePool.mp hd
  let z := base ^ (ε / 5)
  let M := secondAuxiliaryPrimeOddFactor z q
  have hqodd : Odd (q : ℕ) := Nat.odd_iff.mpr (by omega)
  have hd16 := Nat.ModEq.of_dvd (show 16 ∣ secondAuxiliaryPrimeModulus z q from dvd_mul_right _ _) hdmod
  change (d : ℕ) % 16 = secondAuxiliaryPrimeResidue z q % 16 at hd16
  have hdres : (d : ℕ) % 16 = 7 := hd16.trans (secondAuxiliaryPrimeResidue_mod z hqodd)
  have hdM : M ∣ (d : ℕ) + 1 := by
    have hdiv : M ∣ secondAuxiliaryPrimeModulus z q := by
      change M ∣ 16 * M
      exact dvd_mul_left _ _
    have h := Nat.ModEq.of_dvd hdiv
      (hdmod.add_right 1)
    rw [secondAuxiliaryPrimeResidue_succ z hqodd] at h
    exact Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)))
  refine ⟨hbase, hqprime, hdprime, hqmod, hdres, hqlo, hqhi, hdlo, hdhi,
    dvd_trans (show (q : ℕ) ∣ M from dvd_mul_right _ _) hdM, ?_⟩
  intro p hp hpodd hple
  have hmem : p ∈ smallOddPrimes z := Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hp.pos, (Nat.le_floor_iff' hp.ne_zero).mpr hple⟩, hp, hpodd⟩
  have hpM : p ∣ M :=
    (Finset.dvd_prod_of_mem (fun n : ℕ => n) hmem).trans (dvd_mul_left _ _)
  exact hpM.trans hdM

/-- An exceptional subfamily occupying at most a negative power of the base
cannot exhaust a nonempty search pool. -/
theorem exists_goodAuxiliaryPrime
    {pool bad : Finset ℕ} (hpool : pool.Nonempty) {base τ : ℝ}
    (hbase : 1 < base) (hτ : 0 < τ) (hbad : (bad.card : ℝ) ≤ base ^ (-τ) * pool.card) :
    ∃ p ∈ pool, p ∉ bad := by
  classical
  by_contra! h
  have hsub : pool ⊆ bad := fun _ hp => h _ hp
  have hcard : (pool.card : ℝ) ≤ bad.card := by exact_mod_cast Finset.card_le_card hsub
  have hpos : (0 : ℝ) < pool.card := by exact_mod_cast Finset.card_pos.mpr hpool
  have hr : base ^ (-τ) < 1 := by
    rw [← Real.rpow_zero base]
    exact Real.rpow_lt_rpow_of_exponent_lt hbase (by linarith)
  exact (not_lt_of_ge (hcard.trans hbad))
    (by simpa only [one_mul] using mul_lt_mul_of_pos_right hr hpos)

/-- Combine the two exceptional-set bounds into a single good window pair.
The second bound needs to hold only for a first prime that survived its test. -/
theorem eventually_exists_selmerWindowPair_of_exceptional_counts
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∀ᶠ base : ℝ in atTop, ∀ (goodQ : ℕ → Prop) (goodD : ℕ → ℕ → Prop),
      let z := base ^ (ε / 5)
      let z' := z * Real.log base ^ (2 : ℕ)
      let Q := firstAuxiliaryPrimePool z
      let D := secondAuxiliaryPrimePool z z'
      ((Q.filter fun q => ¬goodQ q).card : ℝ) ≤ base ^ (-τ) * Q.card →
      (∀ q ∈ Q, goodQ q → (D q).Nonempty ∧
        ((D q).filter fun d => ¬goodD q d).card ≤ base ^ (-τ) * (D q).card) →
      ∃ q d : ℕ+, SelmerWindowPair ε base q d ∧ goodQ q ∧ goodD q d := by
  classical
  filter_upwards [eventually_firstAuxiliaryPrimePool_nonempty hε, eventually_ge_atTop (2 : ℝ)]
    with base hQ hbase goodQ goodD z z' Q D hbadQ hbadD
  have hbase₁ : 1 < base := (by norm_num : (1 : ℝ) < 2).trans_le hbase
  obtain ⟨q, hq, hqn⟩ := exists_goodAuxiliaryPrime hQ hbase₁ hτ hbadQ
  have hqg : goodQ q := by
    by_contra hn
    exact hqn (Finset.mem_filter.mpr ⟨hq, hn⟩)
  obtain ⟨hD, hbadDq⟩ := hbadD q hq hqg
  obtain ⟨d, hd, hdn⟩ := exists_goodAuxiliaryPrime hD hbase₁ hτ hbadDq
  have hdg : goodD q d := by
    by_contra hn
    exact hdn (Finset.mem_filter.mpr ⟨hd, hn⟩)
  let q' : ℕ+ := ⟨q, (mem_firstAuxiliaryPrimePool.mp hq).1.pos⟩
  let d' : ℕ+ := ⟨d, (mem_secondAuxiliaryPrimePool.mp hd).1.pos⟩
  exact ⟨q', d', selmerWindowPair_of_mem_auxiliaryPrimePools hbase hq hd, hqg, hdg⟩

end Riemann
