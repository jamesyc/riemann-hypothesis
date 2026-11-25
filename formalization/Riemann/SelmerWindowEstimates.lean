module

public import Riemann.SelmerMinusAssembly
public import Riemann.SelmerPlusResidualCounts
public import Riemann.SelmerSmallPrimeWindows

@[expose] public section

open Utilities
open scoped BigOperators

namespace Riemann

/-- Finiteness and the generic count of §17.3 with one fixed exceptional set. -/
theorem selmerPlus_genericPrime_counts
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive) :
    ∃ (bad : Finset ℕ) (A : ℕ) (P : ℝ), 0 < P ∧
      (∀ ℓ ∈ bad, ℓ.Prime ∧ ℓ ≠ 2) ∧
      ∀ (e t : ℕ) (q d : ℕ+), 2 ≤ e → 2 ≤ t → SelmerEstimatePrimePair target q d →
        max P (2 * (t : ℝ) + 1) < (q : ℕ) → max P (2 * (t : ℝ) + 1) < (d : ℕ) →
        let F := selmerHostField target e q d
        let M := (selmerHostConductor target e q d : ℝ) * t
        let L := numberFieldSelmerSignLengths true F
        (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∉ bad →
          ∀ i ∈ Finset.Ico 1 t, ¬ ℓ - 1 ∣ 2 * i → L ℓ i ≠ ⊤) ∧
        (∀ i ∈ Finset.Ico 1 t, ∀ primes : Finset ℕ,
          (∀ ℓ ∈ primes, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∉ bad ∧ ¬ ℓ - 1 ∣ 2 * i) →
          (∑ ℓ ∈ primes, Real.log ℓ * (((L ℓ i).untopD 0 : ℕ) : ℝ)) ≤ M ^ A) := by
  classical
  obtain ⟨bad, A, P, hP, hbad, hcounts⟩ := selmerPlus_genericRationalCharacterCounts target hprim
  let o := orderOf target.character
  let badOrder := o.primeFactors.filter (· ≠ 2)
  let M₀ : ℝ := (target.modulus : ℕ)
  refine ⟨bad ∪ badOrder, 3 * A, max P M₀, hP.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro ℓ hℓ
    rcases Finset.mem_union.mp hℓ with h | h
    · exact hbad ℓ h
    · obtain ⟨hp, ho⟩ := Finset.mem_filter.mp h
      exact ⟨Nat.prime_of_mem_primeFactors hp, ho⟩
  intro e t q d he ht hpair hq hd
  have hq₀ := (max_le_max_right _ (le_max_left P M₀)).trans_lt hq
  have hd₀ := (max_le_max_right _ (le_max_left P M₀)).trans_lt hd
  have hqN : (target.modulus : ℕ) ≤ (q : ℕ) := by
    have h : ((target.modulus : ℕ) : ℝ) < (q : ℕ) :=
      ((le_max_right P M₀).trans (le_max_left _ _)).trans_lt hq
    exact_mod_cast h.le
  have hout (ℓ : ℕ) (hp : ℓ.Prime) (ho : ℓ ≠ 2) (h : ℓ ∉ bad ∪ badOrder) :
      ℓ ∉ bad ∧ ¬ ℓ ∣ o := by
    refine ⟨fun hmem => h (Finset.mem_union_left _ hmem), fun hdiv => ?_⟩
    exact h (Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp, hdiv, (orderOf_pos target.character).ne'⟩, ho⟩))
  have hper (i : ℕ) (hi : i ∈ Finset.Ico 1 t) :
      ∃ B : ℕ → ℝ,
        (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∉ bad ∪ badOrder → ¬ ℓ - 1 ∣ 2 * i →
          let L := numberFieldSelmerSignLengths true (selmerHostField target e q d) ℓ i
          L ≠ ⊤ ∧ ((L.untopD 0 : ℕ) : ℝ) ≤ B ℓ) ∧
        ∀ S : Finset ℕ,
          (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∉ bad ∪ badOrder ∧ ¬ ℓ - 1 ∣ 2 * i) →
          (∑ ℓ ∈ S, Real.log ℓ * B ℓ) ≤ ((selmerHostModulus target e q d : ℝ) * t) ^ A := by
    obtain ⟨B, hlen, hsum⟩ := hcounts e t q d he ht hpair hq₀ hd₀ i hi
    refine ⟨B, ?_, ?_⟩
    · intro ℓ hp ho hb hg
      obtain ⟨hbad', horder⟩ := hout ℓ hp ho hb
      have hdegree : ¬ ℓ ∣ Module.finrank ℚ (selmerHostField target e q d) :=
        fun h => horder (odd_prime_dvd_order_of_dvd_selmerHostDegree target e q d hpair hp ho h)
      exact selmerPlus_hostLength_le_of_rationalPrimeBound target e q d ℓ hp i (B ℓ) ho hdegree
        (hlen ℓ hp ho hbad' horder hg)
    · intro S hS
      exact hsum S fun ℓ hℓ =>
        let ⟨hp, ho, hb, hg⟩ := hS ℓ hℓ
        let ⟨hb', hd'⟩ := hout ℓ hp ho hb
        ⟨hp, ho, hb', hd', hg⟩
  refine ⟨?_, ?_⟩
  · intro ℓ hp ho hb i hi hg
    obtain ⟨_, hlen, _⟩ := hper i hi
    exact (hlen ℓ hp ho hb hg).1
  · intro i hi S hS
    obtain ⟨B, hlen, hsum⟩ := hper i hi
    refine (le_trans (b := ∑ ℓ ∈ S, Real.log ℓ * B ℓ) ?_ (le_trans (hsum S hS) ?_))
    · apply Finset.sum_le_sum
      intro ℓ hℓ
      obtain ⟨hp, ho, hb, hg⟩ := hS ℓ hℓ
      exact mul_le_mul_of_nonneg_left (hlen ℓ hp ho hb hg).2 (Real.log_natCast_nonneg ℓ)
    · exact selmerHostModulus_cutoff_pow_le_conductor target e q d hpair hqN (by omega) A

/-- Use the same exceptional set and size threshold for both good-prime counts. -/
theorem selmerPlus_goodPrime_counts
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive) :
    ∃ (bad : Finset ℕ) (A B : ℕ) (P : ℝ), 0 < P ∧
      (∀ ℓ ∈ bad, ℓ.Prime ∧ ℓ ≠ 2) ∧
      ∀ (e t : ℕ) (q d : ℕ+), 2 ≤ e → 2 ≤ t → SelmerEstimatePrimePair target q d →
        max P (2 * (t : ℝ) + 1) < (q : ℕ) → max P (2 * (t : ℝ) + 1) < (d : ℕ) →
        let F := selmerHostField target e q d
        let M := (selmerHostConductor target e q d : ℝ) * t
        let L := numberFieldSelmerSignLengths true F
        (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∉ bad →
          ∀ i ∈ Finset.Ico 1 t, L ℓ i ≠ ⊤) ∧
        (∀ i ∈ Finset.Ico 1 t, ∀ primes : Finset ℕ,
          (∀ ℓ ∈ primes, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∉ bad ∧ ¬ ℓ - 1 ∣ 2 * i) →
          (∑ ℓ ∈ primes, Real.log ℓ * (((L ℓ i).untopD 0 : ℕ) : ℝ)) ≤ M ^ A) ∧
        (∀ i ∈ Finset.Ico 1 t, ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∉ bad →
          ℓ - 1 ∣ 2 * i → (((L ℓ i).untopD 0 : ℕ) : ℝ) ≤ M ^ B) := by
  classical
  obtain ⟨bad₀, A, P₀, hP₀, hbad₀, hgen⟩ := selmerPlus_genericPrime_counts target hprim
  obtain ⟨bad₁, B, P₁, _, hbad₁, hres⟩ := selmerPlus_residualPrime_counts target hprim
  refine ⟨bad₀ ∪ bad₁, A, B, max P₀ P₁, hP₀.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro ℓ hℓ
    exact (Finset.mem_union.mp hℓ).elim (hbad₀ ℓ) (hbad₁ ℓ)
  intro e t q d he ht hpair hq hd
  obtain ⟨hfin, hgeneric⟩ := hgen e t q d he ht hpair
    ((max_le_max_right _ (le_max_left P₀ P₁)).trans_lt hq)
    ((max_le_max_right _ (le_max_left P₀ P₁)).trans_lt hd)
  have hresidual := hres e t q d he ht hpair
    ((max_le_max_right _ (le_max_right P₀ P₁)).trans_lt hq)
    ((max_le_max_right _ (le_max_right P₀ P₁)).trans_lt hd)
  have hout₀ {ℓ : ℕ} (h : ℓ ∉ bad₀ ∪ bad₁) : ℓ ∉ bad₀ :=
    fun hmem => h (Finset.mem_union_left _ hmem)
  have hout₁ {ℓ : ℕ} (h : ℓ ∉ bad₀ ∪ bad₁) : ℓ ∉ bad₁ :=
    fun hmem => h (Finset.mem_union_right _ hmem)
  refine ⟨?_, ?_, ?_⟩
  · intro ℓ hℓ ho hout i hi
    by_cases hdiv : ℓ - 1 ∣ 2 * i
    · exact (hresidual i hi ℓ hℓ ho (hout₁ hout) hdiv).1
    · exact hfin ℓ hℓ ho (hout₀ hout) i hi hdiv
  · intro i hi primes hp
    exact hgeneric i hi primes fun ℓ hℓ =>
      let ⟨hprime, hodd, hout, hdiv⟩ := hp ℓ hℓ
      ⟨hprime, hodd, hout₀ hout, hdiv⟩
  · intro i hi ℓ hℓ ho hout hdiv
    exact (hresidual i hi ℓ hℓ ho (hout₁ hout) hdiv).2

/-- The arithmetic plus and prime-two estimates on windows, Theorem 17.12(I). -/
theorem numberField_selmer_plus_two_window_estimates : HasSelmerPlusTwoWindowEstimates := by
  intro target hprim ε hε hsmall e t hadm
  obtain ⟨bad, A, B, P₀, hP₀, hbad, hgood⟩ := selmerPlus_goodPrime_counts target hprim
  obtain ⟨J, C, P₁, X₁, hJ, hC, hP₁, hX₁, hwindows⟩ :=
    selmerPlus_two_badPrime_windows target hprim ε hε hsmall e t hadm bad hbad
  let D : ℝ := (A + B + 6 : ℕ) + C
  refine ⟨J, D, max P₀ P₁, X₁, hJ, by dsimp [D]; positivity,
    hP₀.trans_le (le_max_left _ _), by linarith, ?_⟩
  intro X hX q d hpair hq hd hlog
  obtain ⟨Y, hY₂, hYlo, hYhi, hY⟩ := hwindows X hX q d hpair
    ((max_le_max_right _ (le_max_right P₀ P₁)).trans_lt hq)
    ((max_le_max_right _ (le_max_right P₀ P₁)).trans_lt hd) hlog
  refine ⟨Y, hYlo, hYhi, fun x hx => ?_⟩
  obtain ⟨he, _, ht, htx⟩ := hadm x (hY₂.trans hx.1)
  have hX₀ : 0 ≤ X := by linarith [hX₁.trans hX]
  have hxX : x ≤ X := hx.2.trans (by
    rw [← Real.sqrt_eq_rpow] at hYhi
    rw [← Real.sq_sqrt hX₀]
    exact pow_le_pow_left₀ (by linarith) hYhi _)
  have htX := htx.trans (pow_le_pow_left₀ (by linarith [hx.1]) hxX _)
  have hPq : max P₀ (2 * (t x : ℝ) + 1) < (q : ℕ) :=
    (max_le_max (le_max_left P₀ P₁) (by linarith)).trans_lt hq
  have hPd : max P₀ (2 * (t x : ℝ) + 1) < (d : ℕ) :=
    (max_le_max (le_max_left P₀ P₁) (by linarith)).trans_lt hd
  obtain ⟨hfin₀, hgeneric, hresidue⟩ := hgood (e x) (t x) q d he ht hpair hPq hPd
  obtain ⟨htwo, hfin₁, hbudget⟩ := hY x hx
  let M := (selmerHostConductor target (e x) q d : ℝ) * t x
  have hf : 1 ≤ (selmerHostConductor target (e x) q d : ℝ) := by
    exact_mod_cast selmerHostConductor_pos target (e x) q d
  have htM : (t x : ℝ) ≤ M := by
    dsimp [M]
    exact le_mul_of_one_le_left (by positivity) hf
  have hM : 2 ≤ M := (by exact_mod_cast ht : (2 : ℝ) ≤ t x).trans htM
  obtain ⟨hfin, hsum⟩ := oddSelmerLengthBound_of_plusCases hM htM bad
    (fun ℓ hℓ hodd i hi => by
      by_cases hmem : ℓ ∈ bad
      · exact hfin₁ ℓ hmem i hi
      · exact hfin₀ ℓ hℓ hodd hmem i hi)
    hgeneric hresidue hbudget
  refine ⟨htwo, hfin, fun S hS => (hsum S hS).trans ?_⟩
  change M ^ (A + B + 6) + C * _ ≤ M ^ D + D * _
  apply add_le_add
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [D]; linarith)
  · exact mul_le_mul_of_nonneg_right (by
      dsimp [D]
      linarith [show (0 : ℝ) ≤ (A + B + 6 : ℕ) by positivity]) (Real.exp_nonneg _)

/-- Hypothesis 17.11 with the host fields and Selmer groups fixed. -/
theorem numberField_selmer_window_bound : HasSelmerWindowBound numberFieldSelmerLengths :=
  numberField_selmer_window_bound_of_estimates numberField_selmer_plus_two_window_estimates
    numberField_selmer_minus_estimate

end Riemann
