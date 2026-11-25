module

public import Riemann.SelmerWindowSizes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Utilities.ExponentialGrowth

@[expose] public section

open Filter Asymptotics Utilities
open scoped BigOperators

namespace Riemann

/-- The finite partial sums in the odd-prime portions of Theorem 17.12. -/
def OddSelmerLengthBound (lengths : ℕ → ℕ → WithTop ℕ) (cutoff : ℕ) (B : ℝ) : Prop :=
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ i ∈ Finset.Ico 1 cutoff, lengths ℓ i ≠ ⊤) ∧
  ∀ primes : Finset ℕ, (∀ ℓ ∈ primes, ℓ.Prime ∧ ℓ ≠ 2) →
    (∑ ℓ ∈ primes, selmerWeightedLength lengths cutoff ℓ) ≤ B

/-- Finiteness and the unweighted sum of the lengths at a single prime. -/
def SelmerPrimeLengthBound (lengths : ℕ → ℕ → WithTop ℕ) (ℓ cutoff : ℕ) (B : ℝ) : Prop :=
  (∀ i ∈ Finset.Ico 1 cutoff, lengths ℓ i ≠ ⊤) ∧
  selmerTwistLength lengths cutoff ℓ ≤ B

/-- The prime-two estimate of Theorem 17.12 before the weight `log 2`. -/
abbrev TwoSelmerLengthBound (lengths : ℕ → ℕ → WithTop ℕ) (cutoff : ℕ) (B : ℝ) : Prop :=
  SelmerPrimeLengthBound lengths 2 cutoff B

theorem selmerPrimeLengthBound_of_pointwise {lengths : ℕ → ℕ → WithTop ℕ}
    {ℓ t : ℕ} {T b B : ℝ} (hb : 0 ≤ b) (ht : (t : ℝ) ≤ T) (hB : T * b ≤ B)
    (h : ∀ i ∈ Finset.Ico 1 t, lengths ℓ i ≠ ⊤ ∧ (((lengths ℓ i).untopD 0 : ℕ) : ℝ) ≤ b) :
    SelmerPrimeLengthBound lengths ℓ t B := by
  refine ⟨fun i hi => (h i hi).1, ?_⟩
  have hcard : ((Finset.Ico 1 t).card : ℝ) ≤ t := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le t 1
  calc
    selmerTwistLength lengths t ℓ ≤ ∑ _i ∈ Finset.Ico 1 t, b :=
      Finset.sum_le_sum fun i hi => (h i hi).2
    _ = ((Finset.Ico 1 t).card : ℝ) * b := by simp
    _ ≤ T * b := mul_le_mul_of_nonneg_right (hcard.trans ht) hb
    _ ≤ B := hB

/-- Assemble the prime-two estimate and the two odd-prime estimates using
additivity of the length at each odd prime. -/
theorem selmerLengthBound_of_parts {lengths plus minus : ℕ → ℕ → WithTop ℕ}
    {cutoff : ℕ} {B₂ Bplus Bminus : ℝ}
    (h₂ : TwoSelmerLengthBound lengths cutoff B₂)
    (hplus : OddSelmerLengthBound plus cutoff Bplus)
    (hminus : OddSelmerLengthBound minus cutoff Bminus)
    (hsplit : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ i ∈ Finset.Ico 1 cutoff,
      lengths ℓ i = plus ℓ i + minus ℓ i) :
    SelmerLengthBound lengths cutoff (Real.log 2 * B₂ + Bplus + Bminus) := by
  classical
  have hfinite (ℓ : ℕ) (hp : ℓ.Prime) (i : ℕ) (hi : i ∈ Finset.Ico 1 cutoff) :
      lengths ℓ i ≠ ⊤ := by
    by_cases hℓ : ℓ = 2
    · exact hℓ ▸ h₂.1 i hi
    · rw [hsplit ℓ hp hℓ i hi]
      simp [WithTop.add_eq_top, hplus.1 ℓ hp hℓ i hi, hminus.1 ℓ hp hℓ i hi]
  let weight (data : ℕ → ℕ → WithTop ℕ) (ℓ : ℕ) :=
    selmerWeightedLength data cutoff ℓ
  refine ⟨hfinite, fun primes hp => ?_⟩
  let odd := primes.erase 2
  have hodd (ℓ : ℕ) (hℓ : ℓ ∈ odd) : ℓ.Prime ∧ ℓ ≠ 2 :=
    ⟨hp ℓ (Finset.mem_of_mem_erase hℓ), (Finset.mem_erase.mp hℓ).1⟩
  have hsum (ℓ : ℕ) (hℓ : ℓ ∈ odd) : weight lengths ℓ = weight plus ℓ + weight minus ℓ := by
    dsimp only [weight, selmerWeightedLength, selmerTwistLength]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsplit ℓ (hodd ℓ hℓ).1 (hodd ℓ hℓ).2 i hi]
    rcases WithTop.ne_top_iff_exists.mp (hplus.1 ℓ (hodd ℓ hℓ).1 (hodd ℓ hℓ).2 i hi) with ⟨a, ha⟩
    rcases WithTop.ne_top_iff_exists.mp (hminus.1 ℓ (hodd ℓ hℓ).1 (hodd ℓ hℓ).2 i hi) with ⟨b, hb⟩
    rw [← ha, ← hb, ← WithTop.coe_add]
    exact Nat.cast_add a b
  have ht : weight lengths 2 ≤ Real.log 2 * B₂ :=
    mul_le_mul_of_nonneg_left h₂.2 (Real.log_nonneg (by norm_num))
  have hnonneg : 0 ≤ weight lengths 2 := by
    dsimp only [weight, selmerWeightedLength, selmerTwistLength]
    exact mul_nonneg (Real.log_nonneg (by norm_num))
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hprimes : (∑ ℓ ∈ primes, weight lengths ℓ) ≤
      weight lengths 2 + ∑ ℓ ∈ odd, weight lengths ℓ := by
    by_cases hm : 2 ∈ primes
    · simpa only [odd, add_comm] using (Finset.sum_erase_add _ (weight lengths) hm).ge
    · rw [show odd = primes from Finset.erase_eq_of_notMem hm]
      linarith only [hnonneg]
  calc
    _ ≤ weight lengths 2 + ∑ ℓ ∈ odd, weight lengths ℓ := hprimes
    _ = weight lengths 2 + ∑ ℓ ∈ odd, weight plus ℓ + ∑ ℓ ∈ odd, weight minus ℓ := by
      rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib, add_assoc]
    _ ≤ _ := add_le_add (add_le_add ht (hplus.2 odd hodd)) (hminus.2 odd hodd)

/-- The four contributions to Theorem 17.12 fit under the final budget once
the conductor-times-cutoff terms have been bounded by smaller exponentials. -/
theorem eventually_selmerBudget_le {ε Cplus Cminus : ℝ} (hε : 0 < ε)
    (hplus : 0 ≤ Cplus) (hminus : 0 ≤ Cminus) :
    ∀ᶠ x : ℝ in atTop, Real.log 2 * Real.exp (x ^ (4 * ε / 5)) +
      (Real.exp (2 * Cplus * x ^ (ε / 4)) + Cplus * Real.exp (x ^ (4 * ε / 5))) +
      Cminus * Real.exp (6 * x ^ (ε / 4)) ≤ Real.exp (x ^ ε / 2) := by
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have h80 : 0 < 4 * ε / 5 := by positivity
  have h80ε : 4 * ε / 5 < ε := by linarith
  have h25 : 0 < ε / 4 := by positivity
  have h25ε : ε / 4 < ε := by linarith
  filter_upwards [
    Utilities.eventually_mul_exp_rpow_le (c := 1) h80 h80ε
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hquarter,
    Utilities.eventually_mul_exp_rpow_le (c := 2 * Cplus) h25 h25ε
      (by norm_num : (0 : ℝ) ≤ 1) hquarter,
    Utilities.eventually_mul_exp_rpow_le (c := 1) h80 h80ε hplus hquarter,
    Utilities.eventually_mul_exp_rpow_le (c := 6) h25 h25ε hminus hquarter]
    with x htwo hpoly htail hminus'
  simp only [one_mul] at htwo hpoly htail
  linarith only [htwo, hpoly, htail, hminus']

/-- The uniform thresholds in the analytic assembly can be absorbed into
`X₀`, with the cofinal windows and the original twist indices unchanged. -/
theorem hasSelmerWindowBound_of_part_estimates {lengths plus minus : NumberFieldSelmerLengths}
    (hparts : ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∀ e : ℝ → ℕ,
        (∀ x ≥ 1, x ^ (2 + 8 * ε) ≤ (2 : ℝ) ^ e x ∧
          (2 : ℝ) ^ e x ≤ 2 * x ^ (2 + 8 * ε)) →
        ∃ J X₀ Cplus Cminus : ℝ, 1 ≤ J ∧ 1 ≤ X₀ ∧ 0 ≤ Cplus ∧ 0 ≤ Cminus ∧
          ∀ X ≥ X₀, ∀ q d : ℕ+, SelmerWindowPair ε (X ^ (1 / J)) q d →
            ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ≤ X ^ (1 / 2 : ℝ) ∧
              ∀ x ∈ Set.Icc Y (Y ^ (2 : ℕ)),
                let E := selmerHostField target (e x) q d
                let t := Nat.floor (x ^ (401 : ℕ))
                TwoSelmerLengthBound (lengths E) t (Real.exp (x ^ (4 * ε / 5))) ∧
                OddSelmerLengthBound (plus E) t
                  (Real.exp (2 * Cplus * x ^ (ε / 4)) + Cplus * Real.exp (x ^ (4 * ε / 5))) ∧
                OddSelmerLengthBound (minus E) t (Cminus * Real.exp (6 * x ^ (ε / 4))) ∧
                (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ i ∈ Finset.Ico 1 t,
                  lengths E ℓ i = plus E ℓ i + minus E ℓ i)) :
    HasSelmerWindowBound lengths := by
  intro target hprimitive ε hε hεmax e he
  obtain ⟨J, X₀, Cplus, Cminus, hJ, hX₀, hCplus, hCminus, hwindows⟩ :=
    hparts target hprimitive ε hε hεmax e he
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_selmerBudget_le hε hCplus hCminus)
  refine ⟨J, max X₀ ((max 1 A) ^ J), hJ, hX₀.trans (le_max_left _ _), fun X hX => ?_⟩
  intro base q d hpair
  have hbase : A ≤ base := by
    have hJpos := zero_lt_one.trans_le hJ
    have hApos : 0 ≤ max 1 A := zero_le_one.trans (le_max_left _ _)
    have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hApos J)
      ((le_max_right X₀ _).trans hX) (one_div_nonneg.mpr hJpos.le)
    rw [one_div, Real.rpow_rpow_inv hApos hJpos.ne'] at hmono
    exact (le_max_right 1 A).trans (by simpa only [base, one_div] using hmono)
  obtain ⟨Y, hY, hYmax, hwindow⟩ := hwindows X ((le_max_left _ _).trans hX) q d hpair
  refine ⟨Y, hY, hYmax, fun x hx => ?_⟩
  obtain ⟨htwo, hplus, hminus, hsplit⟩ := hwindow x hx
  have hsum := selmerLengthBound_of_parts htwo hplus hminus hsplit
  exact hsum.mono le_rfl (hA x ((hbase.trans hY).trans hx.1))

end Riemann
