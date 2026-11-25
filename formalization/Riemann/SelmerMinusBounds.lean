module

public import Riemann.HostBaseGroup
public import Riemann.SelmerWindowBound
public import Utilities.GeneralizedBernoulli
import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

open Utilities
open scoped BigOperators

namespace Riemann

/-- The odd part of the host degree comes entirely from the target character. -/
theorem selmerHostDegree_eq_dyadic_mul (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (hp : SelmerEstimatePrimePair target q d) :
    Module.finrank ℚ (selmerHostField target e q d) =
      Nat.card (selmerBaseDyadicReduction target e).ker * 2 ^ (e + 2) := by
  let N := selmerBaseModulus target e
  have hq₂ : (q : ℕ) ≠ 2 := by
    have := hp.q_residue
    omega
  have hd₂ : (d : ℕ) ≠ 2 := by
    have := hp.d_residue
    omega
  have hqd : (q : ℕ) ≠ d := by
    have := hp.q_residue
    have := hp.d_residue
    omega
  obtain ⟨hqN₀, hdN₀⟩ := Nat.coprime_mul_iff_left.mp hp.coprime
  have hq : N.Coprime q := selmerBaseModulus_coprime_of_prime target e hp.q_prime hq₂ hqN₀
  have hd : (N * (q : ℕ)).Coprime d :=
    (selmerBaseModulus_coprime_of_prime target e hp.d_prime hd₂ hdN₀).mul_left
      ((Nat.coprime_primes hp.q_prime hp.d_prime).mpr hqd)
  let : Fact (q : ℕ).Prime := ⟨hp.q_prime⟩
  let : Fact (d : ℕ).Prime := ⟨hp.d_prime⟩
  let _ := selmerHostField_isAbelianGalois target e q d
  have hq4 : (q : ℕ) % 4 = 3 := by
    have := hp.q_residue
    omega
  have hd4 : (d : ℕ) % 4 = 3 := by
    have := hp.d_residue
    omega
  rw [← IsGalois.card_aut_eq_finrank,
    Nat.card_congr (selmerHostGalCRT target e q d hq hd).toEquiv,
    Nat.card_prod, Nat.card_prod, selmerSquareClass_card hq4, selmerSquareClass_card hd4]
  change Nat.card (SelmerHostBaseGroup target e) * 2 * 2 = _
  rw [selmerHostBaseGroup_card]
  calc
    _ = Nat.card (selmerBaseDyadicReduction target e).ker * (2 ^ e * 2 ^ (2 : ℕ)) := by ring
    _ = _ := congrArg (Nat.card (selmerBaseDyadicReduction target e).ker * ·)
      (pow_add (2 : ℕ) e 2).symm

theorem odd_prime_dvd_order_of_dvd_selmerHostDegree (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (hpair : SelmerEstimatePrimePair target q d)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (hdegree : ℓ ∣ Module.finrank ℚ (selmerHostField target e q d)) :
    ℓ ∣ orderOf target.character := by
  rw [selmerHostDegree_eq_dyadic_mul target e q d hpair] at hdegree
  rcases hℓ.dvd_mul.mp hdegree with hker | htwo
  · exact hker.trans (selmerBaseDyadicReduction_card_ker_dvd_order target e)
  · exact (hodd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow htwo))).elim

theorem log_selmerBernoulliHeightBound_le {f t i : ℕ} (hf : 0 < f)
    (ht : 2 ≤ t) (hi : i + 1 ≤ t) :
    Real.log (generalizedBernoulliHeightBound f (i + 1)) ≤ (2 * t + 5) * Real.log ((t : ℝ) * f) := by
  have htf : 2 ≤ t * f := ht.trans (Nat.le_mul_of_pos_right t hf)
  have htpos : 0 < t := by omega
  have h16 : 16 ≤ (t * f) ^ 4 := by
    simpa only [show (2 : ℕ) ^ 4 = 16 by norm_num] using Nat.pow_le_pow_left htf 4
  have hpow : f ^ (i + 1 + 1) ≤ (t * f) ^ (t + 1) :=
    (Nat.pow_le_pow_left (Nat.le_mul_of_pos_left f htpos) _).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hfac : (i + 1).factorial ≤ (t * f) ^ t := calc
    _ ≤ (i + 1) ^ (i + 1) := Nat.factorial_le_pow _
    _ ≤ t ^ (i + 1) := Nat.pow_le_pow_left hi _
    _ ≤ t ^ t := Nat.pow_le_pow_right (by omega) hi
    _ ≤ (t * f) ^ t := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right t hf) _
  have hnat : 16 * f ^ (i + 1 + 1) * (i + 1).factorial ≤ (t * f) ^ (2 * t + 5) := calc
    _ ≤ (t * f) ^ 4 * (t * f) ^ (t + 1) * (t * f) ^ t :=
      Nat.mul_le_mul (Nat.mul_le_mul h16 hpow) hfac
    _ = _ := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
  have hreal : generalizedBernoulliHeightBound f (i + 1) ≤ ((t : ℝ) * f) ^ (2 * t + 5) := by
    unfold generalizedBernoulliHeightBound
    exact_mod_cast hnat
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  calc
    _ ≤ Real.log (((t : ℝ) * f) ^ (2 * t + 5)) :=
      Real.log_le_log (by unfold generalizedBernoulliHeightBound; positivity) hreal
    _ = _ := by rw [Real.log_pow]; push_cast; ring

/-- Sum the per-twist Bernoulli and Stickelberger bounds, with the precise
exceptional primes and total budget of Theorem 17.12(II). -/
theorem oddSelmerLengthBound_of_bernoulli_stickelberger
    {lengths : ℕ → ℕ → WithTop ℕ} {C : ℝ} {n t f o : ℕ}
    (hC : 0 ≤ C) (ht : 2 ≤ t) (hf : 0 < f) (ho : 0 < o)
    (hdegree : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ n → ℓ ∣ o)
    (hfinite : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ i ∈ Finset.Ico 1 t, lengths ℓ i ≠ ⊤)
    (hbernoulli : ∀ i ∈ Finset.Ico 1 t, ∀ S : Finset ℕ,
      (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2 ∧ ¬ ℓ ∣ n) →
      (∑ ℓ ∈ S, Real.log (ℓ : ℝ) * (((lengths ℓ i).untopD 0 : ℕ) : ℝ)) ≤
        n * Real.log (generalizedBernoulliHeightBound f (i + 1)))
    (hstick : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ n → ∀ i ∈ Finset.Ico 1 t,
      Real.log (ℓ : ℝ) * (((lengths ℓ i).untopD 0 : ℕ) : ℝ) ≤
        C * ℓ * (n : ℝ) ^ (2 : ℕ) * ((i : ℝ) + 1) * (Real.log ((i : ℝ) * ℓ * f)) ^ (2 : ℕ)) :
    OddSelmerLengthBound lengths t (selmerMinusBudget C n t f o) := by
  classical
  refine ⟨hfinite, fun S hS => ?_⟩
  let S₀ := S.filter fun ℓ => ¬ ℓ ∣ n
  let S₁ := S.filter fun ℓ => ℓ ∣ n
  let w := selmerWeightedLength lengths t
  let b (ℓ : ℕ) : ℝ := (ℓ : ℝ) * (n : ℝ) ^ (2 : ℕ) * (t : ℝ) ^ (2 : ℕ) *
    (Real.log ((t : ℝ) * ℓ * f)) ^ (2 : ℕ)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have htfR : 1 ≤ (t : ℝ) * f := one_le_mul_of_one_le_of_one_le (by linarith) hfR
  have hcard : ((Finset.Ico 1 t).card : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.card_Ico, Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
  have hS₀ (ℓ : ℕ) (hℓ : ℓ ∈ S₀) : ℓ.Prime ∧ ℓ ≠ 2 ∧ ¬ ℓ ∣ n :=
    ⟨(hS ℓ (Finset.mem_filter.mp hℓ).1).1, (hS ℓ (Finset.mem_filter.mp hℓ).1).2,
      (Finset.mem_filter.mp hℓ).2⟩
  have hS₁ (ℓ : ℕ) (hℓ : ℓ ∈ S₁) : ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ n :=
    ⟨(hS ℓ (Finset.mem_filter.mp hℓ).1).1, (hS ℓ (Finset.mem_filter.mp hℓ).1).2,
      (Finset.mem_filter.mp hℓ).2⟩
  have hsum₀ : (∑ ℓ ∈ S₀, w ℓ) ≤ 3 * n * (t : ℝ) ^ (2 : ℕ) * Real.log ((t : ℝ) * f) := by
    dsimp only [w, selmerWeightedLength, selmerTwistLength]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _ ∈ Finset.Ico 1 t, (n : ℝ) * ((2 * t + 5) * Real.log ((t : ℝ) * f)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hbernoulli i hi S₀ hS₀).trans (mul_le_mul_of_nonneg_left
          (log_selmerBernoulliHeightBound_le hf ht (Finset.mem_Ico.mp hi).2) (Nat.cast_nonneg _))
      _ = ((t : ℝ) - 1) * ((2 * t + 5) * ((n : ℝ) * Real.log ((t : ℝ) * f))) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
      _ = (((t : ℝ) - 1) * (2 * t + 5)) * ((n : ℝ) * Real.log ((t : ℝ) * f)) := by ring
      _ ≤ (3 * (t : ℝ) ^ (2 : ℕ)) * ((n : ℝ) * Real.log ((t : ℝ) * f)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg htfR))
        nlinarith [sq_nonneg ((t : ℝ) - 2)]
      _ = _ := by ring
  have hstick_sum (ℓ : ℕ) (hℓ : ℓ ∈ S₁) : w ℓ ≤ C * b ℓ := by
    obtain ⟨hprime, hodd, hdvd⟩ := hS₁ ℓ hℓ
    have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hprime.one_le
    let c : ℝ := C * ℓ * (n : ℝ) ^ (2 : ℕ) * Real.log ((t : ℝ) * ℓ * f) ^ (2 : ℕ)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    dsimp only [w, selmerWeightedLength, selmerTwistLength]
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _ ∈ Finset.Ico 1 t, c * (t : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiR : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
        have hitR : (i : ℝ) + 1 ≤ t := by exact_mod_cast (Finset.mem_Ico.mp hi).2
        have hif : 1 ≤ (i : ℝ) * ℓ * f :=
          one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hiR hℓR) hfR
        have hit : (i : ℝ) ≤ t := by linarith
        have hprod := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hit (Nat.cast_nonneg ℓ)) (Nat.cast_nonneg f)
        have hlog := Real.log_le_log (zero_lt_one.trans_le hif) hprod
        have hlogSq := pow_le_pow_left₀ (Real.log_nonneg hif) hlog 2
        refine (hstick ℓ hprime hodd hdvd i hi).trans ?_
        have hm := mul_le_mul hitR hlogSq (sq_nonneg _) (zero_le_one.trans (by linarith : 1 ≤ (t : ℝ)))
        calc
          _ = (C * ℓ * (n : ℝ) ^ (2 : ℕ)) *
              (((i : ℝ) + 1) * Real.log ((i : ℝ) * ℓ * f) ^ (2 : ℕ)) := by ring
          _ ≤ (C * ℓ * (n : ℝ) ^ (2 : ℕ)) *
              ((t : ℝ) * Real.log ((t : ℝ) * ℓ * f) ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hm (by positivity)
          _ = _ := by dsimp [c]; ring
      _ = ((t : ℝ) - 1) * (c * (t : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ (t : ℝ) * (c * (t : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hc (Nat.cast_nonneg _))
      _ = _ := by dsimp [b, c]; ring
  have hsubset : S₁ ⊆ o.primeFactors.erase 2 := by
    intro ℓ hℓ
    obtain ⟨hprime, hodd, hdvd⟩ := hS₁ ℓ hℓ
    exact Finset.mem_erase.mpr ⟨hodd, Nat.mem_primeFactors.mpr
      ⟨hprime, hdegree ℓ hprime hodd hdvd, ho.ne'⟩⟩
  have hsum₁ : (∑ ℓ ∈ S₁, w ℓ) ≤ C * ∑ ℓ ∈ o.primeFactors.erase 2, b ℓ := by
    calc
      _ ≤ ∑ ℓ ∈ S₁, C * b ℓ := Finset.sum_le_sum hstick_sum
      _ = C * ∑ ℓ ∈ S₁, b ℓ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by dsimp [b]; positivity)) hC
  change (∑ ℓ ∈ S, w ℓ) ≤ _
  have hpartition : (∑ ℓ ∈ S₀, w ℓ) + ∑ ℓ ∈ S₁, w ℓ = ∑ ℓ ∈ S, w ℓ := by
    simpa only [S₀, S₁, not_not] using (Finset.sum_filter_add_sum_filter_not S (fun ℓ => ¬ ℓ ∣ n) w)
  rw [← hpartition]
  exact add_le_add hsum₀ hsum₁

/-- The per-twist minus estimates at primes prime to the host degree,
after bounding the relevant generalized Bernoulli numbers. -/
def HasSelmerBernoulliMinusEstimates : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i ≥ 1,
      let E := selmerHostField target e q d
      let n := Module.finrank ℚ E
      let f := selmerHostConductor target e q d
      let lengths := numberFieldSelmerSignLengths false E
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ¬ ℓ ∣ n → lengths ℓ i ≠ ⊤) ∧
      ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ ≠ 2 ∧ ¬ ℓ ∣ n) →
        (∑ ℓ ∈ S, Real.log (ℓ : ℝ) * (((lengths ℓ i).untopD 0 : ℕ) : ℝ)) ≤
          n * Real.log (generalizedBernoulliHeightBound f (i + 1))

/-- The per-twist Stickelberger estimates at odd primes dividing the host degree. -/
def HasSelmerStickelbergerMinusEstimates : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
      ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i ≥ 1,
        let E := selmerHostField target e q d
        let n := Module.finrank ℚ E
        let f := selmerHostConductor target e q d
        let lengths := numberFieldSelmerSignLengths false E
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ n →
          lengths ℓ i ≠ ⊤ ∧
          Real.log (ℓ : ℝ) * (((lengths ℓ i).untopD 0 : ℕ) : ℝ) ≤
            C * ℓ * (n : ℝ) ^ (2 : ℕ) * ((i : ℝ) + 1) *
              (Real.log ((i : ℝ) * ℓ * f)) ^ (2 : ℕ)

/-- The precise per-twist estimates imply the arithmetic minus part of Theorem 17.12. -/
theorem numberField_selmer_minus_estimate_of_prime_estimates
    (hBernoulli : HasSelmerBernoulliMinusEstimates)
    (hStickelberger : HasSelmerStickelbergerMinusEstimates) : HasSelmerMinusEstimate := by
  obtain ⟨C, hC, hstick⟩ := hStickelberger
  refine ⟨C, hC, fun target hprimitive e t q d he ht hpair => ?_⟩
  refine oddSelmerLengthBound_of_bernoulli_stickelberger hC ht
    (selmerHostConductor_pos target e q d) (orderOf_pos target.character)
    (fun _ => odd_prime_dvd_order_of_dvd_selmerHostDegree target e q d hpair) ?_ ?_ ?_
  · intro ℓ hℓ hodd i hi
    have hi' := (Finset.mem_Ico.mp hi).1
    by_cases hdegree : ℓ ∣ Module.finrank ℚ (selmerHostField target e q d)
    · exact (hstick target hprimitive e q d he hpair i hi' ℓ hℓ hodd hdegree).1
    · exact (hBernoulli target hprimitive e q d he hpair i hi').1 ℓ hℓ hodd hdegree
  · exact fun i hi => (hBernoulli target hprimitive e q d he hpair i (Finset.mem_Ico.mp hi).1).2
  · exact fun ℓ hℓ hodd hdegree i hi =>
      (hstick target hprimitive e q d he hpair i (Finset.mem_Ico.mp hi).1 ℓ hℓ hodd hdegree).2

end Riemann
