module

public import Riemann.SelmerLengthAssembly

@[expose] public section

open scoped BigOperators Classical

namespace Riemann

/-- The nongeneric residual branches outside the fixed bad-prime set are
supported at primes at most twice the strict twist cutoff. -/
theorem selmerPlus_residuePrime_le {ℓ i t : ℕ} (hℓ : ℓ.Prime)
    (hi : i ∈ Finset.Ico 1 t) (hdiv : ℓ - 1 ∣ 2 * i) : ℓ ≤ 2 * t := by
  obtain ⟨hi₁, hi₂⟩ := Finset.mem_Ico.mp hi
  have h := Nat.le_of_dvd (show 0 < 2 * i by omega) hdiv
  have hℓ₂ := hℓ.two_le
  omega

/-- Sum the generic and residual counts over twists and preserve the
separate window estimate for the bad primes. -/
theorem oddSelmerLengthBound_of_plusCases {lengths : ℕ → ℕ → WithTop ℕ}
    {t C K : ℕ} {M Bbad : ℝ} (hM : 2 ≤ M) (ht : (t : ℝ) ≤ M) (bad : Finset ℕ)
    (hfinite : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ i ∈ Finset.Ico 1 t, lengths ℓ i ≠ ⊤)
    (hgeneric : ∀ i ∈ Finset.Ico 1 t, ∀ primes : Finset ℕ,
      (∀ ℓ ∈ primes, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∉ bad ∧ ¬ℓ - 1 ∣ 2 * i) →
      (∑ ℓ ∈ primes, Real.log ℓ * (((lengths ℓ i).untopD 0 : ℕ) : ℝ)) ≤ M ^ C)
    (hresidue : ∀ i ∈ Finset.Ico 1 t, ∀ ℓ : ℕ,
      ℓ.Prime → ℓ ≠ 2 → ℓ ∉ bad → ℓ - 1 ∣ 2 * i →
      (((lengths ℓ i).untopD 0 : ℕ) : ℝ) ≤ M ^ K)
    (hbudget : (∑ ℓ ∈ bad, selmerWeightedLength lengths t ℓ) ≤ Bbad) :
    OddSelmerLengthBound lengths t (M ^ (C + K + 6) + Bbad) := by
  classical
  refine ⟨hfinite, fun primes hp => ?_⟩
  let good := primes.filter fun ℓ => ℓ ∉ bad
  let w := selmerWeightedLength lengths t
  let wi (i ℓ : ℕ) := Real.log ℓ * (((lengths ℓ i).untopD 0 : ℕ) : ℝ)
  have hM₁ : 1 ≤ M := by linarith
  have hM₀ : 0 ≤ M := by linarith
  have hw (ℓ : ℕ) : 0 ≤ w ℓ :=
    mul_nonneg (Real.log_natCast_nonneg ℓ) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hgood (ℓ : ℕ) (hℓ : ℓ ∈ good) : ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∉ bad := by
    obtain ⟨hp', hb⟩ := Finset.mem_filter.mp hℓ
    exact ⟨(hp ℓ hp').1, (hp ℓ hp').2, hb⟩
  have htwist (i : ℕ) (hi : i ∈ Finset.Ico 1 t) :
      (∑ ℓ ∈ good, wi i ℓ) ≤ M ^ (C + K + 5) := by
    let residue := good.filter fun ℓ => ℓ - 1 ∣ 2 * i
    let generic := good.filter fun ℓ => ¬ℓ - 1 ∣ 2 * i
    have hrinfo (ℓ : ℕ) (hℓ : ℓ ∈ residue) :
        (ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∉ bad) ∧ ℓ - 1 ∣ 2 * i :=
      ⟨hgood ℓ (Finset.mem_filter.mp hℓ).1, (Finset.mem_filter.mp hℓ).2⟩
    have hbnd (ℓ : ℕ) (hℓ : ℓ ∈ residue) : ℓ ≤ 2 * t :=
      selmerPlus_residuePrime_le (hrinfo ℓ hℓ).1.1 hi (hrinfo ℓ hℓ).2
    have hcard : (residue.card : ℝ) ≤ 2 * (t : ℝ) := by
      have hs : residue ⊆ Finset.Icc 1 (2 * t) := fun ℓ hℓ =>
        Finset.mem_Icc.mpr ⟨(hrinfo ℓ hℓ).1.1.one_lt.le, hbnd ℓ hℓ⟩
      have h := Finset.card_le_card hs
      rw [Nat.card_Icc] at h
      exact_mod_cast (show residue.card ≤ 2 * t by omega)
    have hr : (∑ ℓ ∈ residue, wi i ℓ) ≤ M ^ (K + 4) := by
      calc
        _ ≤ ∑ _ℓ ∈ residue, 2 * M * M ^ K := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          obtain ⟨⟨hp', hodd, hbad⟩, hdiv⟩ := hrinfo ℓ hℓ
          have hlog : Real.log ℓ ≤ 2 * M := by
            have hl : (ℓ : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hbnd ℓ hℓ
            have hpos : (0 : ℝ) < ℓ := by exact_mod_cast hp'.pos
            linarith [Real.log_le_sub_one_of_pos hpos]
          exact mul_le_mul hlog (hresidue i hi ℓ hp' hodd hbad hdiv)
            (Nat.cast_nonneg _) (by positivity)
        _ = (residue.card : ℝ) * (2 * M * M ^ K) := by simp
        _ ≤ (2 * M) * (2 * M * M ^ K) :=
          mul_le_mul_of_nonneg_right (hcard.trans (by linarith)) (by positivity)
        _ ≤ _ := by
          rw [show (2 * M) * (2 * M * M ^ K) = M ^ K * (4 * M ^ 2) by ring, pow_add]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [show M ^ 4 = M ^ 2 * M ^ 2 by ring]
          exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    have hg : (∑ ℓ ∈ generic, wi i ℓ) ≤ M ^ C :=
      hgeneric i hi generic fun ℓ hℓ =>
        let ⟨hp', hodd, hbad⟩ := hgood ℓ (Finset.mem_filter.mp hℓ).1
        ⟨hp', hodd, hbad, (Finset.mem_filter.mp hℓ).2⟩
    rw [← Finset.sum_filter_add_sum_filter_not good (fun ℓ => ℓ - 1 ∣ 2 * i)]
    calc
      _ ≤ M ^ (K + 4) + M ^ C := add_le_add hr hg
      _ ≤ M ^ (C + K + 4) + M ^ (C + K + 4) :=
        add_le_add (pow_le_pow_right₀ hM₁ (by omega)) (pow_le_pow_right₀ hM₁ (by omega))
      _ ≤ _ := by
        rw [show C + K + 5 = (C + K + 4) + 1 by omega, pow_succ M (C + K + 4)]
        calc
          _ = M ^ (C + K + 4) * 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hM (pow_nonneg hM₀ _)
  have hg : (∑ ℓ ∈ good, w ℓ) ≤ M ^ (C + K + 6) := by
    dsimp only [w, selmerWeightedLength, selmerTwistLength]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i ∈ Finset.Ico 1 t, M ^ (C + K + 5) := Finset.sum_le_sum htwist
      _ = ((Finset.Ico 1 t).card : ℝ) * M ^ (C + K + 5) := by simp
      _ ≤ M * M ^ (C + K + 5) := by
        have hc : ((Finset.Ico 1 t).card : ℝ) ≤ (t : ℝ) := by
          rw [Nat.card_Ico]
          exact_mod_cast Nat.sub_le t 1
        exact mul_le_mul_of_nonneg_right (hc.trans ht) (by positivity)
      _ = _ := by
        rw [show C + K + 6 = (C + K + 5) + 1 by omega, pow_succ M (C + K + 5), mul_comm]
  rw [← Finset.sum_filter_add_sum_filter_not primes (fun ℓ => ℓ ∉ bad)]
  refine add_le_add hg ((Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ℓ _ _ => hw ℓ)).trans hbudget)
  intro ℓ hℓ
  exact not_not.mp (Finset.mem_filter.mp hℓ).2

end Riemann
