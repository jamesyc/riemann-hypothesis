module

public import Utilities.FiniteMeanSquare
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Squarefree

@[expose] public section

open Utilities
open scoped BigOperators Classical ComplexConjugate

namespace Riemann

/-- The Legendre symbol with a finite-index prime argument. Values at
nonprimes are unused in the auxiliary-prime search pools. -/
noncomputable def auxiliaryLegendre (q n : ℕ) : ℂ :=
  if h : q.Prime then
    letI : Fact q.Prime := ⟨h⟩
    (legendreSym q n : ℂ)
  else 0

@[simp] theorem auxiliaryLegendre_of_prime {q : ℕ} (hq : q.Prime) (n : ℕ) :
    letI : Fact q.Prime := ⟨hq⟩
    auxiliaryLegendre q n = (legendreSym q n : ℂ) := by
  let _ : Fact q.Prime := ⟨hq⟩
  simp [auxiliaryLegendre, hq]

private theorem conj_auxiliaryLegendre (q n : ℕ) :
    conj (auxiliaryLegendre q n) = auxiliaryLegendre q n := by
  by_cases hq : q.Prime <;> simp [auxiliaryLegendre, hq]

private theorem norm_auxiliaryLegendre_le_one (q n : ℕ) :
    ‖auxiliaryLegendre q n‖ ≤ 1 := by
  by_cases hq : q.Prime
  · let _ : Fact q.Prime := ⟨hq⟩
    rw [auxiliaryLegendre_of_prime hq]
    by_cases hn : ((n : ℤ) : ZMod q) = 0
    · rw [(legendreSym.eq_zero_iff q _).mpr hn, Int.cast_zero, norm_zero]
      exact zero_le_one
    · rcases legendreSym.eq_one_or_neg_one q hn with hn' | hn' <;> rw [hn'] <;> simp
  · simp [auxiliaryLegendre, hq]

private theorem auxiliaryLegendre_mul (q n m : ℕ) :
    auxiliaryLegendre q (n * m) = auxiliaryLegendre q n * auxiliaryLegendre q m := by
  by_cases hq : q.Prime
  · let _ : Fact q.Prime := ⟨hq⟩
    simp only [auxiliaryLegendre_of_prime hq, Nat.cast_mul, legendreSym.mul, Int.cast_mul]
  · simp [auxiliaryLegendre, hq]

private theorem auxiliaryLegendre_sq {q n : ℕ} (hq : q.Prime) (hn : ¬ q ∣ n) :
    auxiliaryLegendre q (n ^ (2 : ℕ)) = 1 := by
  let _ : Fact q.Prime := ⟨hq⟩
  rw [auxiliaryLegendre_of_prime hq, Nat.cast_pow]
  have hn' : ((n : ℤ) : ZMod q) ≠ 0 := by
    simpa only [Int.cast_natCast] using (ZMod.natCast_eq_zero_iff n q).not.mpr hn
  rw [legendreSym.sq_one' q hn', Int.cast_one]

/-- The two types of correlation exceptions in Proposition 5.4. -/
def IsExceptionalLegendreProduct (bad : Finset ℕ) (n m : ℕ) : Prop :=
  IsSquare (n * m) ∨ ∃ s ∈ bad, ∃ r : ℕ, r ^ (2 : ℕ) * s = n * m

/-- Proposition 5.4 with an indicator for the square and exceptional
squarefree products. Each remaining covariance is bounded by the symbol
correlation for its squarefree part. -/
theorem auxiliaryLegendre_meanSquare_le {Z : ℕ} (primes bad : Finset ℕ) (η : ℝ)
    (hprime : ∀ q ∈ primes, q.Prime ∧ Z < q)
    (hcorr : ∀ s : ℕ, Squarefree s → 1 < s → s ≤ Z ^ (2 : ℕ) → s ∉ bad →
      ‖∑ q ∈ primes, auxiliaryLegendre q s‖ ≤ η * primes.card)
    (c : ℕ → ℂ) :
    (∑ q ∈ primes, ‖∑ n ∈ Finset.Icc 1 Z, c n * auxiliaryLegendre q n‖ ^ (2 : ℕ)) ≤
      ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z, ‖c n‖ * ‖c m‖ *
        (if IsExceptionalLegendreProduct bad n m then (primes.card : ℝ) else η * primes.card) := by
  classical
  apply sum_norm_sum_mul_sq_le_covariance
  intro n hn m hm
  simp only [conj_auxiliaryLegendre, ← auxiliaryLegendre_mul]
  by_cases hb : IsExceptionalLegendreProduct bad n m
  · rw [ite_eq_left hb]
    calc
      _ ≤ ∑ q ∈ primes, ‖auxiliaryLegendre q (n * m)‖ := norm_sum_le _ _
      _ ≤ ∑ _q ∈ primes, (1 : ℝ) := Finset.sum_le_sum fun q _ => norm_auxiliaryLegendre_le_one q _
      _ = _ := by simp
  rw [ite_eq_right hb]
  obtain ⟨hn₀, hnZ⟩ := Finset.mem_Icc.mp hn
  obtain ⟨hm₀, hmZ⟩ := Finset.mem_Icc.mp hm
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by omega
  have hnm : 0 < n * m := Nat.mul_pos hnpos hmpos
  obtain ⟨s, r, hs, hr, hprod, hfree⟩ := Nat.sq_mul_squarefree_of_pos hnm
  have hs₁ : 1 < s := by
    by_contra! h
    have hs1 : s = 1 := by omega
    apply hb
    exact Or.inl ⟨r, by simpa only [hs1, mul_one, pow_two] using hprod.symm⟩
  have hsZ : s ≤ Z ^ (2 : ℕ) := by
    have hsdvd : s ∣ n * m := ⟨r ^ (2 : ℕ), by rw [← hprod, mul_comm]⟩
    exact (Nat.le_of_dvd hnm hsdvd).trans (by simpa only [pow_two] using Nat.mul_le_mul hnZ hmZ)
  have hsb : s ∉ bad := fun h => hb (Or.inr ⟨s, h, r, hprod⟩)
  have hreduce : (∑ q ∈ primes, auxiliaryLegendre q (n * m)) =
      ∑ q ∈ primes, auxiliaryLegendre q s := by
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hp, hqZ⟩ := hprime q hq
    have hqnm : ¬ q ∣ n * m := fun h => (hp.dvd_mul.mp h).elim
      (fun hd => (not_le_of_gt hqZ) ((Nat.le_of_dvd hnpos hd).trans hnZ))
      (fun hd => (not_le_of_gt hqZ) ((Nat.le_of_dvd hmpos hd).trans hmZ))
    have hqr : ¬ q ∣ r := by
      intro h
      apply hqnm
      rw [← hprod]
      exact (h.trans (dvd_pow_self _ (by decide))).trans (dvd_mul_right _ _)
    rw [← hprod, auxiliaryLegendre_mul, auxiliaryLegendre_sq hp hqr, one_mul]
  rw [hreduce]
  exact hcorr s hfree hs₁ hsZ hsb

/-- The exceptional-pair and total-mass form of the auxiliary-prime
second moment bound. -/
theorem auxiliaryLegendre_meanSquare_le_of_masses {Z : ℕ} (primes bad : Finset ℕ)
    {η E B : ℝ} (hη : 0 ≤ η)
    (hprime : ∀ q ∈ primes, q.Prime ∧ Z < q)
    (hcorr : ∀ s : ℕ, Squarefree s → 1 < s → s ≤ Z ^ (2 : ℕ) → s ∉ bad →
      ‖∑ q ∈ primes, auxiliaryLegendre q s‖ ≤ η * primes.card)
    (c : ℕ → ℂ)
    (hE : (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
      if IsExceptionalLegendreProduct bad n m then ‖c n‖ * ‖c m‖ else 0) ≤ E)
    (hL₁ : (∑ n ∈ Finset.Icc 1 Z, ‖c n‖) ≤ B) :
    (∑ q ∈ primes, ‖∑ n ∈ Finset.Icc 1 Z, c n * auxiliaryLegendre q n‖ ^ (2 : ℕ)) ≤
      (primes.card : ℝ) * (E + η * B ^ (2 : ℕ)) := by
  classical
  let I := Finset.Icc 1 Z
  let P : ℝ := primes.card
  let w (n m : ℕ) := ‖c n‖ * ‖c m‖
  let e (n m : ℕ) := if IsExceptionalLegendreProduct bad n m then w n m else 0
  refine (auxiliaryLegendre_meanSquare_le primes bad η hprime hcorr c).trans ?_
  have hterm (n m : ℕ) :
      w n m * (if IsExceptionalLegendreProduct bad n m then P else η * P) ≤
        P * e n m + (P * η) * w n m := by
    by_cases h : IsExceptionalLegendreProduct bad n m
    · simp only [e, ite_eq_left h]
      have hpos : 0 ≤ (P * η) * w n m := by dsimp [P, w]; positivity
      linarith [mul_comm (w n m) P]
    · simp only [e, ite_eq_right h, mul_zero, zero_add]
      exact le_of_eq (by ring)
  have hw :
      (∑ n ∈ I, ∑ m ∈ I, w n m) = (∑ n ∈ I, ‖c n‖) ^ (2 : ℕ) := by
    rw [pow_two, Finset.sum_mul]
    simp only [w, Finset.mul_sum]
  have hpow : (∑ n ∈ I, ‖c n‖) ^ (2 : ℕ) ≤ B ^ (2 : ℕ) :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hL₁ _
  calc
    _ ≤ ∑ n ∈ I, ∑ m ∈ I, (P * e n m + (P * η) * w n m) :=
      Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => hterm n m
    _ = P * (∑ n ∈ I, ∑ m ∈ I, e n m) + (P * η) * (∑ n ∈ I, ∑ m ∈ I, w n m) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ P * E + (P * η) * B ^ (2 : ℕ) := by
      rw [hw]
      exact add_le_add (mul_le_mul_of_nonneg_left hE (by dsimp [P]; positivity))
        (mul_le_mul_of_nonneg_left hpow (by dsimp [P]; positivity))
    _ = _ := by ring

end Riemann
