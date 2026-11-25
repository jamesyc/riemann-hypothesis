module

public import Utilities.HigherStickelberger
public import Utilities.FiniteAlgebraAnnihilator
import Utilities.GroupAlgebraNorm

@[expose] public section

namespace Utilities

/-- The standard completed character bound grows at most logarithmically
in the level, with a linear factor in the Bernoulli index. -/
theorem log_higherStickelbergerHeight_le {N k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) :
    Real.log (2 * (1 + ((2 * N + 1 : ℕ) : ℝ) ^ k) * generalizedBernoulliHeightBound N k) ≤
      8 * (k : ℝ) * Real.log ((k : ℝ) * N) := by
  let T : ℝ := (k : ℝ) * N
  let a : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hTN : (N : ℝ) ≤ T := le_mul_of_one_le_left (by positivity) (by linarith)
  have hTk : (k : ℝ) ≤ T := le_mul_of_one_le_right (by positivity) (by linarith)
  have hT : 4 ≤ T := by dsimp [T]; nlinarith
  have hT₁ : 1 ≤ T := by linarith
  have h16 : (16 : ℝ) ≤ T ^ k := by
    calc
      _ ≤ T ^ (2 : ℕ) := by nlinarith [sq_nonneg (T - 4)]
      _ ≤ _ := pow_le_pow_right₀ hT₁ hk
  have ha : a ≤ T ^ (2 : ℕ) := by
    dsimp [a]
    push_cast
    have hNT := mul_le_mul_of_nonneg_left hTN (show 0 ≤ T by linarith)
    have h4N := mul_le_mul_of_nonneg_right hT (show (0 : ℝ) ≤ N by positivity)
    nlinarith
  have ha₁ : 1 ≤ a := by dsimp [a]; push_cast; linarith
  have h2 : (2 : ℝ) ≤ T ^ k := (by norm_num : (2 : ℝ) ≤ 16).trans h16
  have hsmooth : 1 + a ^ k ≤ T ^ (3 * k) := by
    calc
      _ ≤ 2 * a ^ k := by linarith [one_le_pow₀ ha₁ (n := k)]
      _ ≤ T ^ k * (T ^ (2 : ℕ)) ^ k :=
        mul_le_mul h2 (pow_le_pow_left₀ (by linarith) ha _) (by positivity) (by positivity)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hNpow : (N : ℝ) ^ (k + 1) ≤ T ^ (2 * k) :=
    (pow_le_pow_left₀ (by positivity) hTN _).trans (pow_le_pow_right₀ hT₁ (by omega))
  have hfact : (k.factorial : ℝ) ≤ T ^ k :=
    (show (k.factorial : ℝ) ≤ (k : ℝ) ^ k by exact_mod_cast k.factorial_le_pow).trans
      (pow_le_pow_left₀ (by positivity) hTk _)
  have hprod : 2 * (1 + a ^ k) * generalizedBernoulliHeightBound N k ≤ T ^ (8 * k) := by
    unfold generalizedBernoulliHeightBound
    calc
      _ ≤ T ^ k * T ^ (3 * k) * (T ^ k * T ^ (2 * k) * T ^ k) := by gcongr
      _ = _ := by simp only [← pow_add]; congr 1; omega
  have hpos : 0 < 2 * (1 + a ^ k) * generalizedBernoulliHeightBound N k := by
    have : (0 : ℝ) < N := by linarith
    unfold generalizedBernoulliHeightBound
    positivity
  have hlog := Real.log_le_log hpos hprod
  rw [Real.log_pow, Nat.cast_mul] at hlog
  exact hlog

/-- The parity-completed integral Stickelberger element has nonzero norm and
a uniform bound on its logarithm. -/
theorem intNorm_parityHigherStickelberger_bound {N : ℕ} [NeZero N] {G : Type*}
    [CommGroup G] [Fintype G] (π : (ZMod N)ˣ →* G) {k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k)
    (ha : (2 * N + 1).Coprime N) :
    let z := groupAlgebraParityCompletion (π (-1)) ((-1 : ℤ) ^ k)
      (integralHigherStickelberger π k (2 * N + 1) ha)
    Algebra.norm ℤ z ≠ 0 ∧
      Real.log ((Algebra.norm ℤ z).natAbs : ℝ) ≤ (Fintype.card G : ℝ) * (8 * (k : ℝ) * Real.log ((k : ℝ) * N)) := by
  dsimp only
  let a := 2 * N + 1
  let s := integralHigherStickelberger π k a ha
  let c := π (-1)
  let ε := (-1 : ℤ) ^ k
  let B := (1 + (a : ℝ) ^ k) * generalizedBernoulliHeightBound N k
  have hB : 1 ≤ B := by
    dsimp only [B, generalizedBernoulliHeightBound]
    have hNpow : 1 ≤ (N : ℝ) ^ (k + 1) := one_le_pow₀ (by exact_mod_cast (show 1 ≤ N by omega))
    have hfact : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
    apply one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (pow_nonneg (by positivity) _))
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hNpow) hfact
  have hc : c * c = 1 := by dsimp only [c]; rw [← map_mul]; simp
  have he : ε * ε = 1 := by dsimp only [ε]; rw [← mul_pow]; norm_num
  have hval (χ : AddChar (Additive G) ℂ) :
      let y := groupAlgebraCharacterEval G (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ)
        (groupAlgebraParityCompletion c ε s)) χ
      y ≠ 0 ∧ ‖y‖ ≤ 2 * B := by
    dsimp only
    let η : G →* ℂ := AddChar.toMonoidHomEquiv χ
    have hcast : groupAlgebraCharacterEval G (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ)
        (groupAlgebraParityCompletion c ε s)) χ =
      MonoidAlgebra.lift ℤ ℂ G η (groupAlgebraParityCompletion c ε s) := lift_complex_map_int G η _
    rw [hcast]
    classical
    rw [lift_groupAlgebraParityCompletion_eq_ite η c hc ε he]
    split_ifs with hχ
    · have hp : η (π (-1)) = (-1 : ℂ) ^ k := by
        simpa [c, ε] using hχ
      refine ⟨mul_ne_zero (by norm_num) (lift_integralHigherStickelberger_ne_zero (by omega) π η ha hk (by omega) hp), ?_⟩
      rw [norm_mul, Complex.norm_two]
      exact mul_le_mul_of_nonneg_left (norm_lift_integralHigherStickelberger_le (by omega) π η ha hk) (by norm_num)
    · rw [Complex.norm_two]
      exact ⟨by norm_num, by linarith⟩
  obtain ⟨hne, hlog⟩ := intNorm_groupAlgebra_ne_zero_log_le G (groupAlgebraParityCompletion c ε s) (2 * B) hval
  refine ⟨hne, hlog.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))⟩
  simpa only [B, a, mul_assoc] using log_higherStickelbergerHeight_le hN hk

end Utilities
