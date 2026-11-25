module

public import Riemann.ExcessBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter

namespace Riemann

/-- The step and horizontal-rank intervals of Proposition 5.15(i). -/
structure ChainRankBounds (x ε : ℝ) (m k : ℕ) : Prop where
  steps_even : Even m
  rank_even : Even k
  steps_lower : x ^ (1 / 2 - ε / 16) ≤ (m : ℝ)
  steps_upper : (m : ℝ) ≤ 2 * x ^ (1 / 2 - ε / 16)
  rank_lower : x ^ (9 / 2 + 10 * ε) ≤ (k : ℝ)
  rank_upper : (k : ℝ) ≤ 2 * x ^ (9 / 2 + 10 * ε)

private theorem exists_even_nat_between {y : ℝ} (hy : 2 ≤ y) :
    ∃ n : ℕ, Even n ∧ y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * y := by
  refine ⟨2 * ⌈y / 2⌉₊, even_two.mul_right _, ?_, ?_⟩
  · push_cast
    linarith [Nat.le_ceil (y / 2)]
  · push_cast
    linarith [Nat.ceil_lt_add_one (show 0 ≤ y / 2 by linarith)]

theorem eventually_exists_chainRankBounds {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∃ m k : ℕ, ChainRankBounds x ε m k := by
  have hm : 0 < 1 / 2 - ε / 16 := by linarith
  have hk : 0 < 9 / 2 + 10 * ε := by linarith
  filter_upwards [(tendsto_rpow_atTop hm).eventually_ge_atTop 2,
    (tendsto_rpow_atTop hk).eventually_ge_atTop 2] with x hxm hxk
  obtain ⟨m, hem, hm₀, hm₁⟩ := exists_even_nat_between hxm
  obtain ⟨k, hek, hk₀, hk₁⟩ := exists_even_nat_between hxk
  exact ⟨m, k, hem, hek, hm₀, hm₁, hk₀, hk₁⟩

/-- The inequalities of Proposition 5.15(ii) that concern the selected ranks. -/
theorem eventually_chainRank_sizeBounds {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∀ {n m k : ℕ}, x ^ (2 + 8 * ε) ≤ (n : ℝ) →
      (n : ℝ) ≤ 2 * x ^ (2 + 8 * ε) → ChainRankBounds x ε m k →
      2 ≤ m ∧ m + 3 ≤ k ∧ m ≤ 2 * n ∧ 2 * n ≤ k ∧
      x ^ (1 / 2 - ε) ≤ (m : ℝ) ∧ (m : ℝ) ≤ x ^ (1 / 2 + ε / 2) ∧
      x * m ≤ (k : ℝ) ∧ (k : ℝ) ≤ (n : ℝ) ^ 2 * x ^ (1 / 2 - ε) := by
  have hm : 0 < 1 / 2 - ε / 16 := by linarith
  have hslack : 0 < 9 * ε / 16 := by positivity
  filter_upwards [eventually_ge_atTop (3 : ℝ), (tendsto_rpow_atTop hm).eventually_ge_atTop 2,
    (tendsto_rpow_atTop hslack).eventually_ge_atTop 2,
    (tendsto_rpow_atTop (show 0 < 5 * ε by positivity)).eventually_ge_atTop 2]
    with x hx hm₀ hm₁ hk₁ n m k hn hn' hmk
  have hx₁ : 1 ≤ x := by linarith
  have hx' : 0 < x := by positivity
  have hm₂ : (2 : ℝ) ≤ (m : ℝ) := hm₀.trans hmk.steps_lower
  have hm_x : (m : ℝ) ≤ 2 * x := hmk.steps_upper.trans (by
    gcongr
    simpa using Real.rpow_le_rpow_of_exponent_le hx₁ (show 1 / 2 - ε / 16 ≤ (1 : ℝ) by linarith))
  have hn_x : x ≤ (n : ℝ) := (show x ≤ x ^ (2 + 8 * ε) by
    simpa using Real.rpow_le_rpow_of_exponent_le hx₁ (show (1 : ℝ) ≤ 2 + 8 * ε by linarith)).trans hn
  have hk_x : x ^ (3 : ℕ) ≤ (k : ℝ) := (show x ^ (3 : ℕ) ≤ x ^ (9 / 2 + 10 * ε) by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx₁ (by push_cast; linarith)).trans
      hmk.rank_lower
  have hmul : x * m ≤ (k : ℝ) := by
    refine (mul_le_mul_of_nonneg_left hm_x hx'.le).trans (?_ : x * (2 * x) ≤ x ^ (3 : ℕ)) |>.trans hk_x
    nlinarith [mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ x by linarith) (sq_nonneg x)]
  have hmk' : (m : ℝ) + 3 ≤ (k : ℝ) := by
    have haux : (m : ℝ) + 3 ≤ x * m := by
      nlinarith [mul_le_mul_of_nonneg_right hx (show (0 : ℝ) ≤ m by positivity)]
    exact haux.trans hmul
  have hnk : 2 * (n : ℝ) ≤ (k : ℝ) := by
    calc
      _ ≤ 4 * x ^ (2 + 8 * ε) := by linarith
      _ ≤ x ^ (2 : ℝ) * x ^ (2 + 8 * ε) := by
        gcongr
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        nlinarith
      _ ≤ x ^ (9 / 2 + 10 * ε) := by
        rw [← Real.rpow_add hx']
        exact Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)
      _ ≤ _ := hmk.rank_lower
  refine ⟨by exact_mod_cast hm₂, by exact_mod_cast hmk',
    by exact_mod_cast hm_x.trans (mul_le_mul_of_nonneg_left hn_x (by norm_num)), by exact_mod_cast hnk, ?_, ?_, hmul, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)).trans hmk.steps_lower
  · calc
      _ ≤ 2 * x ^ (1 / 2 - ε / 16) := hmk.steps_upper
      _ ≤ x ^ (9 * ε / 16) * x ^ (1 / 2 - ε / 16) := by gcongr
      _ = _ := by rw [← Real.rpow_add hx']; congr 1; ring
  · calc
      _ ≤ 2 * x ^ (9 / 2 + 10 * ε) := hmk.rank_upper
      _ ≤ x ^ (5 * ε) * x ^ (9 / 2 + 10 * ε) := by gcongr
      _ = (x ^ (2 + 8 * ε)) ^ (2 : ℕ) * x ^ (1 / 2 - ε) := by
        rw [← Real.rpow_mul_natCast hx'.le, ← Real.rpow_add hx', ← Real.rpow_add hx']
        congr 1
        push_cast
        ring
      _ ≤ _ := by gcongr

/-- Supply the averaging budget of Proposition 5.15(ii) once the top and
thick sets have been chosen. Both selected ranks retain their sharper bounds. -/
theorem eventually_exists_chainExcessBudget {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∀ (n NT N₂ : ℕ) (b : ℝ),
      x ^ (2 + 8 * ε) ≤ (n : ℝ) → (n : ℝ) ≤ 2 * x ^ (2 + 8 * ε) →
      (1 / 2 : ℝ) * x ^ (-ε / 8) * n ≤ NT →
      x ^ (-ε) * n ≤ N₂ → N₂ ≤ n → 0 < b →
      ∃ m k : ℕ, ChainRankBounds x ε m k ∧
        ExcessSizeBounds ⟨n, NT, N₂, m, x * b, b, (k : ℝ)⟩ x ε := by
  have hslack : 0 < 3 * ε / 8 := by positivity
  filter_upwards [eventually_ge_atTop (3 : ℝ), eventually_exists_chainRankBounds hε hsmall,
    eventually_chainRank_sizeBounds hε hsmall, (tendsto_rpow_atTop hslack).eventually_ge_atTop 26]
    with x hx hselect hsize hthreshold n NT N₂ b hn hn₁ htop hthick hN₂ hb
  obtain ⟨m, k, hmk⟩ := hselect
  obtain ⟨hm, _, _, _, hm₀, hm₁, hk₀, hk₁⟩ := hsize hn hn₁ hmk
  have hx' : 0 < x := by positivity
  have hn' : (0 : ℝ) < n := (Real.rpow_pos_of_pos hx' _).trans_le hn
  have htop' : (0 : ℝ) < NT := (by positivity : 0 < (1 / 2 : ℝ) * x ^ (-ε / 8) * n).trans_le htop
  have hthick' : (0 : ℝ) < N₂ := (by positivity : 0 < x ^ (-ε) * n).trans_le hthick
  have hk' : (0 : ℝ) < k := (Real.rpow_pos_of_pos hx' _).trans_le hmk.rank_lower
  exact ⟨m, k, hmk, hx, hε, by exact_mod_cast hn', by exact_mod_cast htop',
    by exact_mod_cast hthick', (show 0 < m by omega), by positivity, hb, hk', by nlinarith,
    htop, hthick, hN₂, hm₀, hm₁, hk₀, hk₁, hthreshold⟩

/-- The auxiliary dimension (t_r) in Proposition 5.15(i). -/
structure ChainTwistRankBounds (x ε : ℝ) (n m k tr : ℕ) : Prop where
  rank_odd : Odd tr
  rank_eq :
    let r := k + m - 1
    let f := 2 * n
    let nW := 8 * ⌈(10 * (r : ℝ) / 8) *
      ((f : ℝ) + (f : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * (x ^ ε) ^ (2 : ℕ) / m)⌉₊
    r + tr = 8 * f * r + 4 + ⌈x ^ (377 : ℕ)⌉₊ * nW
  chain_lower : k + m + 4 ≤ tr
  steps_lower : 3 * m < tr
  stable_range : m ^ 2 ≤ k + m * (tr + 1)
  rank_upper : (tr : ℝ) ≤ x ^ (400 : ℕ) - 1
  cutoff : tr ≤ ⌊x ^ (400 : ℕ)⌋₊

/-- The chain auxiliary dimension lies below the Selmer cutoff of Lemma 18.2. -/
theorem eventually_exists_chainTwistRank {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∀ {n m k : ℕ}, x ^ (2 + 8 * ε) ≤ (n : ℝ) →
      (n : ℝ) ≤ 2 * x ^ (2 + 8 * ε) → ChainRankBounds x ε m k →
      ∃ tr : ℕ, ChainTwistRankBounds x ε n m k tr := by
  have hεgap : 0 < (1 / 4 : ℝ) := by norm_num
  filter_upwards [eventually_ge_atTop (3 : ℝ), eventually_chainRank_sizeBounds hε hsmall,
    (tendsto_rpow_atTop hεgap).eventually_ge_atTop 12000] with x hx hsize hlarge n m k hn₀ hn₁ hmk
  let r := k + m - 1
  let f := 2 * n
  let q := (10 * (r : ℝ) / 8) *
    ((f : ℝ) + (f : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * (x ^ ε) ^ (2 : ℕ) / m)
  let nW := 8 * ⌈q⌉₊
  let T := ⌈x ^ (377 : ℕ)⌉₊
  let S := 8 * f * r + 4 + T * nW
  obtain ⟨hm, hmk₀, hmn, _, _, _, _, _⟩ := hsize hn₀ hn₁ hmk
  have hf₀ : 1 ≤ f := by dsimp [f]; omega
  have hr₀ : m ≤ r := by dsimp [r]; omega
  have hr₁ : r ≤ 2 * k := by dsimp [r]; omega
  have hr₂ : k + m ≤ r + 1 := by dsimp [r]; omega
  have hS : 8 * r + 4 ≤ S := by
    have := Nat.mul_le_mul_right r (Nat.mul_le_mul_left 8 hf₀)
    dsimp [S]
    omega
  have htr : r + (S - r) = S := Nat.add_sub_of_le (by omega)
  have hrOdd : Odd r := by
    obtain ⟨a, ha⟩ := hmk.rank_even
    obtain ⟨b, hb⟩ := hmk.steps_even
    refine ⟨a + b - 1, ?_⟩
    dsimp [r]
    omega
  have hSEven : Even S := by
    dsimp [S, nW]
    rw [show 8 * f * r = 2 * (4 * f * r) by ring, show 8 * ⌈q⌉₊ = 2 * (4 * ⌈q⌉₊) by ring]
    exact ((even_two.mul_right _).add (by decide : Even (4 : ℕ))).add ((even_two.mul_right _).mul_left T)
  have htrOdd : Odd (S - r) := by
    obtain ⟨s, hs⟩ := hSEven
    obtain ⟨t, ht⟩ := hrOdd
    refine ⟨s - t - 1, ?_⟩
    omega
  have hstable : m ^ 2 ≤ k + m * (S - r + 1) := by
    have hmtr : m ≤ S - r + 1 := by omega
    nlinarith [Nat.mul_le_mul_left m hmtr]
  have hx₁ : 1 ≤ x := by linarith
  have hx' : 0 < x := by positivity
  have hk' : (k : ℝ) ≤ 2 * x ^ (47 / 10 : ℝ) := hmk.rank_upper.trans (by
    gcongr
    linarith)
  have hf' : (f : ℝ) ≤ 4 * x ^ (54 / 25 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx₁ (show 2 + 8 * ε ≤ (54 / 25 : ℝ) by linarith)
    dsimp [f]
    push_cast
    linarith
  have hr' : (r : ℝ) ≤ 4 * x ^ (47 / 10 : ℝ) := by
    have h : (r : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hr₁
    linarith
  have hm' : x ^ (49 / 100 : ℝ) ≤ (m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)).trans hmk.steps_lower
  have hy : x ^ ε ≤ x ^ (1 / 50 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)
  have hpol : (f : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * (x ^ ε) ^ (2 : ℕ) / (m : ℝ) ≤
      128 * x ^ (18 : ℝ) := by
    have hnum : (f : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * (x ^ ε) ^ (2 : ℕ) ≤
        128 * x ^ (1849 / 100 : ℝ) := by
      calc
        _ ≤ (4 * x ^ (54 / 25 : ℝ)) ^ (2 : ℕ) *
            (2 * x ^ (47 / 10 : ℝ)) ^ (3 : ℕ) * (x ^ (1 / 50 : ℝ)) ^ (2 : ℕ) := by
          have hk₀ : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
          have hk₁ : (k : ℝ) - 1 ≤ 2 * x ^ (47 / 10 : ℝ) := by linarith
          gcongr
        _ = 128 * x ^ (923 / 50 : ℝ) := by
          rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hx'.le, ← Real.rpow_mul_natCast hx'.le,
            ← Real.rpow_mul_natCast hx'.le]
          have hp₁ := (Real.rpow_add hx' ((54 / 25 : ℝ) * (2 : ℕ)) ((47 / 10 : ℝ) * (3 : ℕ))).symm
          have hp₂ := (Real.rpow_add hx' (((54 / 25 : ℝ) * (2 : ℕ)) + (47 / 10 : ℝ) * (3 : ℕ))
            ((1 / 50 : ℝ) * (2 : ℕ))).symm
          calc
            _ = 128 * ((x ^ ((54 / 25 : ℝ) * (2 : ℕ)) * x ^ ((47 / 10 : ℝ) * (3 : ℕ))) *
                x ^ ((1 / 50 : ℝ) * (2 : ℕ))) := by ring
            _ = _ := by rw [hp₁, hp₂]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)) (by norm_num)
    apply (div_le_iff₀ (show (0 : ℝ) < m by exact_mod_cast (show 0 < m by omega))).mpr
    refine hnum.trans ?_
    calc
      _ = 128 * x ^ (18 : ℝ) * x ^ (49 / 100 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hx']; norm_num
      _ ≤ _ := by gcongr
  have hW : (nW : ℝ) ≤ 5288 * x ^ (91 / 4 : ℝ) := by
    have hq₀ : 0 ≤ q := by
      dsimp [q]
      have hk₀ : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      positivity
    have hq₁ : q ≤ 660 * x ^ (91 / 4 : ℝ) := by
      have hf'' : (f : ℝ) ≤ 4 * x ^ (18 : ℝ) := hf'.trans (by gcongr; norm_num)
      have hr'' : 10 * (r : ℝ) / 8 ≤ 5 * x ^ (47 / 10 : ℝ) := by linarith
      dsimp [q]
      calc
        _ ≤ (5 * x ^ (47 / 10 : ℝ)) * (132 * x ^ (18 : ℝ)) := by
          have hk₀ : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
          have hk₁ : 0 ≤ (k : ℝ) - 1 := sub_nonneg.mpr hk₀
          exact mul_le_mul hr'' (by linarith) (by positivity) (by positivity)
        _ ≤ _ := by
          calc
            _ = 660 * x ^ (227 / 10 : ℝ) := by
              rw [show (5 : ℝ) * x ^ (47 / 10 : ℝ) * (132 * x ^ (18 : ℝ)) =
                660 * (x ^ (47 / 10 : ℝ) * x ^ (18 : ℝ)) by ring, ← Real.rpow_add hx']
              norm_num
            _ ≤ _ := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)) (by norm_num)
    have hX := Real.one_le_rpow hx₁ (by norm_num : 0 ≤ (91 / 4 : ℝ))
    change ((8 * ⌈q⌉₊ : ℕ) : ℝ) ≤ _
    push_cast
    linarith [Nat.ceil_lt_add_one hq₀]
  have hT : (T : ℝ) ≤ 2 * x ^ (377 : ℕ) := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ x ^ (377 : ℕ) by positivity)
    have hpow : 1 ≤ x ^ (377 : ℕ) := one_le_pow₀ hx₁
    dsimp [T]
    linarith
  have hprod : (T : ℝ) * nW ≤ 10576 * x ^ (1599 / 4 : ℝ) := by
    calc
      _ ≤ (2 * x ^ (377 : ℕ)) * (5288 * x ^ (91 / 4 : ℝ)) := by gcongr
      _ = _ := by
        rw [← Real.rpow_natCast x 377, show (2 : ℝ) * x ^ ((377 : ℕ) : ℝ) *
          (5288 * x ^ (91 / 4 : ℝ)) = 10576 *
          (x ^ ((377 : ℕ) : ℝ) * x ^ (91 / 4 : ℝ)) by ring, ← Real.rpow_add hx']
        norm_num
  have hfr : 8 * (f : ℝ) * r ≤ 128 * x ^ (1599 / 4 : ℝ) := by
    calc
      _ ≤ 8 * (4 * x ^ (54 / 25 : ℝ)) * (4 * x ^ (47 / 10 : ℝ)) := by gcongr
      _ = 128 * x ^ (343 / 50 : ℝ) := by
        rw [show (8 : ℝ) * (4 * x ^ (54 / 25 : ℝ)) * (4 * x ^ (47 / 10 : ℝ)) =
          128 * (x ^ (54 / 25 : ℝ) * x ^ (47 / 10 : ℝ)) by ring, ← Real.rpow_add hx']
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)) (by norm_num)
  have hupper : (S : ℝ) ≤ 10708 * x ^ (1599 / 4 : ℝ) := by
    have h := Real.one_le_rpow hx₁ (by norm_num : 0 ≤ (1599 / 4 : ℝ))
    dsimp [S]
    push_cast
    linarith
  have hmargin : 12000 * x ^ (1599 / 4 : ℝ) ≤ x ^ (400 : ℕ) := by
    calc
      _ ≤ x ^ (1 / 4 : ℝ) * x ^ (1599 / 4 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hx']; norm_num [Real.rpow_natCast]
  have hupper' : ((S - r : ℕ) : ℝ) ≤ x ^ (400 : ℕ) - 1 :=
    (Nat.cast_le.mpr (Nat.sub_le S r)).trans (by
      linarith [Real.one_le_rpow hx₁ (by norm_num : 0 ≤ (1599 / 4 : ℝ))])
  exact ⟨S - r, htrOdd, htr, by omega, by omega, hstable, hupper', Nat.le_floor (by linarith)⟩

/-- The two cardinality requirements of Proposition 18.11(ix) and Lemma 13.19
leave room for a natural number of words with the ranks of Proposition 5.15. -/
theorem eventually_chainRank_wordCount {ε C₀ CΓ CH : ℝ} (hε : 0 < ε)
    (hC₀ : 1 ≤ C₀) (hCΓ : 0 ≤ CΓ) (hCH : 0 ≤ CH) :
    ∀ᶠ x : ℝ in atTop, ∀ {n m k : ℕ}, (n : ℝ) ≤ 2 * x ^ (2 + 8 * ε) →
      ChainRankBounds x ε m k → ∃ N : ℕ, 0 < N ∧
        C₀ * Real.exp (CΓ * (m : ℝ) ^ 5 * (2 * n) * x ^ ε) ^ (2 : ℕ) * x ^ CH ≤ (N : ℝ) ∧
        (N : ℝ) ≤ 2 ^ ((k : ℝ) - 3) := by
  let C := Real.log (2 * C₀) + CH + 256 * CΓ
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hconst : 0 ≤ Real.log (2 * C₀) := Real.log_nonneg (by linarith)
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    (tendsto_rpow_atTop hε).eventually_ge_atTop (2 * C / Real.log 2)] with x hx hlarge n m k hn hmk
  have hx₁ : 1 ≤ x := by linarith
  have hx' : 0 < x := by positivity
  have hpow : x ≤ x ^ (9 / 2 + 9 * ε) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx₁ (show (1 : ℝ) ≤ 9 / 2 + 9 * ε by linarith)
  have hmk₆ : (6 : ℝ) ≤ (k : ℝ) := by
    refine (show (6 : ℝ) ≤ x ^ (2 : ℕ) by nlinarith).trans (?_ : x ^ (2 : ℕ) ≤ x ^ (9 / 2 + 10 * ε)) |>.trans hmk.rank_lower
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx₁ (by push_cast; linarith)
  have hframe : 2 * (CΓ * (m : ℝ) ^ 5 * (2 * n) * x ^ ε) ≤
      (256 * CΓ) * x ^ (9 / 2 + 9 * ε) := by
    calc
      _ ≤ 2 * (CΓ * (2 * x ^ (1 / 2 - ε / 16)) ^ (5 : ℕ) *
          (2 * (2 * x ^ (2 + 8 * ε))) * x ^ ε) := by gcongr; exact hmk.steps_upper
      _ = (256 * CΓ) * x ^ (9 / 2 + 139 * ε / 16) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hx'.le]
        have h := Real.rpow_add hx' ((1 / 2 - ε / 16) * (5 : ℕ)) (2 + 8 * ε)
        have h' := Real.rpow_add hx' (((1 / 2 - ε / 16) * (5 : ℕ)) + (2 + 8 * ε)) ε
        rw [show 9 / 2 + 139 * ε / 16 = ((1 / 2 - ε / 16) * (5 : ℕ)) + (2 + 8 * ε) + ε by push_cast; ring,
          h', h]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)) (by positivity)
  let A := C₀ * Real.exp (CΓ * (m : ℝ) ^ 5 * (2 * n) * x ^ ε) ^ (2 : ℕ) * x ^ CH
  have hA : 1 ≤ A := by
    dsimp [A]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ (Real.one_le_exp (by positivity))))
      (Real.one_le_rpow hx₁ hCH)
  refine ⟨⌈A⌉₊, Nat.ceil_pos.mpr (by linarith), Nat.le_ceil A, ?_⟩
  refine (Nat.ceil_lt_add_one (show 0 ≤ A by linarith)).le.trans
    ((by linarith : A + 1 ≤ 2 * A).trans ?_)
  -- Compare the logarithms so the polynomial factors of the frame count are explicit.
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_rpow (by norm_num)]
  have hleft : Real.log (2 * A) ≤ C * x ^ (9 / 2 + 9 * ε) := by
    have hlogx : Real.log x ≤ x ^ (9 / 2 + 9 * ε) :=
      (Real.log_le_sub_one_of_pos hx').trans (by linarith)
    have hbase : Real.log (2 * C₀) ≤ Real.log (2 * C₀) * x ^ (9 / 2 + 9 * ε) := by
      simpa using mul_le_mul_of_nonneg_left (hx₁.trans hpow) hconst
    have heq : Real.log (2 * A) = Real.log (2 * C₀) +
        2 * (CΓ * (m : ℝ) ^ 5 * (2 * n) * x ^ ε) + CH * Real.log x := by
      dsimp [A]
      rw [show 2 * (C₀ * Real.exp (CΓ * (m : ℝ) ^ 5 * (2 * n) * x ^ ε) ^ (2 : ℕ) * x ^ CH) =
        (2 * C₀) * Real.exp (CΓ * (m : ℝ) ^ 5 * (2 * n) * x ^ ε) ^ (2 : ℕ) * x ^ CH by ring]
      rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hx' _).ne',
        Real.log_mul (by linarith : 2 * C₀ ≠ 0) (by positivity),
        Real.log_pow, Real.log_exp, Real.log_rpow hx']
      norm_num
    rw [heq]
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hlogx hCH]
  refine hleft.trans ?_
  have hC := (div_le_iff₀ hlog₂).mp hlarge
  calc
    _ ≤ (x ^ ε * x ^ (9 / 2 + 9 * ε)) * Real.log 2 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx'.le (9 / 2 + 9 * ε))]
    _ ≤ _ := by
      rw [← Real.rpow_add hx', show ε + (9 / 2 + 9 * ε) = 9 / 2 + 10 * ε by ring]
      nlinarith [mul_le_mul_of_nonneg_right hmk.rank_lower hlog₂.le,
        mul_le_mul_of_nonneg_right hmk₆ hlog₂.le]

end Riemann
