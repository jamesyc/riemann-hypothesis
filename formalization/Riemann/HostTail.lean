module

public import Riemann.AdmissibleExcess
import Riemann.SelmerWindowSizes
import Utilities.ExponentialGrowth
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Nonvanishing

@[expose] public section

open Filter Asymptotics Utilities
open scoped Topology

namespace Riemann

private theorem twoPow_le_selmerHostBaseGroup_card
    (target : BundledDirichletCharacter) (e : ℕ) :
    2 ^ e ≤ Nat.card (SelmerHostBaseGroup target e) := by
  let _ : NeZero (selmerBaseModulus target e) := ⟨(selmerBaseModulus_pos target e).ne'⟩
  rw [selmerHostBaseGroup_card]
  exact Nat.le_mul_of_pos_left _ Nat.card_pos

theorem selmerHostModulus_le_card
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+) :
    selmerHostModulus target e q d ≤
      4 * Nat.card (SelmerHostBaseGroup target e) * (target.modulus : ℕ) * (q : ℕ) * (d : ℕ) := by
  have hE := twoPow_le_selmerHostBaseGroup_card target e
  refine (selmerHostModulus_le_product target e q d).trans ?_
  rw [pow_add, show (2 : ℕ) ^ 2 = 4 by decide, mul_comm (2 ^ e) 4]
  gcongr

/-- A cubic bound on the dyadic degree controls the logarithm of the host
modulus uniformly over each auxiliary-prime window. -/
theorem exists_selmerHost_logModulus_le_of_twoPow_le_cube
    (target : BundledDirichletCharacter) (D : ℝ) (hD : 1 ≤ D) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {ε base x : ℝ} {q d : ℕ+} {e : ℕ},
      0 ≤ ε → 3 ≤ base → base ≤ x → SelmerWindowPair ε base q d →
      (2 : ℝ) ^ e ≤ D * x ^ (3 : ℕ) →
      1 ≤ A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ) ∧
      Real.log (selmerHostModulus target e q d) ≤ A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ) := by
  let m : ℝ := (target.modulus : ℕ)
  let A := Real.log 4 + Real.log D + Real.log m + 5
  have hD₀ := zero_lt_one.trans_le hD
  have hm₁ : 1 ≤ m := by
    dsimp only [m]
    exact_mod_cast (show 1 ≤ (target.modulus : ℕ) from target.modulus.pos)
  have hm₀ := zero_lt_one.trans_le hm₁
  have hA : 1 ≤ A := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
    dsimp [A]
    linarith [Real.log_nonneg hm₁]
  refine ⟨A, hA, fun {ε base x q d e} hε hbase hbx hpair hpowCube => ?_⟩
  have hx₁ : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 3).trans (hbase.trans hbx)
  have hx₀ := zero_lt_one.trans_le hx₁
  have hlog₁ : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx₀).mpr
    (Real.exp_one_lt_three.le.trans (hbase.trans hbx))
  have hpow : 1 ≤ x ^ (ε / 5) := Real.one_le_rpow hx₁ (by positivity)
  let B := x ^ (ε / 5) * Real.log x ^ (2 : ℕ)
  have hBpow : x ^ (ε / 5) ≤ B :=
    le_mul_of_one_le_right (by positivity) (by nlinarith)
  have hBlog : Real.log x ≤ B := by
    exact (show Real.log x ≤ Real.log x ^ (2 : ℕ) by nlinarith).trans
      (le_mul_of_one_le_left (sq_nonneg _) hpow)
  have hB : 1 ≤ B := hlog₁.trans hBlog
  have hAB : 1 ≤ A * B := hA.trans (le_mul_of_one_le_right (by positivity) hB)
  refine ⟨by simpa only [B, mul_assoc] using hAB, ?_⟩
  let n : ℝ := (2 : ℝ) ^ e
  have hn : 0 < n := by dsimp only [n]; positivity
  have hlogn : Real.log n ≤ Real.log D + 3 * Real.log x := by
    have h := Real.log_le_log hn hpowCube
    rw [Real.log_mul hD₀.ne' (pow_pos hx₀ _).ne', Real.log_pow] at h
    norm_num at h
    simpa only [n, Real.log_pow] using h
  have hlogqd : Real.log ((q : ℕ) * (d : ℕ) : ℝ) ≤ 2 * B := by
    calc
      _ ≤ x ^ (ε / 5) * (1 + Real.log x ^ (2 : ℕ)) := hpair.log_mul_upper hε hbx
      _ = x ^ (ε / 5) + B := by dsimp [B]; ring
      _ ≤ 2 * B := by linarith
  have hqd₀ : (0 : ℝ) < (q : ℕ) * (d : ℕ) :=
    mul_pos (by exact_mod_cast q.pos) (by exact_mod_cast d.pos)
  have hN₀ : (0 : ℝ) < selmerHostModulus target e q d := by
    exact_mod_cast selmerHostModulus_pos target e q d
  have hN : (selmerHostModulus target e q d : ℝ) ≤ 4 * n * m * ((q : ℕ) * (d : ℕ)) := by
    calc
      _ ≤ (2 : ℝ) ^ (e + 2) * m * (q : ℕ) * (d : ℕ) := by
        dsimp only [m]
        exact_mod_cast selmerHostModulus_le_product target e q d
      _ = _ := by rw [pow_add]; dsimp only [n]; norm_num; ring
  have hlogs := Real.log_le_log hN₀ hN
  rw [Real.log_mul (by positivity) hqd₀.ne', Real.log_mul (by positivity) hm₀.ne',
    Real.log_mul (by norm_num) hn.ne'] at hlogs
  have hconst₀ : 0 ≤ Real.log 4 + Real.log D + Real.log m :=
    add_nonneg (add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hD))
      (Real.log_nonneg hm₁)
  have hconst := le_mul_of_one_le_right hconst₀ hB
  change _ ≤ A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ)
  rw [mul_assoc]
  change _ ≤ A * B
  dsimp only [A]
  nlinarith

/-- Proposition 5.3's logarithmic conductor range from the host cardinality
bound in the prepared windows. -/
theorem exists_selmerHost_logModulus_le (target : BundledDirichletCharacter) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {ε base x : ℝ} {q d : ℕ+} {e : ℕ},
      0 ≤ ε → 3 ≤ base → base ≤ x → SelmerWindowPair ε base q d →
      (Nat.card (SelmerHostBaseGroup target e) : ℝ) ≤ 2 * x ^ (2 + 8 * ε) →
      ε ≤ 1 / 52 →
      1 ≤ A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ) ∧
      Real.log (selmerHostModulus target e q d) ≤ A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ) := by
  obtain ⟨A, hA, hmodulus⟩ := exists_selmerHost_logModulus_le_of_twoPow_le_cube target 2 (by norm_num)
  refine ⟨A, hA, fun {ε base x q d e} hε hbase hbx hp hcard hε' => hmodulus hε hbase hbx hp ?_⟩
  have hdyadic : (2 : ℝ) ^ e ≤ Nat.card (SelmerHostBaseGroup target e) := by
    exact_mod_cast twoPow_le_selmerHostBaseGroup_card target e
  have hx₁ : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 3).trans (hbase.trans hbx)
  refine (hdyadic.trans hcard).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num; linarith)

theorem selmerHostInducingCharacter_logModulus_le
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H]
    (coord : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)) (ψ : ExcessCharacter H) :
    Real.log ((selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
      coord ψ).modulus : ℕ) ≤ Real.log (selmerHostModulus target e q d) := by
  let χ := selmerHostDirichlet (target := target) (e := e) (q := q) (d := d) coord ψ
  let _ : NeZero (selmerHostModulus target e q d) := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  change Real.log (χ.conductor : ℝ) ≤ _
  apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
  exact_mod_cast Nat.le_of_dvd (selmerHostModulus_pos target e q d) χ.conductor_dvd_level

private theorem eventually_scaledExpDecay_le {r b c D δ : ℝ} (a : ℝ)
    (hr : 0 < r) (hrb : r < b) (hc : 0 < c) (hD : 0 < D) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, D * x ^ a * Real.exp (-c * x ^ b) ≤ δ * Real.exp (-(x ^ r)) := by
  have hlog := (((isLittleO_log_rpow_atTop hr).const_mul_left a).add
    (isLittleO_const_rpow_atTop (Real.log (D / δ)) hr)).bound (zero_lt_one : (0 : ℝ) < 1)
  have hpow := (tendsto_rpow_atTop (sub_pos.mpr hrb)).eventually_ge_atTop (2 / c)
  filter_upwards [hlog, hpow, eventually_gt_atTop (0 : ℝ)] with x hlogx hpowx hx
  change ‖a * Real.log x + Real.log (D / δ)‖ ≤ 1 * ‖x ^ r‖ at hlogx
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)] at hlogx
  have hupper := (le_abs_self (a * Real.log x + Real.log (D / δ))).trans hlogx
  have hlower : 2 * x ^ r ≤ c * x ^ b := by
    have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp hpowx) (Real.rpow_nonneg hx.le r)
    calc
      _ ≤ (x ^ (b - r) * c) * x ^ r := h
      _ = _ := by rw [mul_comm (x ^ (b - r)) c, mul_assoc, ← Real.rpow_add hx,
        show b - r + r = b by ring]
  have hexponent : Real.log (D / δ) + Real.log x * a - c * x ^ b ≤ -(x ^ r) := by linarith
  calc
    _ = δ * Real.exp (Real.log (D / δ) + Real.log x * a - c * x ^ b) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_log (div_pos hD hδ), ← Real.rpow_def_of_pos hx,
        neg_mul, Real.exp_neg]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hδ.le

/-- An envelope for the three terms of Proposition 5.3, after taking one
constant prefactor and one common positive exponential coefficient. -/
noncomputable def selmerTailEnvelope (K c L t : ℝ) : ℝ :=
  K * L ^ (5 : ℕ) *
    (Real.exp (-c * t) + Real.exp (-c * t / L) +
      (1 + c * Real.sqrt t) * Real.exp (-c * Real.sqrt t))

/-- At the scale dictated by the thin nodes, the envelope from Proposition
5.3 is uniformly bounded by the slope used in §6.3. -/
theorem eventually_selmerTailEnvelope_le {ε A K c : ℝ}
    (hε : 0 < ε) (hA : 1 ≤ A) (hK : 0 < K) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, ∀ L t : ℝ,
      1 ≤ L → L ≤ A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ) →
      (1 / 2 : ℝ) * x ^ (ε / 3) ≤ t →
      selmerTailEnvelope K c L t ≤ Real.exp (-(x ^ (ε / 8))) := by
  let a := (61 / 300 : ℝ) * ε
  let b := (13 / 100 : ℝ) * ε
  let k := c / (4 * A)
  have hA₀ := zero_lt_one.trans_le hA
  have hk₀ : 0 < k := div_pos hc (by positivity)
  have hk : k ≤ c / 4 := by
    dsimp [k]
    exact div_le_div_of_nonneg_left hc.le (by norm_num) (by linarith)
  have hk' : k ≤ c / (2 * A) := by
    dsimp [k]
    exact div_le_div_of_nonneg_left hc.le (by positivity) (by linarith)
  have hfast := eventually_scaledExpDecay_le (5 * a)
    (show 0 < ε / 8 by positivity) (show ε / 8 < b by dsimp [b]; linarith)
    hk₀ (show 0 < 4 * K * A ^ (5 : ℕ) by positivity) (δ := 1) one_pos
  have hlog := (isLittleO_log_rpow_atTop (show 0 < ε / 600 by positivity)).bound
    (zero_lt_one : (0 : ℝ) < 1)
  filter_upwards [hfast, hlog, eventually_ge_atTop (1 : ℝ)] with x hfx hlogx hx L t hL₁ hL ht
  have hx₀ := zero_lt_one.trans_le hx
  have hL₀ := zero_lt_one.trans_le hL₁
  have ht₀ : 0 < t := (by positivity : 0 < (1 / 2 : ℝ) * x ^ (ε / 3)).trans_le ht
  have hlog₀ := Real.log_nonneg hx
  rw [one_mul, Real.norm_of_nonneg hlog₀, Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _)] at hlogx
  have hL' : L ≤ A * x ^ a := by
    calc
      _ ≤ A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ) := hL
      _ ≤ A * x ^ (ε / 5) * (x ^ (ε / 600)) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog₀ hlogx _) (by positivity)
      _ = _ := by
        rw [pow_two, mul_assoc, ← Real.rpow_add hx₀, ← Real.rpow_add hx₀]
        congr 2
        dsimp [a]
        ring
  have hLpower : L ^ (5 : ℕ) ≤ A ^ (5 : ℕ) * x ^ (5 * a) := by
    calc
      _ ≤ (A * x ^ a) ^ (5 : ℕ) := pow_le_pow_left₀ hL₀.le hL' _
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ a), ← Real.rpow_mul hx₀.le, mul_comm a]
        norm_num
  have hbx : x ^ b ≤ x ^ (ε / 3) :=
    Real.rpow_le_rpow_of_exponent_le hx (show b ≤ ε / 3 by dsimp [b]; linarith)
  have hbt : x ^ b / 2 ≤ t := by
    calc
      _ = (1 / 2 : ℝ) * x ^ b := by ring
      _ ≤ (1 / 2 : ℝ) * x ^ (ε / 3) := mul_le_mul_of_nonneg_left hbx (by norm_num)
      _ ≤ _ := ht
  have hbtL : x ^ b / (2 * A) ≤ t / L := by
    apply (le_div_iff₀ hL₀).mpr
    calc
      _ ≤ (x ^ b / (2 * A)) * (A * x ^ a) :=
        mul_le_mul_of_nonneg_left hL' (by positivity)
      _ = (1 / 2 : ℝ) * x ^ (ε / 3) := by
        rw [show ε / 3 = b + a by dsimp [a, b]; ring, Real.rpow_add hx₀]
        field_simp
      _ ≤ _ := ht
  have hbsqrt : x ^ b / 2 ≤ Real.sqrt t := by
    apply (Real.le_sqrt (by positivity) ht₀.le).mpr
    calc
      (x ^ b / 2) ^ (2 : ℕ) = x ^ (b + b) / 4 := by
        rw [div_pow, pow_two (x ^ b), ← Real.rpow_add hx₀]
        norm_num
      _ ≤ x ^ (ε / 3) / 4 :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx (by dsimp [b]; linarith))
          (by norm_num)
      _ ≤ (1 / 2 : ℝ) * x ^ (ε / 3) := by nlinarith [Real.rpow_nonneg hx₀.le (ε / 3)]
      _ ≤ _ := ht
  have h1 : k * x ^ b ≤ c * t := by
    have h := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hx₀.le b)
    nlinarith [mul_le_mul_of_nonneg_left hbt hc.le, mul_nonneg hc.le (Real.rpow_nonneg hx₀.le b)]
  have h2 : k * x ^ b ≤ c * t / L := by
    calc
      _ ≤ (c / (2 * A)) * x ^ b := mul_le_mul_of_nonneg_right hk' (by positivity)
      _ = c * (x ^ b / (2 * A)) := by ring
      _ ≤ c * (t / L) := mul_le_mul_of_nonneg_left hbtL hc.le
      _ = _ := by ring
  have h3 : k * x ^ b ≤ c * Real.sqrt t / 2 := by
    have h := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hx₀.le b)
    nlinarith [mul_le_mul_of_nonneg_left hbsqrt hc.le]
  let u := c * Real.sqrt t
  have hu : 0 ≤ u := by positivity
  have hthird : (1 + u) * Real.exp (-u) ≤ 2 * Real.exp (-(k * x ^ b)) := by
    have hu' := Real.add_one_le_exp (u / 2)
    calc
      _ ≤ (2 * Real.exp (u / 2)) * Real.exp (-u) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith
      _ = 2 * Real.exp (-(u / 2)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg h3)) (by norm_num)
  have hterms :
      Real.exp (-c * t) + Real.exp (-c * t / L) + (1 + u) * Real.exp (-u) ≤
        4 * Real.exp (-(k * x ^ b)) := by
    have he1 : Real.exp (-c * t) ≤ Real.exp (-(k * x ^ b)) :=
      Real.exp_le_exp.mpr (by linarith)
    have he2 : Real.exp (-c * t / L) ≤ Real.exp (-(k * x ^ b)) := by
      rw [neg_mul, neg_div]
      exact Real.exp_le_exp.mpr (neg_le_neg h2)
    linarith
  calc
    selmerTailEnvelope K c L t ≤ (K * (A ^ (5 : ℕ) * x ^ (5 * a))) *
        (4 * Real.exp (-(k * x ^ b))) := by
      unfold selmerTailEnvelope
      exact mul_le_mul (mul_le_mul_of_nonneg_left hLpower hK.le)
        (by simpa only [u, neg_mul] using hterms) (by positivity) (by positivity)
    _ = (4 * K * A ^ (5 : ℕ)) * x ^ (5 * a) * Real.exp (-k * x ^ b) := by ring_nf
    _ ≤ _ := by simpa only [one_mul] using hfx

/-- The thin cutoff forces a uniform lower bound on the logarithm of the
argument of every smoothed tail. -/
theorem eventually_log_ge_of_thinCutoff {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y →
      (1 / 2 : ℝ) * x ^ (ε / 3) ≤ Real.log y := by
  have hgrow := (tendsto_rpow_atTop (show 0 < ε / 3 by positivity)).eventually_ge_atTop
    (2 * Real.log 3)
  filter_upwards [hgrow] with x hx y hy
  have hbase : 0 < Real.exp (x ^ (ε / 3)) / 3 := by positivity
  have h := Real.log_le_log hbase hy
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at h
  linarith

/-- The three-term majorant of Proposition 5.3 can be used directly at
every thin-node argument. The coefficients are uniform in the cutoff and
logarithmic conductor. -/
theorem eventually_tailBound_of_prop53_majorant {ε A P Q R c₀ c₁ : ℝ}
    (hε : 0 < ε) (hA : 1 ≤ A) (hP : 0 < P) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    ∀ᶠ x : ℝ in atTop, ∀ L y v : ℝ,
      1 ≤ L → L ≤ A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ) →
      Real.exp (x ^ (ε / 3)) / 3 ≤ y →
      v ≤ y * (P * Real.exp (-c₀ * Real.log y) +
        Q * L ^ (5 : ℕ) * Real.exp (-c₁ * Real.log y / L) +
        R * L ^ (4 : ℕ) * (1 + c₁ * Real.sqrt (Real.log y)) *
          Real.exp (-c₁ * Real.sqrt (Real.log y))) →
      v ≤ Real.exp (-(x ^ (ε / 8))) * y := by
  let c := min c₀ c₁
  have hc : 0 < c := lt_min hc₀ hc₁
  let K := P + Q + R * (c₁ / c)
  have hK : 0 < K := by positivity
  have hPc : P ≤ K := by
    dsimp [K]
    linarith [mul_nonneg hR (div_nonneg hc₁.le hc.le)]
  have hQc : Q ≤ K := by
    dsimp [K]
    linarith [mul_nonneg hR (div_nonneg hc₁.le hc.le)]
  have hRc : R * (c₁ / c) ≤ K := by
    dsimp [K]
    linarith
  filter_upwards [eventually_log_ge_of_thinCutoff hε, eventually_selmerTailEnvelope_le hε hA hK hc,
    eventually_ge_atTop (1 : ℝ)] with x hlog henv hx L y v hL hLa hy hv
  have hy₀ : 0 ≤ y := (by positivity : 0 ≤ Real.exp (x ^ (ε / 3)) / 3).trans hy
  let t := Real.log y
  have ht : ((1 / 2 : ℝ) * x ^ (ε / 3)) ≤ t := hlog y hy
  have ht₀ : 0 ≤ t := (mul_nonneg (by norm_num)
    (Real.rpow_nonneg (zero_le_one.trans hx) _)).trans ht
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have hLpow : (1 : ℝ) ≤ L ^ (5 : ℕ) := one_le_pow₀ hL
  have hLpow' : L ^ (4 : ℕ) ≤ L ^ (5 : ℕ) := pow_right_mono₀ hL (by decide)
  have hc₀' : c ≤ c₀ := min_le_left _ _
  have hc₁' : c ≤ c₁ := min_le_right _ _
  have hfirst : P * Real.exp (-c₀ * t) ≤ K * L ^ (5 : ℕ) * Real.exp (-c * t) := by
    have hp := hPc.trans (le_mul_of_one_le_right hK.le hLpow)
    apply mul_le_mul hp _ (Real.exp_pos _).le (by positivity)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hc₀') ht₀)
  have hsecond : Q * L ^ (5 : ℕ) * Real.exp (-c₁ * t / L) ≤
      K * L ^ (5 : ℕ) * Real.exp (-c * t / L) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hQc (by positivity)) _ (Real.exp_pos _).le
      (by positivity)
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (neg_le_neg hc₁') ht₀) hL₀.le)
  have hthird : R * L ^ (4 : ℕ) * (1 + c₁ * Real.sqrt t) * Real.exp (-c₁ * Real.sqrt t) ≤
      K * L ^ (5 : ℕ) * ((1 + c * Real.sqrt t) * Real.exp (-c * Real.sqrt t)) := by
    have hcRatio : (1 : ℝ) ≤ c₁ / c := (one_le_div hc).mpr hc₁'
    have hlin : 1 + c₁ * Real.sqrt t ≤ (c₁ / c) * (1 + c * Real.sqrt t) := by
      rw [mul_add, mul_one, ← mul_assoc, div_mul_cancel₀ _ hc.ne']
      linarith
    calc
      _ ≤ R * L ^ (5 : ℕ) * ((c₁ / c) * (1 + c * Real.sqrt t)) * Real.exp (-c₁ * Real.sqrt t) := by
        gcongr
      _ = (R * (c₁ / c)) * L ^ (5 : ℕ) * (1 + c * Real.sqrt t) * Real.exp (-c₁ * Real.sqrt t) := by ring
      _ ≤ _ := by
        rw [← mul_assoc]
        apply mul_le_mul _ _ (Real.exp_pos _).le (by positivity)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRc (by positivity))
            (by positivity)
        · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hc₁') (Real.sqrt_nonneg t))
  have hsum :
      P * Real.exp (-c₀ * t) + Q * L ^ (5 : ℕ) * Real.exp (-c₁ * t / L) +
        R * L ^ (4 : ℕ) * (1 + c₁ * Real.sqrt t) * Real.exp (-c₁ * Real.sqrt t) ≤
          selmerTailEnvelope K c L t := by
    calc
      _ ≤ K * L ^ (5 : ℕ) * Real.exp (-c * t) + K * L ^ (5 : ℕ) * Real.exp (-c * t / L) +
          K * L ^ (5 : ℕ) * ((1 + c * Real.sqrt t) * Real.exp (-c * Real.sqrt t)) :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ = _ := by unfold selmerTailEnvelope; ring
  refine hv.trans ?_
  rw [mul_comm (Real.exp (-(x ^ (ε / 8)))) y]
  exact mul_le_mul_of_nonneg_left (hsum.trans (henv L t hL hLa ht)) hy₀

/-- All nontrivial characters with modulus dividing one fixed level
share a real zero-free interval immediately below one. -/
theorem exists_noRealZero_nearOne_of_modulus_dvd (M : ℕ+) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 400 ∧ ∀ χ : BundledDirichletCharacter,
      (χ.modulus : ℕ) ∣ (M : ℕ) → χ.character ≠ 1 →
      ∀ β ∈ Set.Ioo (1 - c) 1, DirichletCharacter.LFunction χ.character (β : ℂ) ≠ 0 := by
  let I := Σ n : Fin (M : ℕ), {χ : DirichletCharacter ℂ ((n : ℕ) + 1) // χ ≠ 1}
  let _ : ∀ n : Fin (M : ℕ), Finite {χ : DirichletCharacter ℂ ((n : ℕ) + 1) // χ ≠ 1} :=
    fun n => by
      let _ : NeZero ((n : ℕ) + 1) := ⟨Nat.succ_ne_zero _⟩
      infer_instance
  let _ : Finite I := by dsimp only [I]; infer_instance
  have hone (i : I) : ∀ᶠ β : ℝ in 𝓝 1,
      DirichletCharacter.LFunction i.2.val (β : ℂ) ≠ 0 := by
    let _ : NeZero ((i.1 : ℕ) + 1) := ⟨Nat.succ_ne_zero _⟩
    have hc : Continuous (fun β : ℝ => DirichletCharacter.LFunction i.2.val (β : ℂ)) :=
      (DirichletCharacter.differentiable_LFunction i.2.property).continuous.comp Complex.continuous_ofReal
    apply hc.continuousAt.eventually_ne
    rw [Complex.ofReal_one]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re i.2.val (Or.inl i.2.property) (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (Filter.eventually_all.mpr hone)
  let c := min r (1 / 400 : ℝ)
  have hc₀ : 0 < c := lt_min hr (by norm_num)
  refine ⟨c, hc₀, min_le_right _ _, fun χ hdiv hχ β hβ => ?_⟩
  rcases χ with ⟨⟨n, hn⟩, χ⟩
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ j =>
    have hj : j < M := Nat.lt_of_succ_le (Nat.le_of_dvd M.pos hdiv)
    let i : I := ⟨⟨j, hj⟩, ⟨χ, hχ⟩⟩
    have hdist : β ∈ Metric.ball (1 : ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hβ.2)]
      have hm : c ≤ r := min_le_left _ _
      linarith [hβ.1]
    exact hball β hdist i

end Riemann
