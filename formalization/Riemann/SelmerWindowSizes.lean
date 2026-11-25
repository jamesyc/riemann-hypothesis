module

public import Riemann.SelmerWindows
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Utilities.ExponentialGrowth

@[expose] public section

open Filter Asymptotics Utilities

namespace Riemann

/-- Logarithmic size of the product of the auxiliary primes at any scale
above the window base. -/
theorem SelmerWindowPair.log_mul_upper {ε base x : ℝ} {q d : ℕ+}
    (hpair : SelmerWindowPair ε base q d) (hε : 0 ≤ ε) (hbase : base ≤ x) :
    Real.log ((q : ℕ) * (d : ℕ) : ℝ) ≤ x ^ (ε / 5) * (1 + Real.log x ^ (2 : ℕ)) := by
  have hb : 0 < base := by linarith [hpair.base_ge_two]
  have hlog₀ : 0 ≤ Real.log base := Real.log_nonneg (by linarith [hpair.base_ge_two])
  have hlog := Real.log_le_log hb hbase
  have hlog₂ : Real.log base ^ (2 : ℕ) ≤ Real.log x ^ (2 : ℕ) := by gcongr
  have hpow := Real.rpow_le_rpow hb.le hbase (by positivity : 0 ≤ ε / 5)
  rw [Real.log_mul (by exact_mod_cast q.pos.ne') (by exact_mod_cast d.pos.ne')]
  calc
    _ ≤ base ^ (ε / 5) + base ^ (ε / 5) * Real.log base ^ (2 : ℕ) :=
      add_le_add hpair.q_upper hpair.d_upper
    _ = base ^ (ε / 5) * (1 + Real.log base ^ (2 : ℕ)) := by ring
    _ ≤ _ := mul_le_mul hpow (by linarith only [hlog₂]) (by positivity)
      (Real.rpow_nonneg (hb.le.trans hbase) _)

/-- At sufficiently large window scales, the product of the auxiliary primes
has the logarithmic size used in the proof of Theorem 17.12. -/
theorem eventually_selmerWindowPair_log_mul_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ base : ℝ in atTop, ∀ q d : ℕ+, SelmerWindowPair ε base q d →
      Real.log ((q : ℕ) * (d : ℕ) : ℝ) ≤ base ^ (ε / 4) := by
  have hgap : 0 < ε / 20 := by positivity
  have hlog : (fun x : ℝ => Real.log x ^ (2 : ℕ)) =o[atTop] (fun x : ℝ => x ^ (ε / 20)) := by
    simpa only [← Real.rpow_natCast, Nat.cast_ofNat] using
      isLittleO_log_rpow_rpow_atTop (2 : ℝ) hgap
  have hpow := (tendsto_rpow_atTop hgap).eventually_ge_atTop (2 : ℝ)
  filter_upwards [hlog.bound (by norm_num : (0 : ℝ) < 1 / 2), hpow] with base hsmall hlarge q d hp
  have hbase : 0 ≤ base := by linarith [hp.base_ge_two]
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (Real.rpow_nonneg hbase _)] at hsmall
  have hlogle : 1 + Real.log base ^ (2 : ℕ) ≤ base ^ (ε / 20) := by linarith
  calc
    _ ≤ base ^ (ε / 5) * (1 + Real.log base ^ (2 : ℕ)) := hp.log_mul_upper hε.le le_rfl
    _ ≤ base ^ (ε / 5) * base ^ (ε / 20) :=
      mul_le_mul_of_nonneg_left hlogle (Real.rpow_nonneg hbase _)
    _ = base ^ (ε / 4) := by
      rw [← Real.rpow_add (by linarith [hp.base_ge_two]), show ε / 5 + ε / 20 = ε / 4 by ring]

/-- Both auxiliary primes eventually dominate any fixed power of the base. -/
theorem eventually_selmerWindowPair_gt_rpow {ε : ℝ} (hε : 0 < ε) (K : ℝ)
    (hK : 0 < K) (r : ℝ) :
    ∀ᶠ base : ℝ in atTop, ∀ q d : ℕ+, SelmerWindowPair ε base q d →
      K * base ^ r < (q : ℕ) ∧ K * base ^ r < (d : ℕ) := by
  have hexp : 0 < ε / 5 := by positivity
  have hlog := (isLittleO_log_rpow_atTop hexp).const_mul_left r
  have hconst := Utilities.isLittleO_const_rpow_atTop (Real.log K) hexp
  have hbound := (hconst.add hlog).bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with base hb hl q d hp
  have hbase : 0 < base := by linarith [hp.base_ge_two]
  have hmain : Real.log (K * base ^ r) ≤ base ^ (ε / 5) / 2 := by
    rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hbase _).ne', Real.log_rpow hbase]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hbase.le _)] at hb
    have h := (le_abs_self (Real.log K + r * Real.log base)).trans hb
    linarith
  have hd : base ^ (ε / 5) / 2 < Real.log (d : ℕ) :=
    (div_le_div_of_nonneg_right
      (le_mul_of_one_le_right (Real.rpow_nonneg hbase.le _)
        (one_le_pow₀ hl)) (by norm_num)).trans_lt hp.d_lower
  have hKl : 0 < K * base ^ r := mul_pos hK (Real.rpow_pos_of_pos hbase _)
  exact ⟨(Real.log_lt_log_iff hKl (by exact_mod_cast q.pos)).mp (hmain.trans_lt hp.q_lower),
    (Real.log_lt_log_iff hKl (by exact_mod_cast d.pos)).mp (hmain.trans_lt hd)⟩

end Riemann
