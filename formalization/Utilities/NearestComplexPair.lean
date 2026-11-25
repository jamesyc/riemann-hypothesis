module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open scoped ComplexConjugate

namespace Utilities

private theorem sq_dist_real_center (σ : ℝ) (z : ℂ) :
    dist (σ : ℂ) z ^ 2 = (σ - z.re) ^ 2 + z.im ^ 2 := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem real_center_eq_bisector {σ : ℝ} {z w : ℂ}
    (heq : dist (σ : ℂ) z = dist (σ : ℂ) w) (hre : w.re ≠ z.re) :
    σ = (‖w‖ ^ 2 - ‖z‖ ^ 2) / (2 * (w.re - z.re)) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hre))).mpr
  have hsq := congrArg (fun d : ℝ => d ^ 2) heq
  rw [sq_dist_real_center, sq_dist_real_center] at hsq
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  nlinarith only [hsq]

private theorem eq_or_eq_conj_of_equal_dist_of_equal_re {σ : ℝ} {z w : ℂ}
    (heq : dist (σ : ℂ) z = dist (σ : ℂ) w) (hre : w.re = z.re) : w = z ∨ w = conj z := by
  have hsq := congrArg (fun d : ℝ => d ^ 2) heq
  rw [sq_dist_real_center, sq_dist_real_center, hre] at hsq
  have hprod : (w.im - z.im) * (w.im + z.im) = 0 := by nlinarith only [hsq]
  rcases mul_eq_zero.mp hprod with hdiff | hsum
  · exact Or.inl (Complex.ext hre (sub_eq_zero.mp hdiff))
  · refine Or.inr (Complex.ext ?_ ?_)
    · simpa only [Complex.conj_re] using hre
    · simpa only [Complex.conj_im] using eq_neg_of_add_eq_zero_left hsum

/-- For a conjugation-invariant set finite on every bounded disc, choose a
real center whose nearest points consist of one real point or one conjugate pair.
The larger radius still sees exactly those nearest points. -/
theorem exists_isolated_nearest_conj_pair (P : Set ℂ) (hfinite : ∀ R : ℝ,
    (P ∩ Metric.closedBall 0 R).Finite) (hconj : ∀ z ∈ P, conj z ∈ P)
    {exponent : ℝ} (hupper : ∀ z ∈ P, exponent < z.re → z.re < 1)
    {p : ℂ} (hp : p ∈ P) (hpRe : exponent < p.re)
    (σmin : ℝ) (hσmin : 1 < σmin) :
    ∃ (σ r R : ℝ) (q : ℂ), σmin ≤ σ ∧ σ - 1 < r ∧ r < R ∧ R < σ - exponent ∧
      q ∈ P ∧ 0 ≤ q.im ∧ dist (σ : ℂ) q = r ∧
        ∀ z ∈ P, dist (σ : ℂ) z ≤ R → z = q ∨ z = conj q := by
  let T := max σmin (max (exponent + 1) ((‖p‖ ^ 2 + 1) / (2 * (p.re - exponent))))
  let M := 2 * (T + 1) + ‖p‖ + 1
  let candidates := P ∩ Metric.closedBall (0 : ℂ) M
  have hfiniteCandidates : candidates.Finite := hfinite M
  let bisector (pair : ℂ × ℂ) :=
    (‖pair.2‖ ^ 2 - ‖pair.1‖ ^ 2) / (2 * (pair.2.re - pair.1.re))
  let ties := bisector '' (candidates ×ˢ candidates)
  have hfiniteTies : ties.Finite := (hfiniteCandidates.prod hfiniteCandidates).image bisector
  obtain ⟨σ, hσ, hσNotTie⟩ : ∃ σ ∈ Set.Ioo T (T + 1), σ ∉ ties := by
    by_contra hnone
    have hsubset : Set.Ioo T (T + 1) ⊆ ties := by
      intro s hs
      by_contra hs'
      exact hnone ⟨s, hs, hs'⟩
    exact (Set.Ioo_infinite (by linarith : T < T + 1)) (hfiniteTies.subset hsubset)
  have hσLarge : σmin ≤ σ := (le_max_left _ _).trans hσ.1.le
  have hσ₀ : 0 < σ := (zero_lt_one.trans hσmin).trans_le hσLarge
  have hσExp : exponent < σ := by
    have h := ((le_max_left (exponent + 1) _).trans (le_max_right σmin _)).trans_lt hσ.1
    linarith
  have htargetDist : dist (σ : ℂ) p < σ - exponent := by
    have hnum := ((le_max_right (exponent + 1) _).trans (le_max_right σmin _)).trans_lt hσ.1
    have hbig := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr hpRe))).mp hnum
    rw [Complex.sq_norm, Complex.normSq_apply] at hbig
    apply (sq_lt_sq₀ dist_nonneg (sub_pos.mpr hσExp).le).mp
    rw [sq_dist_real_center]
    nlinarith only [hbig, sq_nonneg exponent]
  have htargetBound : dist (σ : ℂ) p ≤ σ + ‖p‖ := by
    rw [dist_eq_norm]
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ₀.le] using norm_sub_le (σ : ℂ) p
  have hcand (z : ℂ) (hz : z ∈ P) (hd : dist (σ : ℂ) z ≤ dist (σ : ℂ) p + 1) :
      z ∈ candidates := by
    refine ⟨hz, ?_⟩
    have hnorm : ‖z‖ ≤ dist (σ : ℂ) z + σ := by
      calc
        ‖z‖ = ‖z - (σ : ℂ) + (σ : ℂ)‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - (σ : ℂ)‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
        _ = _ := by rw [← dist_eq_norm, dist_comm z (σ : ℂ), Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hσ₀.le]
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp only [M]
    linarith [hσ.2]
  have hpCand : p ∈ candidates := hcand p hp (by linarith)
  obtain ⟨q₀, hq₀, hminimal⟩ := candidates.exists_min_image (dist (σ : ℂ)) hfiniteCandidates ⟨p, hpCand⟩
  let r := dist (σ : ℂ) q₀
  have hrTarget : r ≤ dist (σ : ℂ) p := hminimal p hpCand
  have hrExp : r < σ - exponent := hrTarget.trans_lt htargetDist
  have hq₀P : q₀ ∈ P := hq₀.1
  have hrealBound : σ - q₀.re ≤ r := by
    simpa only [r, dist_eq_norm, Complex.sub_re, Complex.ofReal_re] using
      Complex.re_le_norm ((σ : ℂ) - q₀)
  have hqExp : exponent < q₀.re := by linarith
  have hqUpper := hupper q₀ hq₀P hqExp
  have hrLower : σ - 1 < r := by linarith
  let cap := min (σ - exponent) (dist (σ : ℂ) p + 1)
  let larger := insert cap ((dist (σ : ℂ) '' candidates) ∩ Set.Ioi r)
  have hfiniteLarger : larger.Finite := ((hfiniteCandidates.image _).subset Set.inter_subset_left).insert cap
  obtain ⟨d, hd, hdMin⟩ := larger.exists_min_image id hfiniteLarger ⟨cap, Set.mem_insert _ _⟩
  have hcap : r < cap := lt_min hrExp (by linarith)
  have hdLarger : r < d := by
    rcases Set.mem_insert_iff.mp hd with hdEq | hdOther
    · rwa [hdEq]
    · exact hdOther.2
  have hdCap : d ≤ cap := hdMin cap (Set.mem_insert _ _)
  let R := (d + r) / 2
  have hR : r < R := by dsimp only [R]; linarith
  have hRd : R < d := by dsimp only [R]; linarith
  have hRExp : R < σ - exponent := (hRd.trans_le hdCap).trans_le (min_le_left _ _)
  have hRTarget : R < dist (σ : ℂ) p + 1 := (hRd.trans_le hdCap).trans_le (min_le_right _ _)
  have hpair (z : ℂ) (hz : z ∈ P) (hzR : dist (σ : ℂ) z ≤ R) :
      z = q₀ ∨ z = conj q₀ := by
    have hzC := hcand z hz (hzR.trans hRTarget.le)
    have hdistLower : r ≤ dist (σ : ℂ) z := hminimal z hzC
    have hdistUpper : dist (σ : ℂ) z ≤ r := by
      by_contra! hlt
      have hzL : dist (σ : ℂ) z ∈ larger := Set.mem_insert_of_mem _ ⟨Set.mem_image_of_mem _ hzC, hlt⟩
      exact (not_lt_of_ge ((hdMin _ hzL).trans hzR)) hRd
    have hdist : dist (σ : ℂ) q₀ = dist (σ : ℂ) z := le_antisymm hdistLower hdistUpper
    by_cases hre : z.re = q₀.re
    · exact eq_or_eq_conj_of_equal_dist_of_equal_re hdist hre
    · exact (hσNotTie ⟨(q₀, z), ⟨hq₀, hzC⟩, (real_center_eq_bisector hdist hre).symm⟩).elim
  by_cases him : 0 ≤ q₀.im
  · exact ⟨σ, r, R, q₀, hσLarge, hrLower, hR, hRExp, hq₀P, him, rfl, hpair⟩
  · have hqdist : dist (σ : ℂ) (conj q₀) = r := by
      rw [← Complex.dist_conj_comm, Complex.conj_ofReal]
    refine ⟨σ, r, R, conj q₀, hσLarge, hrLower, hR, hRExp, hconj q₀ hq₀P, ?_, hqdist, ?_⟩
    · rw [Complex.conj_im]
      exact neg_nonneg.mpr (lt_of_not_ge him).le
    · intro z hz hzR
      simpa only [Complex.conj_conj] using (hpair z hz hzR).symm

end Utilities
