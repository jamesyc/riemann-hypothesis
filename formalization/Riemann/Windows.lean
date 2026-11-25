module

public import Mathlib.Data.PNat.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Riemann.Consequences
public import Riemann.AdmissibleChain
public import Utilities.SmoothedMangoldtMellin
public import Riemann.WindowCriterion
import Riemann.SelmerWindowEstimates
import Riemann.PreparedExcessWindows

@[expose] public section

open Filter Utilities
open scoped BigOperators
open scoped Topology

namespace Riemann

/-- The continued Mellin formula F from (2.4). -/
noncomputable def zetaMellinFormula (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s / (s * (s - 1)) -
    1 / (s - 1) ^ (2 : ℕ) + (1 + (Real.eulerMascheroniConstant : ℂ)) / (s - 1)

/-- The continued Mellin formula Fχ from (2.4). -/
noncomputable def characterMellinFormula (χ : BundledDirichletCharacter) (s : ℂ) : ℂ :=
  let D := logDeriv (DirichletCharacter.LFunction χ.character)
  D 1 / (s - 1) - D s / (s * (s - 1))

/-- Averaging the formulas for a character and its conjugate gives the real-part transform. -/
noncomputable def realCharacterMellinFormula (χ : BundledDirichletCharacter) (s : ℂ) : ℂ :=
  (characterMellinFormula χ s + characterMellinFormula ⟨χ.modulus, χ.character⁻¹⟩ s) / 2

noncomputable def smoothedCombinationMellin {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ) (s : ℂ) : ℂ :=
  zetaMellinFormula s + ∑ i,
    (weight i : ℂ) * realCharacterMellinFormula (family i) s

/-- Every exponent above one gives a global growth majorant for the
combination of smoothed zeta and character sums. -/
theorem abs_smoothedCombination_le_rpow {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ) {a : ℝ} (ha : 1 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, |smoothedCombination family weight x| ≤ B * x ^ a := by
  obtain ⟨B, hB, hzeta⟩ := abs_smoothedZetaSum_le_rpow ha
  choose C hC hchar using fun i => norm_complexSmoothedCharacterSum_le_rpow (family i) ha
  have hsum₀ : (0 : ℝ) ≤ ∑ i, |weight i| * C i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hC i)
  refine ⟨B + ∑ i, |weight i| * C i, add_nonneg hB hsum₀, fun x hx => ?_⟩
  have hsum : |∑ i, weight i * (complexSmoothedCharacterSum (family i) x).re| ≤
      (∑ i, |weight i| * C i) * x ^ a := by
    calc
      _ ≤ ∑ i, |weight i * (complexSmoothedCharacterSum (family i) x).re| := by
        simpa only [Real.norm_eq_abs] using
          norm_sum_le (Finset.univ : Finset ι) (fun i => weight i * (complexSmoothedCharacterSum (family i) x).re)
      _ ≤ ∑ i, |weight i| * C i * x ^ a := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hchar i x hx)) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  calc
    _ ≤ |smoothedZetaSum x| + |∑ i, weight i * (complexSmoothedCharacterSum (family i) x).re| := abs_add_le _ _
    _ ≤ B * x ^ a + (∑ i, |weight i| * C i) * x ^ a := add_le_add (hzeta x hx) hsum
    _ = _ := by rw [add_mul]

theorem zetaCorrection_hasMellin (s : ℂ) (hs : 1 < s.re) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator fun x => (zetaCorrection x : ℂ))
      (-s) (-(1 / (s - 1) ^ (2 : ℕ)) + (1 + (Real.eulerMascheroniConstant : ℂ)) / (s - 1)) := by
  let linear := (Set.Ici (1 : ℝ)).indicator fun x => (x : ℂ)
  let linearLog := (Set.Ici (1 : ℝ)).indicator fun x => (x : ℂ) * (Real.log x : ℂ)
  let c : ℂ := 1 + (Real.eulerMascheroniConstant : ℂ)
  have hlinear : HasMellin linear (-s) (1 / (s - 1)) := cutoffLinear_hasMellin hs
  have hlog : HasMellin linearLog (-s) (1 / (s - 1) ^ (2 : ℕ)) := cutoffLinearLog_hasMellin hs
  have hleft := hasMellin_const_smul hlog.1 (-1 : ℂ)
  have hright := hasMellin_const_smul hlinear.1 c
  have hsum := hasMellin_add hleft.1 hright.1
  rw [hleft.2, hright.2, hlog.2, hlinear.2] at hsum
  have hfun : (fun x => (-1 : ℂ) • linearLog x + c • linear x) =
      (Set.Ici (1 : ℝ)).indicator (fun x => (zetaCorrection x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Ici (1 : ℝ) <;>
      simp [Set.indicator, hx, linear, linearLog, c, zetaCorrection, smul_eq_mul, neg_mul]
  rw [← hfun]
  simpa only [smul_eq_mul, neg_one_mul, ← mul_div_assoc, mul_one, neg_div, c] using hsum

theorem smoothedZetaSum_hasMellin (s : ℂ) (hs : 1 < s.re) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator fun x => (smoothedZetaSum x : ℂ))
      (-s) (zetaMellinFormula s) := by
  have hprime := smoothedMangoldt_hasMellin (fun _ => 1) (by simp) hs
  have hseries : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * 1) s =
      -logDeriv riemannZeta s := by
    simpa only [mul_one, logDeriv_apply, neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [hseries] at hprime
  have hcorr := zetaCorrection_hasMellin s hs
  have hfun : (fun x => (Set.Ici (1 : ℝ)).indicator (smoothedMangoldt (fun _ => 1)) x +
      (Set.Ici (1 : ℝ)).indicator (fun y => (zetaCorrection y : ℂ)) x) =
      (Set.Ici (1 : ℝ)).indicator (fun x => (smoothedZetaSum x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Ici (1 : ℝ) <;>
      simp [Set.indicator, hx, smoothedZetaSum, smoothedMangoldt_one_real]
  rw [← hfun]
  simpa only [hprime.2, hcorr.2, zetaMellinFormula, sub_eq_add_neg, add_assoc] using
    hasMellin_add hprime.1 hcorr.1

private theorem complexSmoothedCharacterSum_hasMellin_of_mangoldt (χ : BundledDirichletCharacter)
    (s : ℂ) (hs : 1 < s.re)
    (htransform :
      let coefficient := fun n : ℕ => χ.character (n : ZMod (χ.modulus : ℕ))
      HasMellin ((Set.Ici (1 : ℝ)).indicator (smoothedMangoldt coefficient)) (-s)
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * coefficient n) s /
          (s * (s - 1)))) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator (complexSmoothedCharacterSum χ))
      (-s) (characterMellinFormula χ s) := by
  let coefficient := fun n : ℕ => χ.character (n : ZMod (χ.modulus : ℕ))
  let D := logDeriv (DirichletCharacter.LFunction χ.character)
  let primeSum := (Set.Ici (1 : ℝ)).indicator (smoothedMangoldt coefficient)
  let linear := (Set.Ici (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ))
  have hseries : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * coefficient n) s = -D s := by
    have htwist := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ.character hs
    rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ.character hs,
      ← DirichletCharacter.LFunction_eq_LSeries χ.character hs] at htwist
    have hcoeff : (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * coefficient n) =
        coefficient * (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      funext n
      exact mul_comm _ _
    rw [hcoeff]
    simpa only [D, logDeriv_apply, neg_div] using htwist
  have hprime : HasMellin primeSum (-s) (-D s / (s * (s - 1))) := by
    change HasMellin primeSum (-s)
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * coefficient n) s /
        (s * (s - 1))) at htransform
    rwa [hseries] at htransform
  have hlinear : HasMellin linear (-s) (1 / (s - 1)) := cutoffLinear_hasMellin hs
  have hcorr := hasMellin_const_smul hlinear.1 (D 1)
  have hsum := hasMellin_add hprime.1 hcorr.1
  have hfun : (fun x => primeSum x + D 1 • linear x) =
      (Set.Ici (1 : ℝ)).indicator (complexSmoothedCharacterSum χ) := by
    funext x
    by_cases hx : x ∈ Set.Ici (1 : ℝ) <;>
      simp [primeSum, linear, complexSmoothedCharacterSum, smoothedTwist, D, coefficient,
        Set.indicator, hx, smul_eq_mul]
  rw [← hfun]
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  rw [hprime.2, hcorr.2, hlinear.2]
  simp only [smul_eq_mul, ← mul_div_assoc, mul_one, neg_div, characterMellinFormula, D]
  ring

/-- Apply the twisted logarithmic derivatives and average a character with its conjugate. -/
theorem realSmoothedCharacterSum_hasMellin_of_mangoldt (χ : BundledDirichletCharacter)
    (hχ : χ.character ≠ 1) (s : ℂ) (hs : 1 < s.re)
    (htransforms : ∀ ψ : DirichletCharacter ℂ (χ.modulus : ℕ),
      let coefficient := fun n : ℕ => ψ (n : ZMod (χ.modulus : ℕ))
      HasMellin ((Set.Ici (1 : ℝ)).indicator (smoothedMangoldt coefficient)) (-s)
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * coefficient n) s /
          (s * (s - 1)))) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator fun x => ((complexSmoothedCharacterSum χ x).re : ℂ))
      (-s) (realCharacterMellinFormula χ s) := by
  let χinv : BundledDirichletCharacter := ⟨χ.modulus, χ.character⁻¹⟩
  let F := (Set.Ici (1 : ℝ)).indicator (complexSmoothedCharacterSum χ)
  let G := (Set.Ici (1 : ℝ)).indicator (complexSmoothedCharacterSum χinv)
  have hF : HasMellin F (-s) (characterMellinFormula χ s) :=
    complexSmoothedCharacterSum_hasMellin_of_mangoldt χ s hs (htransforms χ.character)
  have hG : HasMellin G (-s) (characterMellinFormula χinv s) :=
    complexSmoothedCharacterSum_hasMellin_of_mangoldt χinv s hs (htransforms χ.character⁻¹)
  have hsum := hasMellin_add hF.1 hG.1
  have havg := hasMellin_const_smul hsum.1 ((2 : ℂ)⁻¹)
  rw [hsum.2, hF.2, hG.2] at havg
  have hfun : (fun x => (2 : ℂ)⁻¹ • (F x + G x)) =
      (Set.Ici (1 : ℝ)).indicator (fun x => ((complexSmoothedCharacterSum χ x).re : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Ici (1 : ℝ)
    · simp only [F, G, χinv, Set.indicator_of_mem hx, complexSmoothedCharacterSum_inv_eq_conj χ hχ,
        Complex.re_eq_add_conj, smul_eq_mul, div_eq_mul_inv]
      exact mul_comm _ _
    · simp [F, G, hx]
  rw [← hfun]
  simpa only [smul_eq_mul, realCharacterMellinFormula, χinv, div_eq_mul_inv, mul_comm] using havg

theorem realSmoothedCharacterSum_hasMellin (χ : BundledDirichletCharacter)
    (hχ : χ.character ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator fun x => ((complexSmoothedCharacterSum χ x).re : ℂ))
      (-s) (realCharacterMellinFormula χ s) :=
  realSmoothedCharacterSum_hasMellin_of_mangoldt χ hχ s hs fun ψ =>
    smoothedMangoldt_hasMellin (fun n => ψ (n : ZMod (χ.modulus : ℕ))) (fun _ => ψ.norm_le_one _) hs

private theorem hasMellin_sum {ι : Type*} (indices : Finset ι)
    (f : ι → ℝ → ℂ) (value : ι → ℂ) (s : ℂ)
    (h : ∀ i ∈ indices, HasMellin (f i) s (value i)) :
    HasMellin (fun x => ∑ i ∈ indices, f i x) s (∑ i ∈ indices, value i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [HasMellin, MellinConvergent, mellin]
  | @insert i indices hi ih =>
    have hhead := h i (Finset.mem_insert_self i indices)
    have htail := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    simpa only [hhead.2, htail.2] using hasMellin_add hhead.1 htail.1

/-- The Mellin identities (2.3)–(2.4), on the initial half-plane of convergence. -/
theorem smoothedCombination_hasMellin {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ)
    (hnontrivial : ∀ i, (family i).character ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    HasMellin ((Set.Ici (1 : ℝ)).indicator fun x => (smoothedCombination family weight x : ℂ))
      (-s) (smoothedCombinationMellin family weight s) := by
  let zetaTerm := (Set.Ici (1 : ℝ)).indicator fun x => (smoothedZetaSum x : ℂ)
  let twistTerm (i : ι) := (Set.Ici (1 : ℝ)).indicator
    fun x => ((complexSmoothedCharacterSum (family i) x).re : ℂ)
  have hterm (i : ι) := realSmoothedCharacterSum_hasMellin (family i) (hnontrivial i) s hs
  have hsum := hasMellin_sum Finset.univ (fun i x => (weight i : ℂ) * twistTerm i x)
    (fun i => (weight i : ℂ) * realCharacterMellinFormula (family i) s) (-s)
    (fun i _ => by
      simpa only [smul_eq_mul, (hterm i).2] using
        hasMellin_const_smul (hterm i).1 (weight i : ℂ))
  have hbase : HasMellin zetaTerm (-s) (zetaMellinFormula s) := smoothedZetaSum_hasMellin s hs
  have hfun : (fun x => zetaTerm x + ∑ i, (weight i : ℂ) * twistTerm i x) =
      (Set.Ici (1 : ℝ)).indicator (fun x => (smoothedCombination family weight x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Ici (1 : ℝ) <;>
      simp [zetaTerm, twistTerm, Set.indicator, hx, smoothedCombination,
        Complex.ofReal_sum, Complex.ofReal_mul]
  rw [← hfun]
  simpa only [smoothedCombinationMellin, hbase.2, hsum.2] using hasMellin_add hbase.1 hsum.1

private theorem riemannZeta_meromorphic : Meromorphic riemannZeta := by
  intro s
  by_cases hs : s = 1
  · subst s
    have heq : riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)] (fun z => (z - 1)⁻¹ + riemannZeta₀ z) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact riemannZeta_eq_inv_sub_add hz
    rw [MeromorphicAt.meromorphicAt_congr heq]
    have hζ₀ := (differentiable_riemannZeta₀.analyticAt 1).meromorphicAt
    fun_prop
  · exact (analyticOn_riemannZeta s hs).meromorphicAt

theorem smoothedCombinationMellin_meromorphic {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ)
    (hnontrivial : ∀ i, (family i).character ≠ 1) :
    Meromorphic (smoothedCombinationMellin family weight) := by
  have hzeta : Meromorphic zetaMellinFormula := by
    unfold zetaMellinFormula
    have hz := riemannZeta_meromorphic
    fun_prop
  have hchar (χ : BundledDirichletCharacter) (hχ : χ.character ≠ 1) :
      Meromorphic (characterMellinFormula χ) := by
    have hL : Meromorphic (DirichletCharacter.LFunction χ.character) :=
      fun s => ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s).meromorphicAt
    unfold characterMellinFormula
    dsimp only
    fun_prop
  intro s
  unfold smoothedCombinationMellin
  refine (hzeta s).fun_add (MeromorphicAt.fun_sum fun i _ => ?_)
  have hinv := hchar ⟨(family i).modulus, (family i).character⁻¹⟩
    (inv_ne_one.mpr (hnontrivial i))
  exact ((Meromorphic.const _).fun_mul
    (((hchar (family i) (hnontrivial i)).fun_add hinv).fun_div (Meromorphic.const _))) s

theorem smoothedCombination_has_window_mellin {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ)
    (hnontrivial : ∀ i, (family i).character ≠ 1) :
    WindowMellinData (smoothedCombination family weight)
      (smoothedCombinationMellin family weight) :=
  ⟨(continuous_smoothedCombination family weight).measurable,
    fun _ ha => abs_smoothedCombination_le_rpow family weight ha,
    smoothedCombinationMellin_meromorphic family weight hnontrivial,
    fun s hs => smoothedCombination_hasMellin family weight hnontrivial s hs⟩

private theorem dirichletLFunction_order_ne_top (χ : BundledDirichletCharacter)
    (hχ : χ.character ≠ 1) (ρ : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ.character) ρ ≠ ⊤ := by
  let L := DirichletCharacter.LFunction χ.character
  have hAnalytic (z : ℂ) : AnalyticAt ℂ L z := (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  intro htop
  have hzero : L = 0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ hAnalytic).mp htop
  have htwo : L 2 ≠ 0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.character
    (Or.inl hχ) (by norm_num)
  exact htwo (by simpa only [Pi.zero_apply] using congrFun hzero (2 : ℂ))

private theorem riemannZeta_order_ne_top {ρ : ℂ} (hρ₁ : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  let q (z : ℂ) := (z - 1)⁻¹
  have hq : AnalyticAt ℂ q ρ := by
    dsimp only [q]
    fun_prop (disch := exact sub_ne_zero.mpr hρ₁)
  have hq₀ : q ρ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hρ₁)
  have hfactor : riemannZeta =ᶠ[𝓝 ρ] q * riemannZeta₁ := by
    filter_upwards [compl_singleton_mem_nhds hρ₁] with z hz
    exact riemannZeta_eq_inv_sub_mul (show z ≠ 1 from hz)
  rw [analyticOrderAt_congr hfactor, analyticOrderAt_mul hq (differentiable_riemannZeta₁.analyticAt ρ),
    hq.analyticOrderAt_eq_zero.mpr hq₀, zero_add]
  intro htop
  have hzero : riemannZeta₁ = 0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
    differentiable_riemannZeta₁.analyticAt).mp htop
  exact one_ne_zero (by simpa only [riemannZeta₁_one, Pi.zero_apply] using congrFun hzero (1 : ℂ))

private theorem mellinFormula_principalPart_of_logDeriv {L correction : ℂ → ℂ}
    {ρ : ℂ} (hρ₀ : ρ ≠ 0) (hρ₁ : ρ ≠ 1) (hL : AnalyticAt ℂ L ρ)
    (hfinite : analyticOrderAt L ρ ≠ ⊤) (hcorr : AnalyticAt ℂ correction ρ) :
    HasPrincipalPart (fun z => correction z - logDeriv L z / (z * (z - 1))) ρ
      (-(analyticOrderNatAt L ρ : ℂ) / (ρ * (ρ - 1))) := by
  let q (z : ℂ) := -((z * (z - 1))⁻¹)
  have hq : AnalyticAt ℂ q ρ := by
    dsimp only [q]
    fun_prop (disch := exact mul_ne_zero hρ₀ (sub_ne_zero.mpr hρ₁))
  have hsum := (HasPrincipalPart.of_analytic hcorr).add
    ((hasPrincipalPart_logDeriv_of_finiteOrder hL hfinite).mul_analytic hq)
  have hresidue : 0 + q ρ * (analyticOrderNatAt L ρ : ℂ) =
      -(analyticOrderNatAt L ρ : ℂ) / (ρ * (ρ - 1)) := by
    dsimp [q]
    rw [zero_add, div_eq_mul_inv]
    ring
  rw [hresidue] at hsum
  apply hsum.congr_eventuallyEq
  exact Eventually.of_forall fun z => by dsimp only [q]; simp only [div_eq_mul_inv]; ring

private theorem characterMellinFormula_principalPart_ne_one (χ : BundledDirichletCharacter)
    (hχ : χ.character ≠ 1) {ρ : ℂ} (hρ₀ : ρ ≠ 0) (hρ₁ : ρ ≠ 1) :
    HasPrincipalPart (characterMellinFormula χ) ρ
      (-(analyticOrderNatAt (DirichletCharacter.LFunction χ.character) ρ : ℂ) / (ρ * (ρ - 1))) := by
  exact mellinFormula_principalPart_of_logDeriv
    (correction := fun z => logDeriv (DirichletCharacter.LFunction χ.character) 1 / (z - 1)) hρ₀ hρ₁
    ((DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ)
    (dirichletLFunction_order_ne_top χ hχ ρ) (by fun_prop (disch := exact sub_ne_zero.mpr hρ₁))

private theorem zetaMellinFormula_principalPart_ne_one {ρ : ℂ} (hρ₀ : ρ ≠ 0) (hρ₁ : ρ ≠ 1) :
    HasPrincipalPart zetaMellinFormula ρ (-(analyticOrderNatAt riemannZeta ρ : ℂ) / (ρ * (ρ - 1))) := by
  let correction (z : ℂ) := -(1 / (z - 1) ^ (2 : ℕ)) +
    (1 + (Real.eulerMascheroniConstant : ℂ)) / (z - 1)
  have hcorr : AnalyticAt ℂ correction ρ := by
    dsimp only [correction]
    fun_prop (disch := first | exact sub_ne_zero.mpr hρ₁ | exact pow_ne_zero _ (sub_ne_zero.mpr hρ₁))
  have hpart := mellinFormula_principalPart_of_logDeriv hρ₀ hρ₁ (analyticOn_riemannZeta ρ hρ₁)
    (riemannZeta_order_ne_top hρ₁) hcorr
  apply hpart.congr_eventuallyEq
  exact Eventually.of_forall fun z => by
    simp only [zetaMellinFormula, correction, div_eq_mul_inv]
    ring

private theorem characterMellinFormula_principalPart_at_one (χ : BundledDirichletCharacter)
    (hχ : χ.character ≠ 1) : HasPrincipalPart (characterMellinFormula χ) 1 0 := by
  let L := DirichletCharacter.LFunction χ.character
  let D := logDeriv L
  let numerator (z : ℂ) := D 1 - D z / z
  have hL : AnalyticAt ℂ L 1 := (DirichletCharacter.differentiable_LFunction hχ).analyticAt 1
  have hL₀ : L 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hD : AnalyticAt ℂ D 1 := by
    unfold D logDeriv
    exact hL.deriv.div hL hL₀
  have hnum : AnalyticAt ℂ numerator 1 := by
    dsimp only [numerator]
    fun_prop (disch := exact one_ne_zero)
  have hnum₁ : numerator 1 = 0 := by simp [numerator]
  have hpart := hasPrincipalPart_div_sub_of_analytic hnum
  rw [hnum₁] at hpart
  apply hpart.congr_eventuallyEq
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), z ≠ 0 :=
    nhdsWithin_le_nhds (compl_singleton_mem_nhds one_ne_zero)
  filter_upwards [self_mem_nhdsWithin, hnear] with z hz₁ hz₀
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr (show z ≠ 1 from hz₁)
  change D 1 / (z - 1) - D z / (z * (z - 1)) = numerator z / (z - 1)
  dsimp [numerator]
  field_simp [hz₀, hzsub]

private theorem zetaMellinFormula_principalPart_at_one : HasPrincipalPart zetaMellinFormula 1 0 := by
  let D := logDeriv riemannZeta₁
  let γ : ℂ := (Real.eulerMascheroniConstant : ℂ)
  let numerator (z : ℂ) := 1 + γ - (1 + D z) / z
  have hζ : AnalyticAt ℂ riemannZeta₁ 1 := differentiable_riemannZeta₁.analyticAt 1
  have hζ₀ : riemannZeta₁ 1 ≠ 0 := by simp
  have hD : AnalyticAt ℂ D 1 := by
    unfold D logDeriv
    exact hζ.deriv.div hζ hζ₀
  have hD₁ : D 1 = γ := by simp [D, γ, logDeriv_apply]
  have hnum : AnalyticAt ℂ numerator 1 := by
    dsimp only [numerator]
    fun_prop (disch := exact one_ne_zero)
  have hnum₁ : numerator 1 = 0 := by simp [numerator, hD₁]
  have hfactor : riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)] fun z => (z - 1) ^ (-1 : ℤ) * riemannZeta₁ z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [zpow_neg_one] using riemannZeta_eq_inv_sub_mul (show z ≠ 1 from hz)
  have hlog := logDeriv_eventuallyEq_of_factorization (-1) hζ hζ₀ hfactor
  have hpart := hasPrincipalPart_div_sub_of_analytic hnum
  rw [hnum₁] at hpart
  apply hpart.congr_eventuallyEq
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), z ≠ 0 :=
    nhdsWithin_le_nhds (compl_singleton_mem_nhds one_ne_zero)
  filter_upwards [hlog, self_mem_nhdsWithin, hnear] with z hlogz hz₁ hz₀
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr (show z ≠ 1 from hz₁)
  change logDeriv riemannZeta z = ((-1 : ℤ) : ℂ) / (z - 1) + D z at hlogz
  simp only [Int.cast_neg, Int.cast_one] at hlogz
  unfold zetaMellinFormula
  rw [hlogz]
  dsimp [numerator, γ]
  field_simp [hz₀, hzsub]
  ring

private theorem smoothedCombinationMellin_principalPart_at_one {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ)
    (hnontrivial : ∀ i, (family i).character ≠ 1) :
    HasPrincipalPart (smoothedCombinationMellin family weight) 1 0 := by
  have hchar (i : ι) : HasPrincipalPart
      (fun z => (weight i : ℂ) * realCharacterMellinFormula (family i) z) 1 0 := by
    let χ := family i
    have hF := characterMellinFormula_principalPart_at_one χ (hnontrivial i)
    have hG := characterMellinFormula_principalPart_at_one ⟨χ.modulus, χ.character⁻¹⟩
      (inv_ne_one.mpr (hnontrivial i))
    simpa only [realCharacterMellinFormula, div_eq_mul_inv, mul_comm, add_zero, mul_zero, zero_mul, χ] using
      (((hF.add hG).const_mul (2 : ℂ)⁻¹).const_mul (weight i : ℂ))
  have hsum := HasPrincipalPart.finsetSum (Finset.univ : Finset ι)
    (c := fun _ => 0) (fun i _ => hchar i)
  unfold smoothedCombinationMellin
  simpa only [Finset.sum_const_zero, add_zero] using
    zetaMellinFormula_principalPart_at_one.add hsum

/-- The principal-part coefficient of (2.5), including the removable singularity at one. -/
theorem smoothedCombination_principalPart {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ)
    (hnontrivial : ∀ i, (family i).character ≠ 1) (hweight : ∀ i, 0 < weight i)
    (ρ : ℂ) (hρ : 0 < ρ.re) :
    ∃ m : ℝ, 0 ≤ m ∧ (1 ≤ ρ.re → m = 0) ∧
      ((riemannZeta ρ = 0 ∨ ∃ i, DirichletCharacter.LFunction (family i).character ρ = 0) →
        0 < m) ∧ HasPrincipalPart (smoothedCombinationMellin family weight) ρ
          (-(m : ℂ) / (ρ * (ρ - 1))) := by
  rcases eq_or_ne ρ 1 with rfl | hρ₁
  · refine ⟨0, le_rfl, fun _ => rfl, ?_, ?_⟩
    · rintro (hz | ⟨i, hi⟩)
      · exact (riemannZeta_one_ne_zero hz).elim
      · exact (DirichletCharacter.LFunction_apply_one_ne_zero (hnontrivial i) hi).elim
    · simpa using smoothedCombinationMellin_principalPart_at_one family weight hnontrivial
  · have hρ₀ : ρ ≠ 0 := by
      intro hz
      simp [hz] at hρ
    let zetaOrder : ℝ := analyticOrderNatAt riemannZeta ρ
    let charOrder (χ : BundledDirichletCharacter) : ℝ :=
      analyticOrderNatAt (DirichletCharacter.LFunction χ.character) ρ
    let invChar (i : ι) : BundledDirichletCharacter := ⟨(family i).modulus, (family i).character⁻¹⟩
    let contribution (i : ι) := weight i * ((charOrder (family i) + charOrder (invChar i)) / 2)
    let m := zetaOrder + ∑ i, contribution i
    have hzetaOrder₀ : 0 ≤ zetaOrder := Nat.cast_nonneg _
    have hcharOrder₀ (χ : BundledDirichletCharacter) : 0 ≤ charOrder χ := Nat.cast_nonneg _
    have hcontribution₀ (i : ι) : 0 ≤ contribution i :=
      mul_nonneg (hweight i).le
        (div_nonneg (add_nonneg (hcharOrder₀ _) (hcharOrder₀ _)) (by norm_num))
    have hzetaOrder_zero : analyticOrderNatAt riemannZeta ρ = 0 ↔ riemannZeta ρ ≠ 0 :=
      analyticOrderNatAt_eq_zero_iff_of_finite (analyticOn_riemannZeta ρ hρ₁) (riemannZeta_order_ne_top hρ₁)
    have hcharOrder_zero (χ : BundledDirichletCharacter) (hχ : χ.character ≠ 1) :
        analyticOrderNatAt (DirichletCharacter.LFunction χ.character) ρ = 0 ↔
          DirichletCharacter.LFunction χ.character ρ ≠ 0 :=
      analyticOrderNatAt_eq_zero_iff_of_finite ((DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ)
        (dirichletLFunction_order_ne_top χ hχ ρ)
    have hinvNontrivial (i : ι) : (invChar i).character ≠ 1 := inv_ne_one.mpr (hnontrivial i)
    refine ⟨m, add_nonneg hzetaOrder₀ (Finset.sum_nonneg fun i _ => hcontribution₀ i), ?_, ?_, ?_⟩
    · intro hright
      have hzeta₀ : zetaOrder = 0 := by
        have h := hzetaOrder_zero.mpr (riemannZeta_ne_zero_of_one_le_re hright)
        dsimp only [zetaOrder]
        rw [h, Nat.cast_zero]
      have hchar₀ (χ : BundledDirichletCharacter) (hχ : χ.character ≠ 1) : charOrder χ = 0 := by
        have h := (hcharOrder_zero χ hχ).mpr
          (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.character (Or.inl hχ) hright)
        dsimp only [charOrder]
        rw [h, Nat.cast_zero]
      have hsum₀ : ∑ i, contribution i = 0 := Finset.sum_eq_zero fun i _ => by
        simp only [contribution, hchar₀ (family i) (hnontrivial i), hchar₀ (invChar i) (hinvNontrivial i),
          add_zero, zero_div, mul_zero]
      simp only [m, hzeta₀, hsum₀, add_zero]
    · rintro (hzeta | ⟨i, hi⟩)
      · have hpos : 0 < zetaOrder := by
          have h := Nat.pos_of_ne_zero (fun h₀ => hzetaOrder_zero.mp h₀ hzeta)
          dsimp only [zetaOrder]
          exact_mod_cast h
        exact add_pos_of_pos_of_nonneg hpos (Finset.sum_nonneg fun j _ => hcontribution₀ j)
      · have hpos : 0 < charOrder (family i) := by
          have h := Nat.pos_of_ne_zero (fun h₀ => (hcharOrder_zero (family i) (hnontrivial i)).mp h₀ hi)
          dsimp only [charOrder]
          exact_mod_cast h
        have hi' : 0 < contribution i := mul_pos (hweight i)
          (div_pos (add_pos_of_pos_of_nonneg hpos (hcharOrder₀ _)) (by norm_num))
        exact add_pos_of_nonneg_of_pos hzetaOrder₀
          (hi'.trans_le (Finset.single_le_sum (fun j _ => hcontribution₀ j) (Finset.mem_univ i)))
    · let c := -((ρ * (ρ - 1))⁻¹)
      have hzpart : HasPrincipalPart zetaMellinFormula ρ (c * (zetaOrder : ℂ)) := by
        convert zetaMellinFormula_principalPart_ne_one hρ₀ hρ₁ using 1
        simp only [c, zetaOrder, Complex.ofReal_natCast, div_eq_mul_inv]
        ring
      have hterm (i : ι) : HasPrincipalPart
          (fun z => (weight i : ℂ) * realCharacterMellinFormula (family i) z) ρ
          (c * (contribution i : ℂ)) := by
        have hF := characterMellinFormula_principalPart_ne_one (family i) (hnontrivial i) hρ₀ hρ₁
        have hG := characterMellinFormula_principalPart_ne_one (invChar i) (hinvNontrivial i) hρ₀ hρ₁
        convert (((hF.add hG).const_mul (2 : ℂ)⁻¹).const_mul (weight i : ℂ)) using 1
        · funext z
          simp only [realCharacterMellinFormula, invChar, div_eq_mul_inv]
          ring
        · simp only [c, contribution, charOrder, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
            Complex.ofReal_natCast, Complex.ofReal_ofNat]
          ring
      have hsum := HasPrincipalPart.finsetSum (Finset.univ : Finset ι) (fun i _ => hterm i)
      have hpart := hzpart.add hsum
      have hresidue : c * (zetaOrder : ℂ) + (∑ i, c * (contribution i : ℂ)) =
          -(m : ℂ) / (ρ * (ρ - 1)) := by
        rw [← Finset.mul_sum, ← mul_add]
        simp only [c, m, Complex.ofReal_add, Complex.ofReal_sum, div_eq_mul_inv]
        ring
      rw [hresidue] at hpart
      exact hpart

private theorem hasSimplePoleWithResidue_of_positive_multiplicity {A : ℂ → ℂ} {ρ : ℂ} {m : ℝ}
    (hm : 0 < m) (hρ : 0 < ρ.re) (hρlt : ρ.re < 1)
    (hpart : HasPrincipalPart A ρ (-(m : ℂ) / (ρ * (ρ - 1)))) :
    HasSimplePoleWithResidue A ρ (-(m : ℂ) / (ρ * (ρ - 1))) := by
  have hne₀ : ρ ≠ 0 := by
    intro heq
    simp [heq] at hρ
  have hne₁ : ρ ≠ 1 := by
    intro heq
    simp [heq] at hρlt
  exact ⟨div_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hm.ne'))
    (mul_ne_zero hne₀ (sub_ne_zero.mpr hne₁)), hpart⟩

/-- The pole and zero-multiplicity consequences of (2.5) used in Corollary 2.5. -/
theorem smoothedCombination_pole_data {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ)
    (hnontrivial : ∀ i, (family i).character ≠ 1) (hweight : ∀ i, 0 < weight i) :
    let A := smoothedCombinationMellin family weight
    (∀ ρ : ℂ, 0 < ρ.re → meromorphicOrderAt A ρ < 0 →
      ρ.re < 1 ∧ ∃ residue : ℂ, HasSimplePoleWithResidue A ρ residue ∧
        (ρ.im = 0 → 0 < residue.re)) ∧
    (∀ ρ : ℂ, 0 < ρ.re →
      (riemannZeta ρ = 0 ∨ ∃ i, DirichletCharacter.LFunction (family i).character ρ = 0) →
        meromorphicOrderAt A ρ < 0) := by
  dsimp only
  constructor
  · intro ρ hρ horder
    obtain ⟨m, hm₀, hmRight, _, hpart⟩ :=
      smoothedCombination_principalPart family weight hnontrivial hweight ρ hρ
    have hm : 0 < m := by
      by_contra! hmle
      have hzero : m = 0 := le_antisymm hmle hm₀
      have hz : HasPrincipalPart (smoothedCombinationMellin family weight) ρ 0 := by
        simpa [hzero] using hpart
      exact (not_lt_of_ge hz.order_nonneg_of_zero) horder
    have hρlt : ρ.re < 1 := lt_of_not_ge fun hre => hm.ne' (hmRight hre)
    refine ⟨hρlt, _, hasSimplePoleWithResidue_of_positive_multiplicity hm hρ hρlt hpart, ?_⟩
    intro hreal
    have hre : ρ = (ρ.re : ℂ) := by
      apply Complex.ext <;> simp [hreal]
    rw [hre, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      ← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_pos_of_neg_of_neg (neg_lt_zero.mpr hm)
      (mul_neg_of_pos_of_neg hρ (sub_neg.mpr hρlt))
  · intro ρ hρ hzero
    obtain ⟨m, _, hmRight, hmPositive, hpart⟩ :=
      smoothedCombination_principalPart family weight hnontrivial hweight ρ hρ
    have hm := hmPositive hzero
    have hρlt : ρ.re < 1 := lt_of_not_ge fun hre => hm.ne' (hmRight hre)
    have hpole := hasSimplePoleWithResidue_of_positive_multiplicity hm hρ hρlt hpart
    rw [hpole.order_eq_neg_one (smoothedCombinationMellin_meromorphic family weight hnontrivial ρ)]
    exact WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)

/-- Corollary 2.5, including the case of an empty family. -/
theorem nonvanishing_of_window_upper_bound {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ)
    (hnontrivial : ∀ i, (family i).character ≠ 1) (hweight : ∀ i, 0 < weight i)
    {stretch exponent : ℝ} (hstretch : 1 < stretch)
    (hexponent₀ : 0 ≤ exponent) (hexponent₁ : exponent < 1)
    (hbound : HasWindowUpperBound (smoothedCombination family weight) stretch exponent)
    (s : ℂ) (hs : exponent < s.re) :
    riemannZeta s ≠ 0 ∧ ∀ i, DirichletCharacter.LFunction (family i).character s ≠ 0 := by
  have hMellin := smoothedCombination_has_window_mellin family weight hnontrivial
  obtain ⟨hpoles, hzeros⟩ := smoothedCombination_pole_data family weight hnontrivial hweight
  have hregular := meromorphicOrder_nonneg_of_window_upper_bound hMellin hstretch
    hexponent₀ hexponent₁ (fun ρ hρ => hpoles ρ (lt_of_le_of_lt hexponent₀ hρ)) hbound hs
  have hpos : 0 < s.re := lt_of_le_of_lt hexponent₀ hs
  exact ⟨fun hz => (not_lt_of_ge hregular) (hzeros s hpos (Or.inl hz)),
    fun i hi => (not_lt_of_ge hregular) (hzeros s hpos (Or.inr ⟨i, hi⟩))⟩

/-- Cofinal windows with fixed target characters and controlled auxiliary terms. -/
def HasAdmissibleExcessWindows (point : ℝ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
    ∃ C : ℝ, 0 ≤ C ∧ ∀ target : BundledDirichletCharacter, target.character.IsPrimitive →
      ∃ (n : ℕ) (family : Fin n → BundledDirichletCharacter) (weight : Fin n → ℝ),
        (∀ i, (family i).character ≠ 1) ∧ (∀ i, 0 < weight i) ∧
        (target.character ≠ 1 → ∃ i, family i = target) ∧
        ∃ ε₀ K : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 52 ∧ 0 ≤ K ∧
          ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ lower : ℝ,
            ∃ (Y : ℝ) (nAux : ℕ) (aux : Fin nAux → BundledDirichletCharacter),
              max 1 lower ≤ Y ∧ (nAux : ℝ) ≤ K ∧
              (∀ i, (aux i).character.IsPrimitive ∧ (aux i).character ≠ 1) ∧
              ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)),
                (∀ i, ‖complexSmoothedCharacterSum (aux i) x‖ ≤ x ^ (1 / 2 + ε)) ∧
                point x ε C (smoothedCombination family weight x)
                  (∑ i, ‖complexSmoothedCharacterSum (aux i) x‖)

theorem HasAdmissibleExcessWindows.imp {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (h : HasAdmissibleExcessWindows P)
    (hpoint : ∀ x ε C main auxiliary, 0 ≤ C → P x ε C main auxiliary → Q x ε C main auxiliary) :
    HasAdmissibleExcessWindows Q := by
  obtain ⟨C, hC, hproducers⟩ := h
  refine ⟨C, hC, fun target hprimitive => ?_⟩
  obtain ⟨n, family, weight, hnontrivial, hweight, hcontains, ε₀, K, hε₀, hε₀le, hK, hwindows⟩ :=
    hproducers target hprimitive
  refine ⟨n, family, weight, hnontrivial, hweight, hcontains, ε₀, K, hε₀, hε₀le, hK,
    fun ε hε hεlt lower => ?_⟩
  obtain ⟨Y, nAux, aux, hY, hcount, hauxPrimitive, hwindow⟩ := hwindows ε hε hεlt lower
  refine ⟨Y, nAux, aux, hY, hcount, hauxPrimitive, fun x hx => ?_⟩
  obtain ⟨haux, hxw⟩ := hwindow x hx
  exact ⟨haux, hpoint _ _ _ _ _ hC hxw⟩

/-- The cofinal construction in §18 and the identification of its sums in §6.3,
using the D6 bound on the rescaled windows. -/
theorem exists_finite_excess_windows_of_rescaled_selmer
    (hSelmer : HasRescaledSelmerWindowBound numberFieldSelmerLengths) :
    HasAdmissibleExcessWindows HasFiniteExcessWitness := by
  obtain ⟨C, _, _, hC, huniform⟩ := uniform_chain_records_on_prepared_hosts
  have hprepared := exists_prepared_excess_windows_of_rescaled_selmer hSelmer hC
  refine ⟨C, hC, fun target hprimitive => ?_⟩
  obtain ⟨n, family, weight, hnontrivial, hweight, hcontains, ε₀, K, hε₀, hε₀le, hK, hwindows⟩ :=
    hprepared target hprimitive
  obtain ⟨ε₁, hε₁, hchains⟩ := huniform target hprimitive
  refine ⟨n, family, weight, hnontrivial, hweight, hcontains, min ε₀ ε₁, K, lt_min hε₀ hε₁,
    (min_le_left _ _).trans hε₀le, hK, fun ε hε hεlt lower => ?_⟩
  obtain ⟨J, hJ, hcofinal⟩ := hwindows ε hε (hεlt.trans_le (min_le_left _ _))
  obtain ⟨c, x₁, hc, _, _, hcexp, hchain⟩ :=
    hchains ε hε (hεlt.trans_le (min_le_right _ _)) J hJ
  obtain ⟨base, Y, q, d, e, nAux, aux, hY, hbase₀, hbaseY, hbase_width, hpair, hcount,
    hauxPrimitive, hwindow⟩ := hcofinal (max lower x₁)
  have hlowerY : lower ≤ Y := (le_max_left lower x₁).trans ((le_max_right _ _).trans hY)
  have hx₁Y : x₁ ≤ Y := (le_max_right lower x₁).trans ((le_max_right _ _).trans hY)
  refine ⟨Y, nAux, aux, max_le ((le_max_left _ _).trans hY) hlowerY, hcount,
    hauxPrimitive, fun x hx => ?_⟩
  obtain ⟨haux, hhost⟩ := hwindow x hx
  refine ⟨haux, ?_⟩
  obtain ⟨H, group, finite, a, hadmissible, hrecords⟩ :=
    hchain base Y hbase₀ hbaseY hbase_width q d hpair (e x) x (hx₁Y.trans hx.1) hx _ _ hhost
  let localGroup : AddCommGroup H := group
  let localFinite : Fintype H := finite
  exact admissibleExcess_of_hostChainRecords hadmissible hc hcexp hrecords

theorem exists_finite_excess_windows_of_selmer
    (hSelmer : HasSelmerWindowBound numberFieldSelmerLengths) :
    HasAdmissibleExcessWindows HasFiniteExcessWitness :=
  exists_finite_excess_windows_of_rescaled_selmer hSelmer.to_rescaled

theorem exists_finite_excess_windows : HasAdmissibleExcessWindows HasFiniteExcessWitness :=
  exists_finite_excess_windows_of_selmer numberField_selmer_window_bound

/-- Corollary 4.4 on the admissible windows of §6, before absorbing auxiliary characters. -/
theorem exists_smoothed_excess_windows :
    HasAdmissibleExcessWindows (fun x ε C main auxiliary =>
      main ≤ x ^ (1 / 2 + (C + 3) * ε) + auxiliary) :=
  exists_finite_excess_windows.imp fun _ _ _ _ _ hC h => h.combination_le hC

/-- The cofinal window estimate with the exponent of (6.1). -/
theorem exists_smoothed_window_bounds_with_slack (target : BundledDirichletCharacter)
    (hprimitive : target.character.IsPrimitive) :
    ∃ (n : ℕ) (family : Fin n → BundledDirichletCharacter) (weight : Fin n → ℝ),
      (∀ i, (family i).character ≠ 1) ∧ (∀ i, 0 < weight i) ∧
      (target.character ≠ 1 → ∃ i, family i = target) ∧
      ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          HasWindowUpperBound (smoothedCombination family weight) (3 / 2) (1 / 2 + (C + 4) * ε) := by
  obtain ⟨C, hC, htarget⟩ := exists_smoothed_excess_windows
  obtain ⟨n, family, weight, hnontrivial, hweight, hcontains, ε₀, K, hε₀, _, hK, hwindows⟩ :=
    htarget target hprimitive
  refine ⟨n, family, weight, hnontrivial, hweight, hcontains, C, ε₀, hC, hε₀,
    fun ε hε hεlt => ⟨1 + K, by linarith, fun lower => ?_⟩⟩
  obtain ⟨Y, nAux, aux, hY, hcount, _, hwindow⟩ := hwindows ε hε hεlt lower
  refine ⟨Y, hY, fun x hx => ?_⟩
  obtain ⟨haux, hcombination⟩ := hwindow x hx
  have hx₁ : 1 ≤ x := (le_max_left 1 lower).trans (hY.trans hx.1)
  let exponent : ℝ := 1 / 2 + (C + 4) * ε
  have hmain : x ^ (1 / 2 + (C + 3) * ε) ≤ x ^ exponent := by
    apply Real.rpow_le_rpow_of_exponent_le hx₁
    dsimp [exponent]
    have hproduct : (C + 3) * ε ≤ (C + 4) * ε :=
      mul_le_mul_of_nonneg_right (by linarith) hε.le
    linarith
  have hauxExponent : x ^ (1 / 2 + ε) ≤ x ^ exponent := by
    apply Real.rpow_le_rpow_of_exponent_le hx₁
    dsimp [exponent]
    have hproduct : ε ≤ (C + 4) * ε := le_mul_of_one_le_left hε.le (by linarith)
    linarith
  have hauxSum : (∑ i, ‖complexSmoothedCharacterSum (aux i) x‖) ≤ K * x ^ exponent := by
    calc
      _ ≤ ∑ _ : Fin nAux, x ^ exponent := Finset.sum_le_sum fun i _ =>
        (haux i).trans hauxExponent
      _ = (nAux : ℝ) * x ^ exponent := by
        simp [nsmul_eq_mul]
      _ ≤ K * x ^ exponent := mul_le_mul_of_nonneg_right hcount
        (Real.rpow_nonneg (zero_le_one.trans hx₁) _)
  calc
    smoothedCombination family weight x ≤ _ := hcombination
    _ ≤ x ^ exponent + K * x ^ exponent := add_le_add hmain hauxSum
    _ = (1 + K) * x ^ exponent := by rw [add_mul, one_mul]

/-- Specialize (6.1) to any exponent between one half and one. -/
theorem exists_smoothed_window_bounds (target : BundledDirichletCharacter)
    (hprimitive : target.character.IsPrimitive) :
    ∃ (n : ℕ) (family : Fin n → BundledDirichletCharacter) (weight : Fin n → ℝ),
      (∀ i, (family i).character ≠ 1) ∧ (∀ i, 0 < weight i) ∧
      (target.character ≠ 1 → ∃ i, family i = target) ∧
      ∀ exponent : ℝ, 1 / 2 < exponent → exponent < 1 →
        HasWindowUpperBound (smoothedCombination family weight) (3 / 2) exponent := by
  obtain ⟨n, family, weight, hnontrivial, hweight, hcontains, C, ε₀, hC, hε₀, hwindows⟩ :=
    exists_smoothed_window_bounds_with_slack target hprimitive
  refine ⟨n, family, weight, hnontrivial, hweight, hcontains, fun exponent hhalf _ => ?_⟩
  let ε := min (ε₀ / 2) ((exponent - 1 / 2) / (C + 4))
  have hC₄ : 0 < C + 4 := by linarith
  have hε : 0 < ε := lt_min (by linarith) (div_pos (sub_pos.mpr hhalf) hC₄)
  have hεlt : ε < ε₀ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hslack : ε * (C + 4) ≤ exponent - 1 / 2 :=
    (le_div_iff₀ hC₄).mp (min_le_right _ _)
  apply (hwindows ε hε hεlt).mono_exponent
  linarith [mul_comm (C + 4) ε]

theorem nonvanishing_right_of_half_of_windows {ι : Type*} [Fintype ι]
    (family : ι → BundledDirichletCharacter) (weight : ι → ℝ)
    (hnontrivial : ∀ i, (family i).character ≠ 1) (hweight : ∀ i, 0 < weight i)
    (hwindows : ∀ exponent : ℝ, 1 / 2 < exponent → exponent < 1 →
      HasWindowUpperBound (smoothedCombination family weight) (3 / 2) exponent)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    riemannZeta s ≠ 0 ∧ ∀ i, DirichletCharacter.LFunction (family i).character s ≠ 0 := by
  let exponent : ℝ := (1 / 2 + min 1 s.re) / 2
  have hmin : 1 / 2 < min (1 : ℝ) s.re := lt_min (by norm_num) hs
  have hhalf : 1 / 2 < exponent := by
    dsimp [exponent]
    linarith
  have hexponent₁ : exponent < 1 := by
    dsimp [exponent]
    linarith [min_le_left (1 : ℝ) s.re]
  have hrefined : exponent < s.re := by
    dsimp [exponent]
    linarith [min_le_right (1 : ℝ) s.re]
  exact nonvanishing_of_window_upper_bound family weight hnontrivial hweight
    (by norm_num) (by linarith) hexponent₁ (hwindows exponent hhalf hexponent₁) s hrefined

theorem zeta_and_primitive_nonvanishing :
    ZetaNonvanishingRightOfHalf ∧ PrimitiveDirichletLNonvanishingRightOfHalf := by
  have hζ : ZetaNonvanishingRightOfHalf := by
    let target : BundledDirichletCharacter := ⟨1, 1⟩
    obtain ⟨_, family, weight, hnontrivial, hweight, _, hwindows⟩ :=
      exists_smoothed_window_bounds target DirichletCharacter.isPrimitive_one_level_one
    intro s hs
    exact (nonvanishing_right_of_half_of_windows family weight hnontrivial hweight hwindows s hs).1
  refine ⟨hζ, ?_⟩
  intro N _ χ hprimitive s hs _
  by_cases htrivial : χ = 1
  · have hN : N = 1 := by
      have hχ := (DirichletCharacter.isPrimitive_def χ).mp hprimitive
      simpa [htrivial, DirichletCharacter.conductor_one] using hχ.symm
    subst N
    rw [DirichletCharacter.LFunction_modOne_eq]
    exact hζ s hs
  · let target : BundledDirichletCharacter := ⟨⟨N, Nat.pos_of_ne_zero (NeZero.ne N)⟩, χ⟩
    obtain ⟨_, family, weight, hnontrivial, hweight, hcontains, hwindows⟩ :=
      exists_smoothed_window_bounds target hprimitive
    obtain ⟨i, hi⟩ := hcontains htrivial
    have h := (nonvanishing_right_of_half_of_windows family weight hnontrivial hweight hwindows s hs).2 i
    rw [hi] at h
    exact h

end Riemann
