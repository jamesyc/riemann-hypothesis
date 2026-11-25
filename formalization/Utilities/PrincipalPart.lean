module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Topology.DiscreteSubset

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace Utilities

/-- A possible simple principal part, stated on a punctured neighborhood. -/
def HasPrincipalPart (A : ℂ → ℂ) (ρ residue : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
    A =ᶠ[𝓝[≠] ρ] (fun s => residue / (s - ρ) + g s)

def HasSimplePoleWithResidue (A : ℂ → ℂ) (ρ residue : ℂ) : Prop :=
  residue ≠ 0 ∧ HasPrincipalPart A ρ residue

theorem HasPrincipalPart.congr_eventuallyEq {f g : ℂ → ℂ} {ρ c : ℂ}
    (h : HasPrincipalPart f ρ c) (heq : g =ᶠ[𝓝[≠] ρ] f) : HasPrincipalPart g ρ c := by
  obtain ⟨u, hu, hfu⟩ := h
  exact ⟨u, hu, heq.trans hfu⟩

theorem HasPrincipalPart.of_analytic {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) :
    HasPrincipalPart f ρ 0 := by
  refine ⟨f, hf, Eventually.of_forall fun z => ?_⟩
  change f z = 0 / (z - ρ) + f z
  rw [zero_div, zero_add]

theorem HasPrincipalPart.add {f g : ℂ → ℂ} {ρ a b : ℂ}
    (hf : HasPrincipalPart f ρ a) (hg : HasPrincipalPart g ρ b) :
    HasPrincipalPart (fun z => f z + g z) ρ (a + b) := by
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨v, hv, hgv⟩ := hg
  refine ⟨fun z => u z + v z, by fun_prop, ?_⟩
  filter_upwards [hfu, hgv] with z hzf hzg
  rw [hzf, hzg, add_div]
  ring

/-- Multiplying by an analytic function multiplies the residue by its value at the pole. -/
theorem HasPrincipalPart.mul_analytic {f q : ℂ → ℂ} {ρ c : ℂ}
    (hf : HasPrincipalPart f ρ c) (hq : AnalyticAt ℂ q ρ) :
    HasPrincipalPart (fun z => q z * f z) ρ (q ρ * c) := by
  obtain ⟨g, hg, hfg⟩ := hf
  have hqSlope := hq.dslope ρ
  refine ⟨fun z => q z * g z + c * dslope q ρ z, by fun_prop, ?_⟩
  filter_upwards [hfg, self_mem_nhdsWithin] with z hfz hz
  have hne : z ≠ ρ := hz
  change q z * f z = q ρ * c / (z - ρ) + (q z * g z + c * dslope q ρ z)
  rw [hfz, dslope_of_ne q hne, slope_def_field]
  ring

theorem HasPrincipalPart.const_mul {f : ℂ → ℂ} {ρ c : ℂ} (h : HasPrincipalPart f ρ c) (a : ℂ) :
    HasPrincipalPart (fun z => a * f z) ρ (a * c) :=
  h.mul_analytic (q := fun _ => a) analyticAt_const

theorem HasPrincipalPart.finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    {ρ : ℂ} {c : ι → ℂ} (h : ∀ i ∈ s, HasPrincipalPart (f i) ρ (c i)) :
    HasPrincipalPart (fun z => ∑ i ∈ s, f i z) ρ (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (HasPrincipalPart.of_analytic (ρ := ρ) (f := fun _ : ℂ => 0) analyticAt_const)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Dividing an analytic numerator by the local coordinate introduces at most a simple pole. -/
theorem hasPrincipalPart_div_sub_of_analytic {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) :
    HasPrincipalPart (fun z => f z / (z - ρ)) ρ (f ρ) := by
  refine ⟨dslope f ρ, hf.dslope ρ, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z ≠ ρ := hz
  change f z / (z - ρ) = f ρ / (z - ρ) + dslope f ρ z
  rw [dslope_of_ne f hne, slope_def_field, ← add_div]
  ring

/-- The logarithmic derivative of `(z - ρ)^n` times an analytic unit has residue `n`. -/
theorem logDeriv_eventuallyEq_of_factorization {f g : ℂ → ℂ} {ρ : ℂ} (n : ℤ)
    (hg : AnalyticAt ℂ g ρ) (hg₀ : g ρ ≠ 0)
    (hfg : f =ᶠ[𝓝[≠] ρ] fun z => (z - ρ) ^ n * g z) :
    logDeriv f =ᶠ[𝓝[≠] ρ] fun z => (n : ℂ) / (z - ρ) + logDeriv g z := by
  apply (logDeriv_congr_nhdsNE hfg).trans
  filter_upwards [hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hg₀).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hgz hgz₀ hz
  have hsub : z - ρ ≠ 0 := sub_ne_zero.mpr (show z ≠ ρ from hz)
  have hlinear := (hasDerivAt_id' z).sub_const ρ
  have hpow₀ : (z - ρ) ^ n ≠ 0 := zpow_ne_zero n hsub
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (w - ρ) ^ n) z := by
    fun_prop (disch := exact Or.inl hsub)
  change logDeriv (fun w => (w - ρ) ^ n * g w) z = (n : ℂ) / (z - ρ) + logDeriv g z
  rw [logDeriv_fun_mul z hpow₀ hgz₀ hpow hgz.differentiableAt,
    logDeriv_fun_zpow hlinear.differentiableAt n,
    logDeriv_apply (fun w : ℂ => w - ρ) z, hlinear.deriv, mul_one_div]

theorem hasPrincipalPart_logDeriv_of_factorization {f g : ℂ → ℂ} {ρ : ℂ} (n : ℤ)
    (hg : AnalyticAt ℂ g ρ) (hg₀ : g ρ ≠ 0)
    (hfg : f =ᶠ[𝓝[≠] ρ] fun z => (z - ρ) ^ n * g z) :
    HasPrincipalPart (logDeriv f) ρ (n : ℂ) := by
  have hlog : AnalyticAt ℂ (logDeriv g) ρ := by
    unfold logDeriv
    exact hg.deriv.div hg hg₀
  exact ⟨logDeriv g, hlog, logDeriv_eventuallyEq_of_factorization n hg hg₀ hfg⟩

theorem hasPrincipalPart_logDeriv_of_finiteOrder {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (hfinite : analyticOrderAt f ρ ≠ ⊤) :
    HasPrincipalPart (logDeriv f) ρ (analyticOrderNatAt f ρ : ℂ) := by
  obtain ⟨g, hg, hg₀, heq⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  have hfactor : f =ᶠ[𝓝[≠] ρ] fun z => (z - ρ) ^ (analyticOrderNatAt f ρ : ℤ) * g z := by
    simpa only [zpow_natCast, smul_eq_mul] using heq.filter_mono nhdsWithin_le_nhds
  simpa only [Int.cast_natCast] using
    hasPrincipalPart_logDeriv_of_factorization (analyticOrderNatAt f ρ : ℤ) hg hg₀ hfactor

theorem analyticOrderNatAt_eq_zero_iff_of_finite {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (hfinite : analyticOrderAt f ρ ≠ ⊤) :
    analyticOrderNatAt f ρ = 0 ↔ f ρ ≠ 0 := by
  constructor
  · intro hzero
    apply hf.analyticOrderAt_eq_zero.mp
    rw [← Nat.cast_analyticOrderNatAt hfinite, hzero, ENat.natCast_zero]
  · intro hne
    simpa only [analyticOrderNatAt, ENat.toNat_zero] using
      congrArg ENat.toNat (hf.analyticOrderAt_eq_zero.mpr hne)

theorem HasPrincipalPart.order_nonneg_of_zero {A : ℂ → ℂ} {ρ : ℂ}
    (h : HasPrincipalPart A ρ 0) : 0 ≤ meromorphicOrderAt A ρ := by
  obtain ⟨g, hg, heq⟩ := h
  have hlocal : A =ᶠ[𝓝[≠] ρ] g := by
    filter_upwards [heq] with s hs
    simpa only [zero_div, zero_add] using hs
  rw [meromorphicOrderAt_congr hlocal]
  exact hg.meromorphicOrderAt_nonneg

/-- A meromorphic function of nonnegative order has a removable local representative. -/
theorem hasPrincipalPart_zero_of_order_nonneg {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ) (ho : 0 ≤ meromorphicOrderAt f ρ) : HasPrincipalPart f ρ 0 :=
  (HasPrincipalPart.of_analytic (hf.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp ho)).congr_eventuallyEq
    hf.eq_nhdsNE_toMeromorphicNFAt

/-- Fill all removable singularities of a meromorphic function on a set.
The extension agrees in an ordinary neighborhood wherever the original function was analytic. -/
theorem exists_analytic_extension_of_removable_principalParts {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hrem : ∀ z ∈ U, HasPrincipalPart f z 0) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q U ∧
      (∀ z ∈ U, Q =ᶠ[𝓝[≠] z] f) ∧
      (∀ z ∈ U, AnalyticAt ℂ f z → Q =ᶠ[𝓝 z] f) := by
  let Q := toMeromorphicNFOn f U
  have hNF : MeromorphicNFOn Q U := meromorphicNFOn_toMeromorphicNFOn f U
  refine ⟨Q, ?_, fun _ hz => hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz, ?_⟩
  · intro z hz
    apply (hNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    change 0 ≤ meromorphicOrderAt (toMeromorphicNFOn f U) z
    rw [meromorphicOrderAt_toMeromorphicNFOn hf hz]
    exact (hrem z hz).order_nonneg_of_zero
  · intro z hz hzAnalytic
    exact ((hNF hz).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hzAnalytic.meromorphicNFAt).mp
      (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz)

/-- Removing the principal parts at a finite set containing all poles on `U`
leaves a function with an analytic representative on `U`. -/
theorem exists_analytic_remainder_after_subtracting_principalParts {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hparts : ∀ p ∈ poles, HasPrincipalPart f p (residue p))
    (hcover : ∀ z ∈ U, meromorphicOrderAt f z < 0 → z ∈ poles) :
    let remainder (z : ℂ) := f z - ∑ p ∈ poles, residue p / (z - p)
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q U ∧
      (∀ z ∈ U, Q =ᶠ[𝓝[≠] z] remainder) ∧
      (∀ z ∈ U, AnalyticAt ℂ f z → z ∉ poles → Q =ᶠ[𝓝 z] remainder) := by
  classical
  let remainder (z : ℂ) := f z - ∑ p ∈ poles, residue p / (z - p)
  have hregular (s : Finset ℂ) {z : ℂ} (hz : z ∉ s) :
      AnalyticAt ℂ (fun w => ∑ p ∈ s, residue p / (w - p)) z := by
    refine Finset.analyticAt_fun_sum s fun p hp => ?_
    have hpz : z ≠ p := fun h => hz (h.symm ▸ hp)
    fun_prop (disch := exact sub_ne_zero.mpr hpz)
  have hmer : MeromorphicOn remainder U := by
    intro z hz
    exact (hf z hz).fun_sub (MeromorphicAt.fun_sum fun p _ => by fun_prop)
  have hrem (z : ℂ) (hz : z ∈ U) : HasPrincipalPart remainder z 0 := by
    by_cases hzp : z ∈ poles
    · obtain ⟨g, hg, hfg⟩ := hparts z hzp
      have hp := hregular (poles.erase z) (by simp : z ∉ poles.erase z)
      refine ⟨fun w => g w - ∑ p ∈ poles.erase z, residue p / (w - p), by fun_prop, ?_⟩
      filter_upwards [hfg] with w hw
      change f w - (∑ p ∈ poles, residue p / (w - p)) =
        0 / (w - z) + (g w - ∑ p ∈ poles.erase z, residue p / (w - p))
      rw [hw, ← Finset.sum_erase_add _ _ hzp, zero_div, zero_add]
      ring
    · have ho : 0 ≤ meromorphicOrderAt f z := le_of_not_gt fun hp => hzp (hcover z hz hp)
      have hzero := (hasPrincipalPart_zero_of_order_nonneg (hf z hz) ho).add
        (HasPrincipalPart.of_analytic (hregular poles hzp).neg)
      simp only [add_zero] at hzero
      exact hzero.congr_eventuallyEq (Eventually.of_forall fun w => by
        simp only [remainder, sub_eq_add_neg, Pi.neg_apply])
  obtain ⟨Q, hQ, hnear, hsame⟩ := exists_analytic_extension_of_removable_principalParts hmer hrem
  exact ⟨Q, hQ, hnear, fun z hz hfz hzp => hsame z hz (hfz.fun_sub (hregular poles hzp))⟩

theorem finite_poles_inter_isCompact {f : ℂ → ℂ} (hf : Meromorphic f) {K : Set ℂ}
    (hK : IsCompact K) : ({z | meromorphicOrderAt f z < 0} ∩ K).Finite := by
  let P : Set ℂ := {z | meromorphicOrderAt f z < 0}
  have hP : Pᶜ ∈ Filter.codiscrete ℂ := by
    rw [mem_codiscrete_iff_forall_mem_nhdsNE]
    intro z
    filter_upwards [(hf z).eventually_analyticAt] with w hw
    exact not_lt_of_ge hw.meromorphicOrderAt_nonneg
  have hPK : Pᶜ ∈ Filter.codiscreteWithin K :=
    ((codiscreteWithin_le_codiscrete_inf_principal K).trans inf_le_left) hP
  simpa only [Set.sdiff_eq, compl_compl, Set.inter_comm] using hK.finite_sdiff_of_mem_codiscreteWithin hPK

theorem HasSimplePoleWithResidue.order_eq_neg_one {A : ℂ → ℂ} {ρ residue : ℂ}
    (h : HasSimplePoleWithResidue A ρ residue) (hA : MeromorphicAt A ρ) :
    meromorphicOrderAt A ρ = -1 := by
  obtain ⟨hresidue, g, hg, heq⟩ := h
  apply (meromorphicOrderAt_eq_int_iff (n := -1) hA).mpr
  refine ⟨fun s => residue + (s - ρ) * g s, by fun_prop, by simpa, ?_⟩
  filter_upwards [heq, self_mem_nhdsWithin] with s hs hne
  have hsub : s - ρ ≠ 0 := sub_ne_zero.mpr hne
  rw [hs, zpow_neg_one, smul_eq_mul]
  field_simp

end Utilities
