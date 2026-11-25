module

public import Utilities.PrincipalPart
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.RCLike

@[expose] public section

open Filter
open scoped ComplexConjugate Topology

namespace Utilities

private theorem tendsto_conj_nhds_reflected (ρ : ℂ) :
    Tendsto (conj : ℂ → ℂ) (𝓝 (conj ρ)) (𝓝 ρ) := by
  simpa only [Complex.conj_conj] using (Complex.continuous_conj.continuousAt (x := conj ρ)).tendsto

theorem tendsto_conj_nhdsNE_reflected (ρ : ℂ) :
    Tendsto (conj : ℂ → ℂ) (𝓝[≠] (conj ρ)) (𝓝[≠] ρ) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(tendsto_conj_nhds_reflected ρ).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  change conj z ≠ ρ
  intro heq
  exact (show z ≠ conj ρ from hz) (by
    simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ) heq)

theorem analyticAt_conj_conj {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) :
    AnalyticAt ℂ (conj ∘ f ∘ conj) (conj ρ) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  exact ((tendsto_conj_nhds_reflected ρ).eventually hf).mono fun _ hz =>
    differentiableAt_conj_conj_iff.mpr hz

/-- Reflection across the real axis preserves meromorphicity and the local order. -/
theorem meromorphicAt_conj_conj_and_order {f : ℂ → ℂ} {ρ : ℂ} (hf : MeromorphicAt f ρ) :
    MeromorphicAt (conj ∘ f ∘ conj) (conj ρ) ∧
      meromorphicOrderAt (conj ∘ f ∘ conj) (conj ρ) = meromorphicOrderAt f ρ := by
  by_cases htop : meromorphicOrderAt f ρ = ⊤
  · have hzero : (conj ∘ f ∘ conj) =ᶠ[𝓝[≠] (conj ρ)] 0 := by
      filter_upwards [(tendsto_conj_nhdsNE_reflected ρ).eventually (meromorphicOrderAt_eq_top_iff.mp htop)]
        with z hz
      simp only [Function.comp_apply, hz, map_zero, Pi.zero_apply]
    refine ⟨(show AnalyticAt ℂ (0 : ℂ → ℂ) (conj ρ) from analyticAt_const).meromorphicAt.congr hzero.symm, ?_⟩
    rw [htop, meromorphicOrderAt_eq_top_iff]
    exact hzero
  · lift meromorphicOrderAt f ρ to ℤ using htop with n hn
    obtain ⟨g, hg, hg₀, heq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
    have hg' := analyticAt_conj_conj hg
    have hg₀' : (conj ∘ g ∘ conj) (conj ρ) ≠ 0 := by
      intro h
      apply hg₀
      apply (starRingEnd ℂ).injective
      simpa only [Function.comp_apply, Complex.conj_conj, map_zero] using h
    have hfactor : (conj ∘ f ∘ conj) =ᶠ[𝓝[≠] (conj ρ)] fun z => (z - conj ρ) ^ n • (conj ∘ g ∘ conj) z := by
      filter_upwards [(tendsto_conj_nhdsNE_reflected ρ).eventually heq] with z hz
      change conj (f (conj z)) = (z - conj ρ) ^ n • conj (g (conj z))
      simp only [hz, smul_eq_mul, map_mul, map_zpow₀, map_sub, Complex.conj_conj]
    have hmer := MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨n, _, hg', hfactor⟩
    exact ⟨hmer, (meromorphicOrderAt_eq_int_iff hmer).mpr ⟨_, hg', hg₀', hfactor⟩⟩

theorem meromorphic_conj_conj {f : ℂ → ℂ} (hf : Meromorphic f) : Meromorphic (conj ∘ f ∘ conj) := by
  intro z
  simpa only [Complex.conj_conj] using (meromorphicAt_conj_conj_and_order (hf (conj z))).1

theorem hasPrincipalPart_conj_conj {f : ℂ → ℂ} {ρ residue : ℂ} (hf : HasPrincipalPart f ρ residue) :
    HasPrincipalPart (conj ∘ f ∘ conj) (conj ρ) (conj residue) := by
  obtain ⟨g, hg, heq⟩ := hf
  refine ⟨conj ∘ g ∘ conj, analyticAt_conj_conj hg, ?_⟩
  filter_upwards [(tendsto_conj_nhdsNE_reflected ρ).eventually heq] with z hz
  change conj (f (conj z)) = conj residue / (z - conj ρ) + conj (g (conj z))
  simp only [hz, map_add, map_div₀, map_sub, Complex.conj_conj]

/-- Local equality of meromorphic functions implies equality of their
punctured germs everywhere on the complex plane. -/
theorem meromorphic_eventuallyEq_nhdsNE_of_eq_nhds {f g : ℂ → ℂ} {x : ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g) (heq : f =ᶠ[𝓝 x] g) (z : ℂ) :
    f =ᶠ[𝓝[≠] z] g := by
  have htop : meromorphicOrderAt (f - g) x = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [heq.filter_mono nhdsWithin_le_nhds] with y hy
    simp only [Pi.sub_apply, hy, sub_self]
  have hz := ((hf.sub hg).exists_meromorphicOrderAt_eq_top_iff_forall.mp ⟨x, htop⟩) z
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hz] with y hy
  exact sub_eq_zero.mp hy

end Utilities
