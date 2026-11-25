module

public import Riemann.SelmerExceptionalBounds
public import Utilities.NumberFieldClassBounds

@[expose] public section

open Utilities

namespace Riemann

/-- The Kummer count for the first torsion layer of the relaxed restriction
kernel, using the field obtained by adjoining a primitive ℓth root of unity. -/
def HasSelmerKummerTorsionCardBound : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i : ℕ, 1 ≤ i →
      let F := selmerHostField target e q d
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ℓ ∣ Module.finrank ℚ F →
        let V := numberFieldRelaxedSelmerKernel F ℓ i
        let W := Submodule.torsionBy ℤ_[ℓ] V (ℓ : ℤ_[ℓ])
        let F' := CyclotomicField ℓ F
        letI := CyclotomicField.isCyclotomicExtension ℓ F
        letI := IsCyclotomicExtension.numberField {ℓ} F F'
        Finite W ∧ Nat.card W ≤
          ℓ ^ (2 * Module.finrank ℚ F') * NumberField.classNumber F'

/-- The numerical rank bound in the exceptional-prime estimate follows from
the Kummer count once the degree and class number have been bounded. -/
theorem selmerRelaxedTorsionRankEstimate_of_kummerCard
    (h : HasSelmerKummerTorsionCardBound) : HasSelmerRelaxedTorsionRankEstimate := by
  intro target hprimitive e q d he hpair i hi
  dsimp only
  intro ℓ _ hodd hdiv
  let F := selmerHostField target e q d
  let f := selmerHostConductor target e q d
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let F' := CyclotomicField ℓ F
  let _ : IsCyclotomicExtension {ℓ} F F' := CyclotomicField.isCyclotomicExtension ℓ F
  let _ : NumberField F' := IsCyclotomicExtension.numberField {ℓ} F F'
  let V := numberFieldRelaxedSelmerKernel F ℓ i
  let W := Submodule.torsionBy ℤ_[ℓ] V (ℓ : ℤ_[ℓ])
  obtain ⟨hW, hcard⟩ := h target hprimitive e q d he hpair i hi ℓ hodd hdiv
  let _ : Finite W := hW
  obtain ⟨hdegree, hlog⟩ := cyclotomicField_prime_degree_log_classNumber_le F ℓ f
    (selmerHostConductorEmbedding target e q d)
  have hlog₀ : 0 ≤ Real.log ((ℓ : ℝ) * f) := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast (Fact.out : ℓ.Prime).one_le)
      (by exact_mod_cast NeZero.pos f)
  refine exists_padic_torsionRank_of_cardBound ℓ W (NeZero.pos f)
    (NumberField.classNumber_pos F') hdegree hcard ?_
  exact hlog.trans (by nlinarith [mul_nonneg (Nat.cast_nonneg (Module.finrank ℚ F')) hlog₀])

/-- The minus estimate reduces to the Bernoulli comparison, the
Stickelberger annihilator and the Kummer count of relaxed torsion classes. -/
theorem numberField_selmer_minus_estimate_of_comparison_exponent_kummer
    (hBernoulli : HasSelmerBernoulliValuationComparison)
    (hExp : HasSelmerStickelbergerExponentEstimate)
    (hKummer : HasSelmerKummerTorsionCardBound) : HasSelmerMinusEstimate :=
  numberField_selmer_minus_estimate_of_comparison_exponent_rank hBernoulli hExp
    (selmerRelaxedTorsionRankEstimate_of_kummerCard hKummer)

end Riemann
