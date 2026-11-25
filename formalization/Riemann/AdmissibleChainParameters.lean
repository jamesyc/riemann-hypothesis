module

public import Riemann.AdmissibleExcess
public import Riemann.ChainParameters
import Riemann.ChainFrameSizes

@[expose] public section

open Filter Utilities

namespace Riemann

/-- Select the manuscript's ranks on the same prepared field and restrict its
D6 bound to the twists actually needed by the theta chain. -/
theorem eventually_admissibleHostChainParameters {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∀ {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
      {H : Type} [AddCommGroup H] [Fintype H]
      {a : AdmissibleExcessData target e q d H} {C main auxiliary : ℝ},
      AdmissibleExcessConditions a x ε C main auxiliary →
      ∃ m k tr : ℕ, ChainRankBounds x ε m k ∧
        ExcessSizeBounds { a.averaging.budget with steps := m, k := (k : ℝ) } x ε ∧
        ChainTwistRankBounds x ε (Fintype.card H) m k tr ∧
        SelmerLengthBound (numberFieldSelmerLengths (ExcessHost target e q d))
          tr (Real.exp (x ^ ε / 2)) := by
  filter_upwards [eventually_exists_chainExcessBudget hε hsmall,
    eventually_exists_chainTwistRank hε hsmall] with x hbudget htwists
  intro target e q d H _ _ a C main auxiliary ha
  obtain ⟨m, k, hranks, hsizes⟩ := hbudget (Fintype.card H) a.averaging.tops.card
    a.averaging.thickPositions.card a.averaging.b ha.ambient_bounds.1 ha.ambient_bounds.2
    ha.sizes.top_lower ha.sizes.thick_lower ha.sizes.thick_upper ha.sizes.b_pos
  obtain ⟨tr, htr⟩ := htwists ha.ambient_bounds.1 ha.ambient_bounds.2 hranks
  refine ⟨m, k, tr, hranks, ?_, htr, ha.selmer_D6.mono htr.cutoff le_rfl⟩
  simpa only [ExcessAverageData.budget, ha.a_eq] using hsizes

/-- Ranks and a word count on one prepared host. The same choice is used for
all translations, and the restricted D6 bound is on the original field. -/
structure PreparedHostChainPlan {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H] (a : AdmissibleExcessData target e q d H)
    (x ε C₀ CΓ CH : ℝ) where
  steps : ℕ
  horizontalRank : ℕ
  twistRank : ℕ
  wordCount : ℕ
  ranks : ChainRankBounds x ε steps horizontalRank
  sizes : ExcessSizeBounds
    { a.averaging.budget with steps := steps, k := (horizontalRank : ℝ) } x ε
  twists : ChainTwistRankBounds x ε (Fintype.card H) steps horizontalRank twistRank
  selmer : SelmerLengthBound (numberFieldSelmerLengths (ExcessHost target e q d))
    twistRank (Real.exp (x ^ ε / 2))
  wordCount_pos : 0 < wordCount
  wordCount_lower :
    C₀ * Real.exp (CΓ * (steps : ℝ) ^ 5 * (2 * (Fintype.card H : ℝ)) * x ^ ε) ^ (2 : ℕ) *
      x ^ CH ≤ (wordCount : ℝ)
  wordCount_upper : (wordCount : ℝ) ≤ 2 ^ ((horizontalRank : ℝ) - 3)
  b_ge_three : 3 ≤ a.averaging.b
  heightScale_ge : 20 ≤ x ^ CH
  frameSlack : 11 * Real.exp (-(x ^ ε / 8)) * x ^ CH ≤ 1
  frameDegree : 4 * (2 * (Fintype.card H : ℝ)) ≤ a.averaging.b * Real.exp (-(x ^ ε / 8)) ^ (2 : ℕ)

/-- The common multiplicity denominator in the Bessel frame inequalities. -/
noncomputable def PreparedHostChainPlan.frameMultiplicity
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H] {a : AdmissibleExcessData target e q d H}
    {x ε C₀ CΓ CH : ℝ} (plan : PreparedHostChainPlan a x ε C₀ CΓ CH) : ℝ :=
  C₀ * Real.exp (CΓ * (plan.steps : ℝ) ^ 5 * (2 * (Fintype.card H : ℝ)) * x ^ ε) ^ (2 : ℕ)

/-- Jointly choose the ranks and the word count from the host's size and D6
bounds. The resulting scalar assumptions are those of Lemma 13.19. -/
theorem eventually_exists_preparedHostChainPlan {ε C₀ CΓ CH : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 52) (hC₀ : 1 ≤ C₀) (hCΓ : 0 ≤ CΓ) (hCH : 0 < CH) :
    ∀ᶠ x : ℝ in atTop, ∀ {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
      {H : Type} [AddCommGroup H] [Fintype H]
      {a : AdmissibleExcessData target e q d H} {C main auxiliary : ℝ},
      AdmissibleExcessConditions a x ε C main auxiliary →
      Nonempty (PreparedHostChainPlan a x ε C₀ CΓ CH) := by
  filter_upwards [eventually_admissibleHostChainParameters hε hsmall,
    eventually_chainRank_wordCount hε hC₀ hCΓ hCH.le,
    eventually_chainFrame_sizeHypotheses hε hsmall hCH] with x hranks hwords hframe
  intro target e q d H _ _ a C main auxiliary ha
  obtain ⟨m, k, tr, hmk, hsizes, htr, hselmer⟩ := hranks ha
  obtain ⟨N, hN, hlow, hhigh⟩ := hwords ha.ambient_bounds.2 hmk
  obtain ⟨hb, hheight, hslack, hdegree⟩ := hframe (Fintype.card H) ha.ambient_bounds.2
  exact ⟨⟨m, k, tr, N, hmk, hsizes, htr, hselmer, hN, hlow, hhigh,
    ha.b_eq.symm ▸ hb, hheight, hslack, ha.b_eq.symm ▸ hdegree⟩⟩

end Riemann
