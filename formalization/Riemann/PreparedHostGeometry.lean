module

public import Riemann.HostCorrections
import Riemann.ChainParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter Utilities

namespace Riemann

/-- The finite size and averaging conditions at a fixed host. The analytic
fields of the averaging data are filled when the host is assembled. -/
structure PreparedHostGeometry {target : BundledDirichletCharacter} {e : ℕ}
    [Fintype (SelmerHostBaseGroup target e)]
    (avg : ExcessAverageData (SelmerHostBaseGroup target e)) (x ε : ℝ) : Prop where
  subgroup_eq : avg.subgroup = selmerAveragingSubgroup target e
  kept_eq : avg.kept = selmerKeptCharacters target e
  mainWeight_eq : avg.mainWeight = (3 * (orderOf target.character : ℝ) + 1)⁻¹
  b_eq : avg.b = Real.exp (x ^ ε)
  a_eq : avg.a = x * avg.b
  cutoff_eq : avg.thinCutoff = Real.exp (x ^ (ε / 3))
  thin_eq : avg.thinScale = avg.a / avg.thinCutoff
  sizes : ExcessSizeBounds avg.budget x ε
  thick_subset : ∀ u ∈ avg.thickPositions, u ∈ avg.subgroup
  coset_counts : HasSelmerHostCosetCounts avg (x ^ (-1 + ε) * avg.tops.card)
  nodeError_nonneg : 0 ≤ avg.nodeError
  nodeError_le : avg.nodeError ≤ avg.b * x ^ (-6 : ℝ)
  topWeight_pos : ∀ t ∈ avg.tops, 0 < avg.topWeight t
  topWeight_close : ∀ t ∈ avg.tops, |avg.topWeight t / avg.b - x| ≤ 1
  nodeWeight_pos : ∀ u ∈ avg.subgroup, ∀ j : Fin avg.steps, ∀ g, 0 < avg.nodeWeight u j g
  thick_bounds : ∀ u ∈ avg.subgroup, ∀ j : Fin avg.steps, ∀ g, avg.IsThick u g →
    avg.b ≤ avg.nodeWeight u j g ∧ avg.nodeWeight u j g ≤ avg.b + avg.nodeError
  thin_bound : ∀ u ∈ avg.subgroup, ∀ j : Fin avg.steps, ∀ g, ¬avg.IsThick u g →
    avg.nodeWeight u j g ≤ 2 * avg.thinScale

/-- Fill the analytic error fields of the averaging data at the chosen scale. -/
noncomputable def preparedHostAveraging {target : BundledDirichletCharacter} {e : ℕ}
    (g : ExcessAverageData (SelmerHostBaseGroup target e)) (x ε B : ℝ) :
    ExcessAverageData (SelmerHostBaseGroup target e) :=
  { g with
    localVariation := 4 + B * x ^ ε
    equidistributionError := (orderOf target.character : ℝ) * x ^ (-1 + ε)
    tailSlope := Real.exp (-(x ^ (ε / 8))) }

set_option maxHeartbeats 450000 in
/-- The three analytic bounds complete the averaging hypotheses once the
finite sets and weights have been chosen. -/
theorem PreparedHostGeometry.toExcessAverageHypotheses
    {target : BundledDirichletCharacter} {e : ℕ} [Fintype (SelmerHostBaseGroup target e)]
    {g : ExcessAverageData (SelmerHostBaseGroup target e)} {x ε B : ℝ}
    (hg : PreparedHostGeometry g x ε) (hB : 0 ≤ B)
    {G : ExcessCharacter (SelmerHostBaseGroup target e) → ℝ → ℂ}
    (hweighted : ∀ (ψ : ExcessCharacter (SelmerHostBaseGroup target e)) (A w w' : ℝ), 0 < A → 0 < w → w ≤ A → 0 < w' → w' ≤ A →
      ‖(w : ℂ) * G ψ (A / w) - (w' : ℂ) * G ψ (A / w')‖ ≤
        3 * A * |w - w'| / min w w')
    (hvariation : ∀ ψ ∈ g.survivors, ∀ y : ℝ, |y - x| ≤ 1 →
      ‖G ψ y - G ψ x‖ ≤ 4 + B * x ^ ε)
    (htail : ∀ ψ y, Real.exp (x ^ (ε / 3)) / 3 ≤ y →
      ‖G ψ y‖ ≤ Real.exp (-(x ^ (ε / 8))) * y) :
    ExcessAverageHypotheses (preparedHostAveraging g x ε B) G x := by
  let avg := preparedHostAveraging g x ε B
  have hx : 3 ≤ x := hg.sizes.scale_ge_three
  have hx₁ : 1 ≤ x := by linarith
  have hequi := selmerKept_equidistribution_of_coset_counts g hg.subgroup_eq hg.kept_eq _ hg.coset_counts
  have hthin : 0 < avg.thinScale := by
    change 0 < g.thinScale
    rw [hg.thin_eq, hg.cutoff_eq]
    exact div_pos hg.sizes.a_pos (Real.exp_pos _)
  have hthinEq : avg.thinScale * avg.thinCutoff = x * avg.b := by
    change g.thinScale * g.thinCutoff = x * g.b
    rw [hg.thin_eq, hg.cutoff_eq, div_mul_cancel₀ _ (Real.exp_ne_zero _), hg.a_eq]
  have hnode : avg.nodeError ≤ avg.b := by
    refine hg.nodeError_le.trans ?_
    exact mul_le_of_le_one_right hg.sizes.b_pos.le (Real.rpow_le_one_of_one_le_of_nonpos hx₁ (by norm_num))
  have hkept : avg.kept = selmerKeptCharacters target e := hg.kept_eq
  have hsub : avg.subgroup = selmerAveragingSubgroup target e := hg.subgroup_eq
  refine
    { scale_ge_three := hx
      tops_nonempty := Finset.card_pos.mp hg.sizes.top_pos
      thick_nonempty := Finset.card_pos.mp hg.sizes.thick_pos
      thick_subset := hg.thick_subset
      kept_subset := hkept.symm ▸ selmerKeptCharacters_subset_survivors avg hsub
      kept_zero := hkept.symm ▸ selmerKeptCharacters_zero_mem target e
      kept_sign := fun ψ hψ => selmerKeptCharacters_sign ψ (hkept ▸ hψ)
      weight_nonneg := by change 0 ≤ g.mainWeight; rw [hg.mainWeight_eq]; positivity
      equidistribution_nonneg := by dsimp [avg, preparedHostAveraging]; positivity
      equidistribution := fun ψ hψ hn => by
        simpa only [preparedHostAveraging, mul_assoc] using hequi ψ hψ hn
      b_pos := hg.sizes.b_pos
      thinScale_pos := hthin
      thinCutoff_pos := by change 0 < g.thinCutoff; rw [hg.cutoff_eq]; positivity
      thin_size := hthinEq.le
      nodeError_nonneg := hg.nodeError_nonneg
      nodeError_le := hnode
      tailSlope_nonneg := Real.exp_nonneg _
      variation_nonneg := by dsimp [avg, preparedHostAveraging]; positivity
      steps_pos := hg.sizes.steps_pos
      topWeight_pos := hg.topWeight_pos
      topWeight_close := hg.topWeight_close
      nodeWeight_pos := hg.nodeWeight_pos
      thick_bounds := hg.thick_bounds
      thin_bound := hg.thin_bound
      weightedVariation := hweighted
      local_bound := hvariation
      tail_bound := fun ψ y hy => htail ψ y (by simpa only [preparedHostAveraging, hg.cutoff_eq] using hy) }

local instance (target : BundledDirichletCharacter) (e : ℕ) :
    IsAddCommutative (SelmerHostBaseGroup target e) := ⟨⟨fun a b => add_comm a b⟩⟩

/-- Choose a top set with exact coset shares and the numerical size in
Proposition 5.20, and a thick set of the required size inside the subgroup. -/
theorem eventually_exists_preparedHostSets (target : BundledDirichletCharacter) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (e : ℕ) [Fintype (SelmerHostBaseGroup target e)],
      x ^ (2 + 8 * ε) ≤ (Fintype.card (SelmerHostBaseGroup target e) : ℝ) →
      ∃ tops thick : Finset (SelmerHostBaseGroup target e),
        (1 / 2 : ℝ) * x ^ (-ε / 8) * Fintype.card (SelmerHostBaseGroup target e) ≤ tops.card ∧
        (tops.card : ℝ) ≤ x ^ (-ε / 8) * Fintype.card (SelmerHostBaseGroup target e) ∧
        x ^ (-ε) * Fintype.card (SelmerHostBaseGroup target e) ≤ thick.card ∧
        (∀ u ∈ thick, u ∈ selmerAveragingSubgroup target e) ∧
        HasCosetEquidistribution tops (QuotientAddGroup.mk' (selmerAveragingSubgroup target e))
          ((3 * (orderOf target.character : ℝ) + 1)⁻¹) 0 := by
  classical
  let o := orderOf target.character
  let P : ℝ := 3 * (o : ℝ) + 1
  have hP : 0 < P := by unfold P; positivity
  have hlarge := (tendsto_rpow_atTop (show 0 < (-ε / 8) + (2 + 8 * ε) by linarith)).eventually_ge_atTop
    (2 * P)
  have hsmall := (tendsto_rpow_atTop (show 0 < ε / 8 by positivity)).eventually_ge_atTop (2 : ℝ)
  have hthick := (tendsto_rpow_atTop hε).eventually_ge_atTop (o : ℝ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlarge, hsmall, hthick] with x hx hxlarge hxsmall hxthick
  intro e _ hlo
  let H := SelmerHostBaseGroup target e
  let A := selmerAveragingSubgroup target e
  let n := Fintype.card H
  let δ := x ^ (-ε / 8)
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hn : o * Nat.card A = n := by
    calc
      _ = A.index * Nat.card A :=
        congrArg (fun o' : ℕ => o' * Nat.card A) (selmerAveragingSubgroup_index target e).symm
      _ = Nat.card H := AddSubgroup.index_mul_card A
      _ = _ := Nat.card_eq_fintype_card
  have hnR : (n : ℝ) = (o : ℝ) * (Nat.card A : ℝ) := by exact_mod_cast hn.symm
  have hδ : δ ≤ 1 / 2 := by
    dsimp only [δ]
    rw [show -ε / 8 = -(ε / 8) by ring, Real.rpow_neg hx₀.le]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hxsmall
  have hδn : 2 * P ≤ δ * n := by
    calc
      _ ≤ x ^ ((-ε / 8) + (2 + 8 * ε)) := hxlarge
      _ = δ * x ^ (2 + 8 * ε) := (Real.rpow_add hx₀ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  let k := Nat.floor (δ * (n : ℝ) / P)
  have hkle : (k : ℝ) ≤ δ * n / P := Nat.floor_le (by positivity)
  have hcap : 4 * k ≤ Nat.card A := by
    have hδo : 4 * δ * (o : ℝ) ≤ P := by
      have ho₀ : 0 ≤ (o : ℝ) := Nat.cast_nonneg o
      have h := mul_le_mul_of_nonneg_right hδ ho₀
      unfold P
      linarith only [h, ho₀]
    have hcap' : 4 * (k : ℝ) ≤ (Nat.card A : ℝ) := by
      calc
        _ ≤ 4 * (δ * n / P) := mul_le_mul_of_nonneg_left hkle (by norm_num)
        _ = (4 * δ * n) / P := by ring
        _ ≤ _ := (div_le_iff₀ hP).mpr (by
          rw [hnR]
          calc
            _ = (4 * δ * (o : ℝ)) * (Nat.card A : ℝ) := by ring
            _ ≤ P * (Nat.card A : ℝ) := mul_le_mul_of_nonneg_right hδo (by positivity)
            _ = _ := mul_comm _ _)
    exact_mod_cast hcap'
  obtain ⟨tops, hc, hcosets⟩ := exists_exactCosetShares A k hcap
  have ho' : A.index = o := selmerAveragingSubgroup_index target e
  have hcard : (tops.card : ℝ) = P * k := by
    rw [hc, ho']
    simp [P]
  have htopLower : (1 / 2 : ℝ) * δ * n ≤ tops.card := by
    have hk := (div_lt_iff₀ hP).mp (Nat.lt_floor_add_one (δ * (n : ℝ) / P))
    change δ * n < ((k : ℝ) + 1) * P at hk
    nlinarith only [hk, hδn, hcard]
  have htopUpper : (tops.card : ℝ) ≤ δ * n := by
    rw [hcard]
    exact (le_div_iff₀' hP).mp hkle
  let S : Finset H := Finset.univ.filter (· ∈ A)
  have hS : S.card = Nat.card A := by
    let : Fintype A := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype (fun a : H => a ∈ A)).symm
  have htcap : x ^ (-ε) * (n : ℝ) ≤ (S.card : ℝ) := by
    rw [hS, Real.rpow_neg hx₀.le, hnR]
    calc
      _ = ((o : ℝ) / x ^ ε) * (Nat.card A : ℝ) := by ring
      _ ≤ _ := mul_le_of_le_one_left (by positivity)
        ((div_le_one (Real.rpow_pos_of_pos hx₀ _)).mpr hxthick)
  obtain ⟨thick, hs, hthickCard⟩ := Finset.exists_subset_card_eq (Nat.ceil_le.mpr htcap)
  refine ⟨tops, thick, htopLower, htopUpper, ?_, fun a ha => (Finset.mem_filter.mp (hs ha)).2, ?_⟩
  · rw [hthickCard]
    exact Nat.le_ceil _
  · simpa only [ho'] using hcosets

/-- Assemble the numerical geometry for the host averaging, uniformly over
the dyadic exponents in the prescribed degree range. -/
theorem eventually_exists_preparedHostGeometry (target : BundledDirichletCharacter) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∀ (e : ℕ) [Fintype (SelmerHostBaseGroup target e)],
      x ^ (2 + 8 * ε) ≤ (Fintype.card (SelmerHostBaseGroup target e) : ℝ) →
      (Fintype.card (SelmerHostBaseGroup target e) : ℝ) ≤ 2 * x ^ (2 + 8 * ε) →
      ∃ avg : ExcessAverageData (SelmerHostBaseGroup target e), PreparedHostGeometry avg x ε := by
  classical
  filter_upwards [eventually_exists_preparedHostSets target hε,
    eventually_exists_chainExcessBudget hε hsmall] with x hsets hbudget
  intro e _ hlo hhi
  let H := SelmerHostBaseGroup target e
  let A := selmerAveragingSubgroup target e
  obtain ⟨tops, thick, htop, _, hthick, hthickmem, hcosets⟩ := hsets e hlo
  let b := Real.exp (x ^ ε)
  let cutoff := Real.exp (x ^ (ε / 3))
  let thin := x * b / cutoff
  have hb : 0 < b := Real.exp_pos _
  obtain ⟨m, k, _, hsizes⟩ := hbudget (Fintype.card H) tops.card thick.card b
    hlo hhi htop hthick (Finset.card_le_univ thick) hb
  have hx : 0 < x := by linarith [hsizes.scale_ge_three]
  have hthin : 0 < thin := div_pos (mul_pos hx hb) (Real.exp_pos _)
  let avg : ExcessAverageData H :=
    { subgroup := A
      tops := tops
      thickPositions := thick
      kept := selmerKeptCharacters target e
      steps := m
      a := x * b
      b := b
      k := k
      thinScale := thin
      thinCutoff := cutoff
      nodeError := 0
      tailSlope := 0
      localVariation := 0
      mainWeight := (3 * (orderOf target.character : ℝ) + 1)⁻¹
      equidistributionError := 0
      topWeight := fun _ => x * b
      nodeWeight := fun u _ g => if g.1 = 1 ∧ g.2 - u ∈ thick then b else thin }
  refine ⟨avg, ?_⟩
  refine
    { subgroup_eq := rfl
      kept_eq := rfl
      mainWeight_eq := rfl
      b_eq := rfl
      a_eq := rfl
      cutoff_eq := rfl
      thin_eq := rfl
      sizes := hsizes
      thick_subset := hthickmem
      coset_counts := ?_
      nodeError_nonneg := le_rfl
      nodeError_le := by change 0 ≤ b * x ^ (-6 : ℝ); positivity
      topWeight_pos := fun _ _ => mul_pos hx hb
      topWeight_close := ?_
      nodeWeight_pos := ?_
      thick_bounds := ?_
      thin_bound := ?_ }
  · intro q
    exact (hcosets q).trans (by positivity)
  · intro _ _
    change |x * b / b - x| ≤ 1
    rw [mul_div_cancel_right₀ _ hb.ne', sub_self, abs_zero]
    norm_num
  · intro u _ j g
    change 0 < if g.1 = 1 ∧ g.2 - u ∈ thick then b else thin
    split_ifs <;> assumption
  · intro u _ j g hg
    change g.1 = 1 ∧ g.2 - u ∈ thick at hg
    simp [avg, hg]
  · intro u _ j g hg
    change ¬ (g.1 = 1 ∧ g.2 - u ∈ thick) at hg
    change (if g.1 = 1 ∧ g.2 - u ∈ thick then b else thin) ≤ 2 * thin
    rw [ite_eq_right hg]
    linarith

end Riemann
