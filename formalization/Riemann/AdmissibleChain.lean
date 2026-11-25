module

public import Riemann.AdmissibleExcess
public import Riemann.ChainErrorSizes
public import Riemann.ChainConstruction
public import Riemann.AdmissibleChainParameters
import Riemann.HostTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Utilities.RootDiscriminant

@[expose] public section

open Utilities Filter
open scoped BigOperators Classical NumberField

namespace Riemann

theorem AdmissibleExcessData.finrank_host_eq_four_mul_card
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+} {H : Type}
    [AddCommGroup H] [Fintype H] (a : AdmissibleExcessData target e q d H) :
    Module.finrank ℚ (ExcessHost target e q d) = 4 * Fintype.card H := by
  let : IsAbelianGalois ℚ (ExcessHost target e q d) := selmerHostField_isAbelianGalois target e q d
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr a.galoisEquiv.symm.toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  simp [ExcessGroup, Fintype.card_prod]
  omega

/-- The torsion bound used for the thick nodes in Corollary 18.8. -/
theorem AdmissibleExcessData.torsionOrder_host_le
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+} {H : Type}
    [AddCommGroup H] [Fintype H] (a : AdmissibleExcessData target e q d H) :
    NumberField.Units.torsionOrder (ExcessHost target e q d) ≤ 32 * Fintype.card H ^ 2 := by
  calc
    _ ≤ 2 * Module.finrank ℚ (ExcessHost target e q d) ^ 2 := torsionOrder_le_two_mul_finrank_sq _
    _ = _ := by rw [a.finrank_host_eq_four_mul_card]; ring

private theorem AdmissibleExcessConditions.card_le_two_mul_cube
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+} {H : Type}
    [AddCommGroup H] [Fintype H] {a : AdmissibleExcessData target e q d H}
    {x ε C main auxiliary : ℝ} (ha : AdmissibleExcessConditions a x ε C main auxiliary)
    (hsmall : ε < 1 / 52) : (Fintype.card H : ℝ) ≤ 2 * x ^ (3 : ℕ) := by
  refine ha.ambient_bounds.2.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  simpa using Real.rpow_le_rpow_of_exponent_le (by linarith [ha.sizes.scale_ge_three] : 1 ≤ x)
    (show 2 + 8 * ε ≤ (3 : ℝ) by linarith)

/-- The canonical node bases satisfy the midpoint estimates of Corollary 18.8
for every admissible thin-weight choice once the scale is large enough. -/
theorem eventually_admissibleHostNodeBounds {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∀ {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
      {H : Type} [AddCommGroup H] [Fintype H]
      {a : AdmissibleExcessData target e q d H} {C main auxiliary : ℝ},
      AdmissibleExcessConditions a x ε C main auxiliary →
      ∀ (u : H) (bt : H → ℤ) (bases : ExcessNode H → ℤ),
      a.averaging.CanonicalNodeBases u a.nodeTorsionWeights
        (fun t => bt t + Int.floor (a.averaging.thinScale / x))
        (Int.ceil a.averaging.b)
        (Int.ceil (a.averaging.thinScale / (x * Fintype.card H)))
        (Int.ceil (x ^ (402 : ℕ))) bases →
      (∀ t ∈ a.averaging.tops, a.averaging.thinScale ≤ (bt t : ℝ) ∧
        (bt t : ℝ) ≤ (5 / 4 : ℝ) * a.averaging.thinScale) →
      ∀ (j : Fin a.averaging.steps) (ρ : ExcessNode H),
        let w := bases ρ + (2 * (j.val : ℤ) + 1) * Int.ceil (x ^ (402 : ℕ))
        (a.averaging.IsThick u ρ → a.averaging.b ≤ (w : ℝ) ∧
          (w : ℝ) ≤ a.averaging.b +
            (NumberField.Units.torsionOrder (ExcessHost target e q d) : ℝ) +
            (a.averaging.steps : ℝ) * (2 * (Int.ceil (x ^ (402 : ℕ)) : ℝ)) ∧
          (w : ℝ) ≤ 2 * a.averaging.b) ∧
        (¬a.averaging.IsThick u ρ → 1 ≤ w ∧ (w : ℝ) ≤ 2 * a.averaging.thinScale) := by
  have hgapExp : 0 < ε - ε / 3 := by linarith
  have hlogs := (isLittleO_log_rpow_atTop hε).bound (show (0 : ℝ) < 1 / 2000 by norm_num)
  filter_upwards [hlogs, (tendsto_rpow_atTop hgapExp).eventually_ge_atTop 2,
    (tendsto_rpow_atTop hε).eventually_ge_atTop (4 * Real.log 160)] with x hlog hp h160
  intro target e q d H _ _ a C main auxiliary ha u bt bases hbases hbt j ρ
  have hx : 1 ≤ x := by linarith [ha.sizes.scale_ge_three]
  have hx' : 0 < x := by positivity
  have hj : (a.averaging.steps : ℝ) ≤ x := ha.sizes.steps_le_scale (by linarith)
  have hgap : 0 ≤ Int.ceil (x ^ (402 : ℕ)) := Int.ceil_nonneg (by positivity)
  have hp' : 2 * x ^ (ε / 3) ≤ x ^ ε := by
    calc
      _ ≤ x ^ (ε - ε / 3) * x ^ (ε / 3) := by gcongr
      _ = _ := by rw [← Real.rpow_add hx', sub_add_cancel]
  have hlog' : Real.log x ≤ x ^ ε / 2000 := by
    simpa [Real.norm_of_nonneg (Real.log_nonneg hx), Real.norm_of_nonneg (Real.rpow_nonneg hx'.le _),
      div_eq_mul_inv, mul_comm] using hlog
  have hy₀ : 0 ≤ x ^ ε := Real.rpow_nonneg hx'.le _
  have hexp : 160 * x ^ (403 : ℕ) ≤ Real.exp (x ^ ε / 2) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
    linarith
  have hthin : 32 * x ^ (403 : ℕ) ≤ a.averaging.thinScale := by
    rw [ha.thin_eq, ha.a_eq, ha.b_eq, ha.cutoff_eq,
      mul_div_assoc, ← Real.exp_sub]
    have hy : 32 * x ^ (403 : ℕ) ≤ Real.exp (x ^ ε - x ^ (ε / 3)) := by
      refine (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)).trans (hexp.trans ?_)
      exact Real.exp_le_exp.mpr (by linarith)
    exact hy.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le)
  have hthin₄ : 4 ≤ a.averaging.thinScale := by
    have hpow : 1 ≤ x ^ (403 : ℕ) := one_le_pow₀ hx
    linarith
  have hshift : (a.averaging.steps : ℝ) * (2 * (Int.ceil (x ^ (402 : ℕ)) : ℝ)) ≤
      4 * x ^ (403 : ℕ) := by
    have hpow : 1 ≤ x ^ (402 : ℕ) := one_le_pow₀ hx
    have hceil : (Int.ceil (x ^ (402 : ℕ)) : ℝ) ≤ 2 * x ^ (402 : ℕ) := by
      linarith [Int.ceil_lt_add_one (x ^ (402 : ℕ))]
    calc
      _ ≤ x * (2 * (2 * x ^ (402 : ℕ))) := by
        have hgap' : (0 : ℝ) ≤ Int.ceil (x ^ (402 : ℕ)) := by exact_mod_cast hgap
        gcongr
      _ = 4 * x ^ (403 : ℕ) := by rw [show (403 : ℕ) = 402 + 1 by decide, pow_succ]; ring
  have hshift' := hshift.trans (show 4 * x ^ (403 : ℕ) ≤ a.averaging.thinScale / 4 by
    linarith [show 0 ≤ x ^ (403 : ℕ) by positivity])
  have hbound := ExcessAverageData.CanonicalNodeBases.midpoint_bounds a.averaging hbases
    ha.sizes.scale_ge_three ha.sizes.ambient_pos hgap hthin₄ hshift' hbt j ρ
  have hW : (NumberField.Units.torsionOrder (ExcessHost target e q d) : ℝ) ≤
      32 * (Fintype.card H : ℝ) ^ 2 := by exact_mod_cast a.torsionOrder_host_le
  refine ⟨fun hρ => ?_, hbound.2⟩
  obtain ⟨hl, hr⟩ := hbound.1 hρ
  have hn := ha.card_le_two_mul_cube hsmall
  have hW' : (NumberField.Units.torsionOrder (ExcessHost target e q d) : ℝ) ≤
      128 * x ^ (403 : ℕ) := by
    refine hW.trans ((show 32 * (Fintype.card H : ℝ) ^ 2 ≤ 32 * (2 * x ^ (3 : ℕ)) ^ 2 by
      gcongr).trans ?_)
    calc
      _ = 128 * x ^ (6 : ℕ) := by ring
      _ ≤ _ := by gcongr; norm_num
  have hb : 160 * x ^ (403 : ℕ) ≤ a.averaging.b := by
    rw [ha.b_eq]
    exact hexp.trans (Real.exp_le_exp.mpr (by linarith))
  exact ⟨hl, hr, by linarith [show 0 ≤ x ^ (403 : ℕ) by positivity]⟩

private theorem twoPow_le_four_mul_ambientCount {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H] [Fintype H]
    (a : AdmissibleExcessData target e q d H) : 2 ^ e ≤ 4 * Fintype.card H := by
  let N := selmerHostModulus target e q d
  let r : ℕ := 2 ^ (e + 2)
  let : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let : NeZero r := ⟨by positivity⟩
  let S := Subgroup.zpowers (-1 : (ZMod r)ˣ)
  have h₁ : r ∣ selmerBaseModulus target e := Nat.dvd_lcm_left _ _
  have h₂ : selmerBaseModulus target e ∣ N :=
    dvd_trans (Nat.dvd_lcm_left _ q) (Nat.dvd_lcm_left _ d)
  have hle : selmerHostFixingUnits target e q d ≤ S.comap (ZMod.unitsMap (h₁.trans h₂)) := by
    have hproj : selmerHostFixingUnits target e q d ≤
        (selmerBaseFixingUnits target e).comap (ZMod.unitsMap h₂) := by
      exact inf_le_left.trans inf_le_left
    refine hproj.trans ?_
    rw [← ZMod.unitsMap_comp h₁ h₂, ← Subgroup.comap_comap]
    apply Subgroup.comap_mono
    exact inf_le_left
  have hindex : S.index ≤ (selmerHostFixingUnits target e q d).index := by
    rw [← S.index_comap_of_surjective (ZMod.unitsMap_surjective (h₁.trans h₂))]
    exact Subgroup.index_antitone hle
  have hSe : 2 ^ e ≤ S.index := by
    change 2 ^ e ≤ Nat.card (SelmerDyadicQuotient e)
    rw [selmerDyadicQuotient_card]
  have hhost : (selmerHostFixingUnits target e q d).index = 4 * Fintype.card H := by
    let : IsAbelianGalois ℚ (ExcessHost target e q d) := selmerHostField_isAbelianGalois target e q d
    change Nat.card _ = _
    rw [Nat.card_congr (selmerHostGalQuotient target e q d).toEquiv,
      IsGalois.card_aut_eq_finrank]
    exact a.finrank_host_eq_four_mul_card
  exact (hSe.trans hindex).trans_eq hhost

private theorem eventually_admissibleHost_log_rootDiscr_le
    (target : BundledDirichletCharacter) {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∀ {base : ℝ} {q d : ℕ+} {e : ℕ}
      {H : Type} [AddCommGroup H] [Fintype H]
      {a : AdmissibleExcessData target e q d H} {C main auxiliary : ℝ},
      SelmerWindowPair ε base q d → 3 ≤ base → base ≤ x →
      AdmissibleExcessConditions a x ε C main auxiliary →
      Real.log (NumberField.rootDiscr (ExcessHost target e q d)) ≤ x ^ ε / 2 := by
  obtain ⟨A, hA, hmodulus⟩ := exists_selmerHost_logModulus_le_of_twoPow_le_cube target 8 (by norm_num)
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  have hgap : 0 < ε - ε / 5 := by linarith
  have hsmallLog := (isLittleO_log_rpow_rpow_atTop 2 hgap).bound (show 0 < 1 / (2 * A) by positivity)
  filter_upwards [hsmallLog] with x hxlog
  intro base q d e H _ _ a C main auxiliary hpair hbase hbx ha
  have hx : 1 ≤ x := by linarith [ha.sizes.scale_ge_three]
  have hx₀ := zero_lt_one.trans_le hx
  have he : (2 : ℝ) ^ e ≤ 4 * (Fintype.card H : ℝ) := by
    exact_mod_cast twoPow_le_four_mul_ambientCount a
  have he' : (2 : ℝ) ^ e ≤ 8 * x ^ (3 : ℕ) := by
    linarith only [he, ha.card_le_two_mul_cube hsmall]
  have hlog : Real.log x ^ (2 : ℕ) ≤ (1 / (2 * A)) * x ^ (ε - ε / 5) := by
    simpa only [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg (Real.log x)),
      Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _)] using hxlog
  let N := selmerHostModulus target e q d
  let : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let : NeZero (N : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  let : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  have hrd : NumberField.rootDiscr (ExcessHost target e q d) ≤ N :=
    rootDiscr_le_cyclotomicModulus N (CyclotomicField N ℚ) (selmerHostField target e q d)
  calc
    _ ≤ Real.log (N : ℝ) := Real.log_le_log (zero_lt_one.trans_le (one_le_rootDiscr _)) hrd
    _ ≤ A * x ^ (ε / 5) * Real.log x ^ (2 : ℕ) := (hmodulus hε.le hbase hbx hpair he').2
    _ ≤ (A * (1 / (2 * A))) * (x ^ (ε / 5) * x ^ (ε - ε / 5)) := by
      calc
        _ ≤ (A * x ^ (ε / 5)) * ((1 / (2 * A)) * x ^ (ε - ε / 5)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = _ := by ring
    _ = x ^ ε / 2 := by
      rw [← Real.rpow_add hx₀, show ε / 5 + (ε - ε / 5) = ε by ring]
      field_simp

/-- The numerical estimates of Lemma 18.15 at the prepared host. -/
theorem eventually_admissibleHostChainErrorSizes {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 52)
    {c : ChainConstants} (hc : c.Valid) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
      {H : Type} [AddCommGroup H] [Fintype H]
      {a : AdmissibleExcessData target e q d H} {C main auxiliary : ℝ},
      AdmissibleExcessConditions a x ε C main auxiliary →
      Real.log (NumberField.rootDiscr (ExcessHost target e q d)) ≤ x ^ ε / 2 →
      ∀ (u : H) (N : ℕ), 0 < N → (N : ℝ) ≤ 2 ^ (a.averaging.k - 3) →
        ChainErrorSizes (a.averaging.chainInputs a.prime u x ε
          (NumberField.rootDiscr (ExcessHost target e q d)) a.localLog) c N := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (eventually_chainErrorSizes hε hsmall hc)
  refine ⟨x₀, fun x hx target e q d H _ _ a C main auxiliary ha hrd u N hN hcount => ?_⟩
  have hmass : 0 ≤ a.averaging.accountingTopMass :=
    Finset.sum_nonneg fun t ht => (ha.average.topWeight_pos t ht).le
  have hmass' : a.averaging.accountingTopMass ≤
      2 * a.averaging.tops.card * a.averaging.a := by
    unfold ExcessAverageData.accountingTopMass
    calc
      _ ≤ ∑ _t ∈ a.averaging.tops, 2 * a.averaging.a := by
        apply Finset.sum_le_sum
        intro t ht
        have h := (abs_le.mp (ha.average.topWeight_close t ht)).2
        have hr : a.averaging.topWeight t / a.averaging.b ≤ 2 * x := by
          linarith [ha.sizes.scale_ge_three]
        calc
          _ ≤ (2 * x) * a.averaging.b := (div_le_iff₀ ha.average.b_pos).mp hr
          _ = _ := by rw [ha.a_eq]; ring
      _ = _ := by simp; ring
  exact hx₀ x hx _ N rfl rfl ha.sizes ha.b_eq ha.a_eq ha.cutoff_eq ha.thin_eq
    ha.ambient_bounds.2 (one_le_rootDiscr _) hrd hmass hmass' hN hcount

/-- The error exponent depends only on the uniform degree and loss exponents. -/
noncomputable def preparedHostChainErrorBudget (degreeExponent lossExponent : ℝ) : ℝ :=
  (⟨1, 0, degreeExponent, lossExponent⟩ : ChainConstants).errorExponent

/-- The lattice and period inputs of Proposition 18.11 on a prepared host.
The arithmetic construction supplies one refinement for the selected ranks
and the Bessel and level data on that refinement. -/
theorem exists_uniform_preparedHostLatticeConstruction :
    ∃ degreeExponent lossExponent : ℝ,
      ∀ target : BundledDirichletCharacter, target.character.IsPrimitive →
        ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 / 52 ∧
          ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ J : ℝ, 2 ≤ J →
            ∃ (c : ChainConstants) (C₀ CΓ x₁ : ℝ),
              c.Valid ∧ c.degreeExponent = degreeExponent ∧ c.lossExponent = lossExponent ∧
              0 < c.heightExponent ∧ 1 ≤ C₀ ∧ 0 ≤ CΓ ∧
              ∀ base Y : ℝ, 3 ≤ base → base ≤ Y → Y ^ (2 : ℕ) ≤ base ^ J →
                ∀ q d : ℕ+, SelmerWindowPair ε base q d →
                  ∀ (e : ℕ) (x : ℝ), x₁ ≤ x → x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)) →
                    ∀ (main auxiliary : ℝ) (H : Type) [AddCommGroup H] [Fintype H]
                      (initial : AdmissibleExcessData target e q d H),
                      AdmissibleExcessConditions initial x ε
                        (preparedHostChainErrorBudget degreeExponent lossExponent) main auxiliary →
                      ∀ plan : PreparedHostChainPlan initial x ε C₀ CΓ c.heightExponent,
                        ∃ a : AdmissibleExcessData target e q d H,
                          AdmissibleExcessConditions a x ε
                            (preparedHostChainErrorBudget degreeExponent lossExponent) main auxiliary ∧
                          a.averaging.steps = plan.steps ∧ a.averaging.k = (plan.horizontalRank : ℝ) ∧
                          ∀ u ∈ a.averaging.subgroup,
                            let p := a.averaging.chainInputs a.prime u x ε
                              (NumberField.rootDiscr (ExcessHost target e q d)) a.localLog
                            ∃ (U : Type) (r : ChainRecord U p.budget.steps),
                              ChainConstructionCoreConditions p c r ∧
                              r.indices.card = plan.wordCount ∧
                              Nonempty (ChainFrameProjection p c r plan.frameMultiplicity
                                (2 * Fintype.card H)) := by
  sorry

/-- Assemble the arithmetic lattice data with the explicit rank, word-count
and frame estimates. All translations use the same prepared refinement. -/
theorem exists_uniform_preparedHostChainLattices :
    ∃ degreeExponent lossExponent : ℝ,
      ∀ target : BundledDirichletCharacter, target.character.IsPrimitive →
        ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
          ∀ J : ℝ, 2 ≤ J → ∃ (c : ChainConstants) (x₁ : ℝ),
            c.Valid ∧ c.degreeExponent = degreeExponent ∧ c.lossExponent = lossExponent ∧
            ∀ base Y : ℝ, 3 ≤ base → base ≤ Y → Y ^ (2 : ℕ) ≤ base ^ J →
              ∀ q d : ℕ+, SelmerWindowPair ε base q d →
                ∀ (e : ℕ) (x : ℝ), x₁ ≤ x → x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)) →
                  ∀ main auxiliary : ℝ, HasAdmissibleHostPoint target e q d x ε
                      (preparedHostChainErrorBudget degreeExponent lossExponent) main auxiliary →
                    ∃ (H : Type) (group : AddCommGroup H) (finite : Fintype H),
                      letI : AddCommGroup H := group
                      letI : Fintype H := finite
                      ∃ a : AdmissibleExcessData target e q d H,
                        AdmissibleExcessConditions a x ε
                          (preparedHostChainErrorBudget degreeExponent lossExponent) main auxiliary ∧
                          ∀ u ∈ a.averaging.subgroup,
                            let p := a.averaging.chainInputs a.prime u x ε
                              (NumberField.rootDiscr (ExcessHost target e q d)) a.localLog
                            ∃ (U : Type) (r : ChainRecord U p.budget.steps),
                              ChainConstructionConditions p c r := by
  obtain ⟨D, L, hconstruct⟩ := exists_uniform_preparedHostLatticeConstruction
  refine ⟨D, L, fun target htarget => ?_⟩
  obtain ⟨ε₁, hε₁, hsmall, hconstruct'⟩ := hconstruct target htarget
  refine ⟨ε₁, hε₁, fun ε hε hεlt J hJ => ?_⟩
  obtain ⟨c, C₀, CΓ, x₁, hc, hD, hL, hCH, hC₀, hCΓ, hbuild⟩ :=
    hconstruct' ε hε hεlt J hJ
  obtain ⟨x₂, hplan⟩ := eventually_atTop.mp
    (eventually_exists_preparedHostChainPlan hε (hεlt.trans_le hsmall) hC₀ hCΓ hCH)
  refine ⟨c, max x₁ x₂, hc, hD, hL, ?_⟩
  intro base Y hb hby hY q d hpair e x hx hxmem main auxiliary hadm
  obtain ⟨H, group, finite, initial, hinit⟩ := hadm
  let : AddCommGroup H := group
  let : Fintype H := finite
  obtain ⟨plan⟩ := hplan x ((le_max_right _ _).trans hx) hinit
  obtain ⟨a, ha, hm, hk, hr⟩ :=
    hbuild base Y hb hby hY q d hpair e x ((le_max_left _ _).trans hx) hxmem
      main auxiliary H initial hinit plan
  refine ⟨H, group, finite, a, ha, fun u hu => ?_⟩
  let p := a.averaging.chainInputs a.prime u x ε
    (NumberField.rootDiscr (ExcessHost target e q d)) a.localLog
  obtain ⟨U, r, hcore, hwords, ⟨frame⟩⟩ := hr u hu
  have hb' : p.budget.b = initial.averaging.b := ha.b_eq.trans hinit.b_eq.symm
  have hk' : p.budget.k = (plan.horizontalRank : ℝ) := hk
  have hwordBound : (r.indices.card : ℝ) ≤ 2 ^ (p.budget.k - 3) := by
    rw [hwords, hk']
    exact plan.wordCount_upper
  have hwordLower : plan.frameMultiplicity * p.x ^ c.heightExponent ≤ (r.indices.card : ℝ) := by
    rw [hwords]
    exact plan.wordCount_lower
  have hC : 0 < plan.frameMultiplicity := by
    unfold PreparedHostChainPlan.frameMultiplicity
    exact mul_pos (zero_lt_one.trans_le hC₀) (pow_pos (Real.exp_pos _) _)
  have hf : 4 * ((2 * Fintype.card H : ℕ) : ℝ) ≤
      p.budget.b * Real.exp (-(p.x ^ p.ε / 8)) ^ (2 : ℕ) := by
    rw [hb', Nat.cast_mul, Nat.cast_ofNat]
    exact plan.frameDegree
  obtain ⟨_, _, heta, hframe, hframeSmall⟩ := frame.bounds hC
    (hb'.symm ▸ plan.b_ge_three) plan.heightScale_ge plan.frameSlack hf hwordLower
  exact ⟨U, r, ⟨hcore, hwordBound, heta, hframe, hframeSmall⟩⟩

/-- The chain construction of Hypothesis 18.10 at the prepared host.
The degree and loss exponents are independent of the target and of ε. -/
theorem uniform_chain_conditions_on_prepared_hosts :
    ∃ C degreeExponent lossExponent : ℝ, 0 ≤ C ∧
      ∀ target : BundledDirichletCharacter, target.character.IsPrimitive →
        ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
          ∀ J : ℝ, 2 ≤ J → ∃ (c : ChainConstants) (x₁ : ℝ),
            c.Valid ∧ c.degreeExponent = degreeExponent ∧ c.lossExponent = lossExponent ∧
            c.errorExponent ≤ C ∧
            ∀ base Y : ℝ, 3 ≤ base → base ≤ Y → Y ^ (2 : ℕ) ≤ base ^ J →
              ∀ q d : ℕ+, SelmerWindowPair ε base q d →
                ∀ (e : ℕ) (x : ℝ), x₁ ≤ x → x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)) →
                  ∀ main auxiliary : ℝ, HasAdmissibleHostPoint target e q d x ε C main auxiliary →
                    ∃ (H : Type) (group : AddCommGroup H) (finite : Fintype H),
                      letI : AddCommGroup H := group
                      letI : Fintype H := finite
                      ∃ a : AdmissibleExcessData target e q d H,
                        AdmissibleExcessConditions a x ε C main auxiliary ∧
                          ∀ u ∈ a.averaging.subgroup,
                            let p := a.averaging.chainInputs a.prime u x ε
                              (NumberField.rootDiscr (ExcessHost target e q d)) a.localLog
                            ∃ (U : Type) (r : ChainRecord U p.budget.steps),
                              ChainConditions p c r := by
  obtain ⟨D, L, hchain⟩ := exists_uniform_preparedHostChainLattices
  let C := preparedHostChainErrorBudget D L
  have hC : 0 ≤ C := by
    change 0 ≤ max 2 (max D (L + 1)) + 1
    linarith [le_max_left (2 : ℝ) (max D (L + 1))]
  refine ⟨C, D, L, hC, fun target htarget => ?_⟩
  obtain ⟨ε₁, hε₁, hh⟩ := hchain target htarget
  refine ⟨ε₁, hε₁, fun ε hε hεlt J hJ => ?_⟩
  obtain ⟨c, x₁, hc, hD, hL, hexists⟩ := hh ε hε hεlt J hJ
  have hcC : c.errorExponent = C := by
    dsimp [C, preparedHostChainErrorBudget, ChainConstants.errorExponent,
      ChainConstants.baseErrorExponent]
    rw [hD, hL]
  refine ⟨c, x₁, hc, hD, hL, hcC.le, ?_⟩
  intro base Y hbase hbaseY hY q d hpair e x hx hxmem main auxiliary hadm
  obtain ⟨H, group, finite, a, ha, hrecords⟩ :=
    hexists base Y hbase hbaseY hY q d hpair e x hx hxmem main auxiliary hadm
  let : AddCommGroup H := group
  let : Fintype H := finite
  refine ⟨H, group, finite, a, ha, fun u hu => ?_⟩
  obtain ⟨U, r, hr⟩ := hrecords u hu
  exact ⟨U, r, hr.toChainConditions hc ha.sizes⟩

/-- Hypothesis 18.10 at the prepared host, including the large-scale numerical
estimates. The construction may refine the data, weights, and nodes at that host.
The degree and loss exponents are independent of the target and of ε. -/
theorem uniform_chain_records_on_prepared_hosts :
    ∃ C degreeExponent lossExponent : ℝ, 0 ≤ C ∧
      ∀ target : BundledDirichletCharacter, target.character.IsPrimitive →
        ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
          ∀ J : ℝ, 2 ≤ J → ∃ (c : ChainConstants) (x₁ : ℝ),
            c.Valid ∧ c.degreeExponent = degreeExponent ∧ c.lossExponent = lossExponent ∧
            c.errorExponent ≤ C ∧
            ∀ base Y : ℝ, 3 ≤ base → base ≤ Y → Y ^ (2 : ℕ) ≤ base ^ J →
              ∀ q d : ℕ+, SelmerWindowPair ε base q d →
                ∀ (e : ℕ) (x : ℝ), x₁ ≤ x → x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)) →
                  ∀ main auxiliary : ℝ, HasAdmissibleHostPoint target e q d x ε C main auxiliary →
                    ∃ (H : Type) (group : AddCommGroup H) (finite : Fintype H),
                      letI : AddCommGroup H := group
                      letI : Fintype H := finite
                      ∃ a : AdmissibleExcessData target e q d H,
                        AdmissibleExcessConditions a x ε C main auxiliary ∧
                          HasAdmissibleHostChainRecords a x ε c := by
  obtain ⟨C, D, L, hC, hchain⟩ := uniform_chain_conditions_on_prepared_hosts
  refine ⟨C, D, L, hC, fun target htarget => ?_⟩
  obtain ⟨ε₁, hε₁, huniform⟩ := hchain target htarget
  refine ⟨min ε₁ (1 / 52), lt_min hε₁ (by norm_num), fun ε hε hsmall J hJ => ?_⟩
  have hsmall' : ε < 1 / 52 := hsmall.trans_le (min_le_right _ _)
  obtain ⟨c, x₁, hc, hD, hL, hCc, hexists⟩ :=
    huniform ε hε (hsmall.trans_le (min_le_left _ _)) J hJ
  obtain ⟨x₂, hsize⟩ := eventually_admissibleHostChainErrorSizes hε hsmall' hc
  obtain ⟨x₃, hrd⟩ := eventually_atTop.mp
    (eventually_admissibleHost_log_rootDiscr_le target hε hsmall')
  refine ⟨c, max x₁ (max x₂ x₃), hc, hD, hL, hCc, ?_⟩
  intro base Y hb hby hY q d hpair e x hx hxmem main auxiliary hadmissible
  obtain ⟨H, group, finite, a, ha, hrecords⟩ :=
    hexists base Y hb hby hY q d hpair e x ((le_max_left _ _).trans hx) hxmem main auxiliary
      hadmissible
  let : AddCommGroup H := group
  let : Fintype H := finite
  refine ⟨H, group, finite, a, ha, fun u hu => ?_⟩
  obtain ⟨U, r, hr⟩ := hrecords u hu
  have hx₂ : x₂ ≤ x := ((le_max_left _ _).trans (le_max_right x₁ _)).trans hx
  have hx₃ : x₃ ≤ x := ((le_max_right _ _).trans (le_max_right x₁ _)).trans hx
  exact ⟨U, r, hr, hsize x hx₂ ha (hrd x hx₃ hpair hb (hby.trans hxmem.1) ha)
    u r.indices.card r.nonempty.card_pos hr.index_count⟩

end Riemann
