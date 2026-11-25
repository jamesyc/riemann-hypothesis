module

public import Riemann.AdmissibleExcess
public import Riemann.HostAveraging
public import Riemann.AuxiliarySmoothedPrimeSelection
import Riemann.PreparedHostGeometry
import Riemann.PreparedHostTail
import Utilities.PrimeIntervals

@[expose] public section

open Filter Utilities
open scoped BigOperators

namespace Riemann

/-- The auxiliary survivor family for a selected prime pair, independent of the
varying dyadic degree. -/
noncomputable def preparedAuxiliaryCharacter (target : BundledDirichletCharacter)
    {ε base : ℝ} {q d : ℕ+} (pair : SelmerWindowPair ε base q d)
    (i : SelmerAuxiliaryIndex target) : BundledDirichletCharacter :=
  letI : Fact (q : ℕ).Prime := ⟨pair.q_prime⟩
  letI : Fact (d : ℕ).Prime := ⟨pair.d_prime⟩
  selmerAuxiliaryCharacter target q d (by have := pair.q_residue; omega)
    (by have := pair.d_residue; omega) i

/-- Prime-pair selection on the full base interval, including the analytic
bounds on the auxiliary twists from the prime-pool argument of §5. -/
theorem exists_preparedAuxiliaryPrimePairs
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 52 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ J : ℝ, 2 ≤ J → ∃ T : ℝ, ∀ base ≥ T, ∃ q d : ℕ+,
        ∃ pair : SelmerWindowPair ε base q d,
          ((target.modulus : ℕ) : ℝ) ≤ base ^ (ε / 5) ∧
          FirstAuxiliaryRealGood target q ∧ SecondAuxiliaryRealGood target q d ∧
          ∀ x ∈ Set.Icc base (base ^ J), ∀ i : SelmerAuxiliaryIndex target,
            ‖complexSmoothedCharacterSum (preparedAuxiliaryCharacter target pair i) x‖ ≤
              x ^ (1 / 2 + ε) := by
  refine ⟨1 / 52, by norm_num, le_rfl, fun ε hε hsmall J hJ => ?_⟩
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (eventually_exists_smoothedAuxiliaryPrimePair target hprim hε hsmall hJ)
  refine ⟨T, fun base hb => ?_⟩
  obtain ⟨q, d, pair, hmod, hq, hd, hqreal, hdreal⟩ := hT base hb
  refine ⟨q, d, pair, hmod, hqreal, hdreal, fun x hx i => ?_⟩
  let : Fact (q : ℕ).Prime := ⟨pair.q_prime⟩
  let : Fact (d : ℕ).Prime := ⟨pair.d_prime⟩
  have hq₄ : (q : ℕ) % 4 = 3 := by have := pair.q_residue; omega
  have hd₄ : (d : ℕ) % 4 = 3 := by have := pair.d_residue; omega
  change ‖complexSmoothedCharacterSum
    (selmerTwistedCharacter target q d hq₄ hd₄ i.1 i.2.val.1 i.2.val.2) x‖ ≤ _
  cases hsecond : i.2.val.2 with
  | true =>
      simpa only [secondAuxiliaryTestCharacter_coe target q d hq₄ hd₄] using hd x hx (i.1, i.2.val.1)
  | false =>
      have hfirst : i.2.val.1 = true := by
        cases h : i.2.val.1
        · exact False.elim (i.2.property (Prod.ext h hsecond))
        · rfl
      rw [hfirst, selmerTwistedCharacter_no_second_twist]
      simpa only [firstAuxiliaryTestCharacter_coe target q hq₄] using hq x hx i.1

/-- Assemble one admissible point at sufficiently large scales, using
the canonical host and the two real-zero tests carried by the prime pair. -/
theorem eventually_exists_admissibleHostPoint_of_ambient_bounds
    (target : BundledDirichletCharacter) {C ε : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (hsmall : ε < 1 / 52) :
    ∀ᶠ x : ℝ in atTop, ∀ (e : ℕ) {base : ℝ} {q d : ℕ+},
      3 ≤ base → base ≤ x → (pair : SelmerWindowPair ε base q d) →
      ((target.modulus : ℕ) : ℝ) ≤ base ^ (ε / 5) →
      FirstAuxiliaryRealGood target q → SecondAuxiliaryRealGood target q d →
      (∀ i : SelmerAuxiliaryIndex target,
        ‖complexSmoothedCharacterSum (preparedAuxiliaryCharacter target pair i) x‖ ≤ x ^ (1 / 2 + ε)) →
      letI := selmerHostBaseGroupFintype target e
      x ^ (2 + 8 * ε) ≤ (Fintype.card (SelmerHostBaseGroup target e) : ℝ) →
      (Fintype.card (SelmerHostBaseGroup target e) : ℝ) ≤ 2 * x ^ (2 + 8 * ε) →
      SelmerLengthBound (numberFieldSelmerLengths (ExcessHost target e q d))
        (Nat.floor (x ^ (400 : ℕ))) (Real.exp (x ^ ε / 2)) →
      HasAdmissibleHostPoint target e q d x ε C
        (smoothedCombination
          (fun i : Fin (orderOf target.character - 1) => selmerFixedCharacter target ((i : ℕ) + 1))
          (fun _ => (3 * (orderOf target.character : ℝ) + 1)⁻¹) x)
        (∑ i : SelmerAuxiliaryIndex target,
          ‖complexSmoothedCharacterSum (preparedAuxiliaryCharacter target pair i) x‖) := by
  classical
  obtain ⟨B, hB, hfixed⟩ := exists_selmerFixedNormBound target hε
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp eventually_exists_two_primes_Ioc_double
  filter_upwards [eventually_exists_preparedHostGeometry target hε hsmall,
    eventually_preparedHostSmoothedTail target hε hsmall.le, eventually_selmerTailSlope_le hε,
    selmerCorrections_eventually_le target hε hsmall.le hC (zero_le_one.trans hB),
    eventually_ge_atTop (max 1 Z)]
    with x hgeo htail hslope hcorr hxZ e base q d hbase hbx pair hmod hqreal hdreal haux
      hlo hhi hD6
  let H := SelmerHostBaseGroup target e
  let instanceH : Fintype H := selmerHostBaseGroupFintype target e
  let : Fact (q : ℕ).Prime := ⟨pair.q_prime⟩
  let : Fact (d : ℕ).Prime := ⟨pair.d_prime⟩
  have hq₄ : (q : ℕ) % 4 = 3 := by have := pair.q_residue; omega
  have hd₄ : (d : ℕ) % 4 = 3 := by have := pair.d_residue; omega
  obtain ⟨hq, hd⟩ := pair.coprime_host_base_modulus target e hmod
  let coord := pair.hostCoordinates target e hq hd
  let inducing (ψ : ExcessCharacter H) := selmerHostInducingCharacter
    (target := target) (e := e) (q := q) (d := d) coord.symm ψ
  obtain ⟨prime, primeIdeal, hprime, hind⟩ := exists_selmerHostInducingConditions target e pair hmod hq hd
  obtain ⟨g, hg⟩ := hgeo e hlo hhi
  let avg := preparedHostAveraging g x ε B
  have hx : 3 ≤ x := hbase.trans hbx
  have hx₁ : 1 ≤ x := by linarith
  have hb₁ : 1 ≤ avg.b := by change 1 ≤ g.b; rw [hg.b_eq]; exact Real.one_le_exp (by positivity)
  have hkx : x ≤ avg.k := by
    have hm : (1 : ℝ) ≤ g.steps := by exact_mod_cast hg.sizes.steps_pos
    exact (le_mul_of_one_le_right (by positivity) hm).trans hg.sizes.k_lower
  have hkbx : x ≤ avg.k * avg.b :=
    hkx.trans (le_mul_of_one_le_right (by linarith) hb₁)
  have hZ' : Z ≤ (avg.k * avg.b) ^ (8 : ℕ) :=
    ((le_max_right _ _).trans hxZ).trans (hkbx.trans (le_self_pow₀ (hx₁.trans hkbx) (by decide)))
  obtain ⟨p₀, p₁, hp₀, hp₁, hp₀₁, h₀, h₁⟩ := hZ _ hZ'
  let a : AdmissibleExcessData target e q d H := ⟨avg, prime, coord.symm, primeIdeal, inducing, p₀, p₁⟩
  obtain ⟨hz, hfixed'⟩ := hfixed x hx₁
  have hnorm := selmerSurvivors_norm_le target e q d hq₄ hd₄ hq hd avg
    hg.subgroup_eq hg.kept_eq prime hind hx₁ hB hz hfixed' haux
  have hvariation := selmerSurvivors_localVariation_le target e q d hq₄ hd₄ hq hd avg prime hind hx hnorm
  have hcard : (Nat.card H : ℝ) ≤ 2 * x ^ (2 + 8 * ε) := by
    rw [Nat.card_eq_fintype_card]
    exact hhi
  have htail' (ψ : ExcessCharacter H) (y : ℝ) (hy : Real.exp (x ^ (ε / 3)) / 3 ≤ y) :
      ‖prime.smoothed ψ y‖ ≤ Real.exp (-(x ^ (ε / 8))) * y :=
    @htail e base q d hbase hbx pair hmod hqreal hdreal hcard H
      (inferInstanceAs (AddCommGroup (SelmerHostBaseGroup target e))) instanceH
      coord.symm prime hind ψ y hy
  have havg : ExcessAverageHypotheses avg prime.smoothed x :=
    hg.toExcessAverageHypotheses (zero_le_one.trans hB) hind.weightedVariation hvariation htail'
  refine ⟨H, inferInstance, instanceH, a, ?_⟩
  refine
    { toHostPrimeConditions := hprime
      toHostInducingConditions := hind
      level_prime₀ := hp₀
      level_prime₁ := hp₁
      level_primes_distinct := hp₀₁.ne
      level_prime_bounds := ?_
      b_eq := hg.b_eq
      a_eq := hg.a_eq
      cutoff_eq := hg.cutoff_eq
      thin_eq := hg.thin_eq
      ambient_bounds := ⟨hlo, hhi⟩
      selmer_D6 := hD6
      average := havg
      sizes := hg.sizes
      main_eq := selmerMainValue_eq target q d hq₄ hd₄ hq hd avg hg.kept_eq hg.mainWeight_eq prime hind x
      auxiliary_eq := selmerAuxiliaryValue_eq target q d hq₄ hd₄ hq hd avg hg.subgroup_eq hg.kept_eq prime hind x
      corrections := hcorr e avg prime.smoothed hg.sizes hhi hg.subgroup_eq hg.kept_eq hslope
        hg.nodeError_le le_rfl le_rfl (fun ψ hψ => hnorm ψ (havg.kept_subset hψ)) }
  intro p hp
  change p ∈ ({p₀, p₁} : Finset ℕ) at hp
  rcases Finset.mem_insert.mp hp with h | h
  · subst p
    exact ⟨h₀.1.le, h₀.2⟩
  · have hp' := Finset.mem_singleton.mp h
    subst p
    exact ⟨h₁.1.le, h₁.2⟩

/-- Proposition 18.4 with the finite-group and analytic identifications in §6.3. -/
theorem exists_prepared_excess_windows_of_rescaled_selmer
    (hSelmer : HasRescaledSelmerWindowBound numberFieldSelmerLengths) {C : ℝ} (hC : 0 ≤ C) :
    HasPreparedExcessWindows C := by
  classical
  intro target hprim
  obtain ⟨family, weight, hfamily, hweight, hne, hpos, hcontains⟩ :=
    exists_selmerFixedCombination target hprim
  obtain ⟨ε₀, hε₀, hsmall, hpairs⟩ := exists_preparedAuxiliaryPrimePairs target hprim
  let n := Fintype.card (SelmerAuxiliaryIndex target)
  let aidx : SelmerAuxiliaryIndex target ≃ Fin n := Fintype.equivFin _
  refine ⟨_, family, weight, hne, hpos, hcontains, ε₀, n, hε₀, hsmall,
    Nat.cast_nonneg _, fun ε hε hεlt => ?_⟩
  let P (J base : ℝ) (q d : ℕ+) : Prop :=
    ((target.modulus : ℕ) : ℝ) ≤ base ^ (ε / 5) ∧
    FirstAuxiliaryRealGood target q ∧ SecondAuxiliaryRealGood target q d ∧
    ∀ (pair : SelmerWindowPair ε base q d), ∀ x ∈ Set.Icc base (base ^ J),
      ∀ i : SelmerAuxiliaryIndex target,
        ‖complexSmoothedCharacterSum (preparedAuxiliaryCharacter target pair i) x‖ ≤ x ^ (1 / 2 + ε)
  have hP : ∀ J : ℝ, 2 ≤ J → ∃ T : ℝ, ∀ base ≥ T, ∃ q d : ℕ+,
      SelmerWindowPair ε base q d ∧ P J base q d := by
    intro J hJ
    obtain ⟨T, hT⟩ := hpairs ε hε hεlt J hJ
    refine ⟨T, fun base hb => ?_⟩
    obtain ⟨q, d, pair, hmod, hqreal, hdreal, haux⟩ := hT base hb
    exact ⟨q, d, pair, hmod, hqreal, hdreal, fun _ => haux⟩
  have hεsmall := hεlt.trans_le hsmall
  obtain ⟨J, hJ, hw⟩ :=
    exists_ambient_selmer_windows_of_pair_selection hSelmer target hprim hε hεsmall P hP
  obtain ⟨x₀, hpoint⟩ := eventually_atTop.mp
    (eventually_exists_admissibleHostPoint_of_ambient_bounds target hC hε hεsmall)
  refine ⟨J, hJ, fun lower => ?_⟩
  obtain ⟨base, Y, q, d, e, hlow, hb, hbY, hY, pair, hP', hhost⟩ := hw (max lower x₀)
  have hY₀ : x₀ ≤ Y := (le_max_right lower x₀).trans ((le_max_right _ _).trans hlow)
  have hlow' : max 1 lower ≤ Y := (max_le_max_left _ (le_max_left lower x₀)).trans hlow
  obtain ⟨hmod, hqreal, hdreal, haux⟩ := hP'
  let aux (i : Fin n) := preparedAuxiliaryCharacter target pair (aidx.symm i)
  refine ⟨base, Y, q, d, e, n, aux, hlow', hb, hbY, hY, pair, le_rfl, ?_, ?_⟩
  · intro i
    let : Fact (q : ℕ).Prime := ⟨pair.q_prime⟩
    let : Fact (d : ℕ).Prime := ⟨pair.d_prime⟩
    obtain ⟨hq, hd⟩ := pair.coprime_host_base_modulus target 0 hmod
    exact selmerAuxiliaryCharacter_isPrimitive_ne_one target q d
      (by have := pair.q_residue; omega) (by have := pair.d_residue; omega) hq hd (aidx.symm i)
  · intro x hx
    obtain ⟨hxbase, hlo, hhi, hD6⟩ := hhost x hx
    refine ⟨fun i => haux pair x hxbase (aidx.symm i), ?_⟩
    have hdata := hpoint x (hY₀.trans hx.1) (e x) hb hxbase.1 pair hmod hqreal hdreal
      (haux pair x hxbase) hlo hhi hD6
    have hsum :
        (∑ i : SelmerAuxiliaryIndex target,
          ‖complexSmoothedCharacterSum (preparedAuxiliaryCharacter target pair i) x‖) =
        ∑ i, ‖complexSmoothedCharacterSum (aux i) x‖ :=
      Fintype.sum_equiv aidx _ _ (fun i => by simp [aux])
    rw [hsum] at hdata
    simpa only [funext hfamily, funext hweight] using hdata

end Riemann
