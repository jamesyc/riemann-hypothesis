module

public import Riemann.HostCharacters
import Mathlib.Data.Nat.GCD.Prime

@[expose] public section

open Utilities
open scoped BigOperators Classical

namespace Riemann

/-- Indices of the survivors with at least one of the two auxiliary twists. -/
abbrev SelmerAuxiliaryIndex (target : BundledDirichletCharacter) :=
  Fin (orderOf target.character) × {signs : Bool × Bool // signs ≠ (false, false)}

theorem selmerAuxiliaryIndex_card (target : BundledDirichletCharacter) :
    Fintype.card (SelmerAuxiliaryIndex target) = 3 * orderOf target.character := by
  rw [Fintype.card_prod, Fintype.card_fin, show
    Fintype.card {signs : Bool × Bool // signs ≠ (false, false)} = 3 by decide, mul_comm]

noncomputable def selmerUntwistedEmbedding (target : BundledDirichletCharacter) (e : ℕ) :
    Fin (orderOf target.character) ↪ ExcessCharacter (SelmerHostBaseGroup target e) where
  toFun i := selmerSurvivor target e i false false
  inj' := fun i j h => congrArg Prod.fst (selmerSurvivor_injective target e
    (a₁ := (i, false, false)) (a₂ := (j, false, false)) h)

noncomputable def selmerAuxiliaryEmbedding (target : BundledDirichletCharacter) (e : ℕ) :
    SelmerAuxiliaryIndex target ↪ ExcessCharacter (SelmerHostBaseGroup target e) where
  toFun i := selmerSurvivor target e i.1 i.2.val.1 i.2.val.2
  inj' := fun i j h => by
    have he := selmerSurvivor_injective target e
      (a₁ := (i.1, i.2.val)) (a₂ := (j.1, j.2.val)) h
    refine Prod.ext ?_ ?_
    · exact congrArg (fun c : Fin (orderOf target.character) × Bool × Bool => c.1) he
    · exact Subtype.ext (congrArg (fun c : Fin (orderOf target.character) × Bool × Bool => c.2) he)

/-- Characters contributing to the fixed positive combination in §6.3. -/
noncomputable def selmerKeptCharacters (target : BundledDirichletCharacter) (e : ℕ) :
    Finset (ExcessCharacter (SelmerHostBaseGroup target e)) :=
  Finset.univ.map (selmerUntwistedEmbedding target e)

@[simp] theorem selmerSurvivor_zero (target : BundledDirichletCharacter) (e : ℕ) :
    selmerSurvivor target e 0 false false = 0 := by
  apply AddChar.eq_zero_iff.mpr
  intro u
  simp

theorem selmerKeptCharacters_zero_mem (target : BundledDirichletCharacter) (e : ℕ) :
    0 ∈ selmerKeptCharacters target e := by
  let _ : NeZero (target.modulus : ℕ) := ⟨target.modulus.pos.ne'⟩
  exact Finset.mem_map.mpr ⟨⟨0, orderOf_pos _⟩, Finset.mem_univ _, selmerSurvivor_zero target e⟩

theorem selmerKeptCharacters_subset_survivors
    {target : BundledDirichletCharacter} {e : ℕ} [Fintype (SelmerHostBaseGroup target e)]
    (d : ExcessAverageData (SelmerHostBaseGroup target e))
    (hgroup : d.subgroup = selmerAveragingSubgroup target e) :
    selmerKeptCharacters target e ⊆ d.survivors := by
  intro ψ hψ
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hψ
  rw [ExcessAverageData.mem_survivors, hgroup]
  exact selmerSurvivor_trivial_on_averagingSubgroup target e i false false

theorem selmerKeptCharacters_sign
    {target : BundledDirichletCharacter} {e : ℕ}
    (ψ : ExcessCharacter (SelmerHostBaseGroup target e))
    (hψ : ψ ∈ selmerKeptCharacters target e) : ψ (1, 0, 0) = 1 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hψ
  change selmerSurvivor target e i false false (1, 0, 0) = 1
  simp [show (0 : SelmerHostBaseGroup target e).toMul = 1 from rfl]

/-- The characters surviving the average but omitted from the main term are
indexed by the three nontrivial choices of auxiliary twists for each target power. -/
theorem selmerSurvivingAuxiliary_eq {target : BundledDirichletCharacter} {e : ℕ}
    [Fintype (SelmerHostBaseGroup target e)]
    (d : ExcessAverageData (SelmerHostBaseGroup target e))
    (hgroup : d.subgroup = selmerAveragingSubgroup target e)
    (hkept : d.kept = selmerKeptCharacters target e) :
    d.survivors \ d.kept = Finset.univ.map (selmerAuxiliaryEmbedding target e) := by
  ext ψ
  rw [Finset.mem_sdiff, ExcessAverageData.mem_survivors, hgroup, hkept, Finset.mem_map]
  constructor
  · rintro ⟨hψ, hnot⟩
    obtain ⟨i, ds, qs, hi, hval⟩ := selmerSurvivor_eq_target_pow_mul_signs target e ψ hψ
    have hchar : selmerSurvivor target e i qs ds = ψ := by
      ext g
      rw [selmerSurvivor_apply, hval]
    have hsign : (qs, ds) ≠ (false, false) := by
      intro h
      have hq : qs = false := congrArg Prod.fst h
      have hd : ds = false := congrArg Prod.snd h
      apply hnot
      refine Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
      change selmerSurvivor target e i false false = ψ
      simpa only [hq, hd] using hchar
    exact ⟨⟨⟨i, hi⟩, ⟨(qs, ds), hsign⟩⟩, Finset.mem_univ _, hchar⟩
  · rintro ⟨i, _, rfl⟩
    refine ⟨selmerSurvivor_trivial_on_averagingSubgroup target e _ _ _, ?_⟩
    intro hm
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
    have htag := selmerSurvivor_injective target e (a₁ := (j, false, false)) (a₂ := (i.1, i.2.val)) hj
    exact i.2.property (congrArg Prod.snd htag).symm

theorem selmerSurvivors_card {target : BundledDirichletCharacter} {e : ℕ}
    [Fintype (SelmerHostBaseGroup target e)]
    (d : ExcessAverageData (SelmerHostBaseGroup target e))
    (hgroup : d.subgroup = selmerAveragingSubgroup target e)
    (hkept : d.kept = selmerKeptCharacters target e) :
    d.survivors.card = 4 * orderOf target.character := by
  have hh := Finset.card_sdiff_add_card_eq_card
    (show d.kept ⊆ d.survivors from hkept.symm ▸ selmerKeptCharacters_subset_survivors d hgroup)
  rw [selmerSurvivingAuxiliary_eq d hgroup hkept, hkept, selmerKeptCharacters] at hh
  simp only [Finset.card_map, Finset.card_univ, selmerAuxiliaryIndex_card, Fintype.card_fin] at hh
  omega

theorem selmerSurvivor_auxiliary_ne_zero (target : BundledDirichletCharacter) (e : ℕ)
    (i : SelmerAuxiliaryIndex target) : selmerAuxiliaryEmbedding target e i ≠ 0 := by
  let _ : NeZero (target.modulus : ℕ) := ⟨target.modulus.pos.ne'⟩
  intro h
  rw [← selmerSurvivor_zero target e] at h
  have htag := selmerSurvivor_injective target e
    (a₁ := (i.1, i.2.val)) (a₂ := (⟨0, orderOf_pos _⟩, false, false)) h
  exact i.2.property (congrArg Prod.snd htag)

section Auxiliary

variable (target : BundledDirichletCharacter) (q d : ℕ+)
  [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime]
  (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3)

/-- The primitive auxiliary family is indexed independently of the varying host level. -/
noncomputable def selmerAuxiliaryCharacter (i : SelmerAuxiliaryIndex target) :
    BundledDirichletCharacter :=
  selmerTwistedCharacter target q d hq₄ hd₄ i.1 i.2.val.1 i.2.val.2

variable {e : ℕ} (hq : (selmerBaseModulus target e).Coprime q)
  (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)

include hq hd in
theorem selmerAuxiliaryCharacter_isPrimitive_ne_one (i : SelmerAuxiliaryIndex target) :
    (selmerAuxiliaryCharacter target q d hq₄ hd₄ i).character.IsPrimitive ∧
      (selmerAuxiliaryCharacter target q d hq₄ hd₄ i).character ≠ 1 := by
  rw [selmerAuxiliaryCharacter, ← selmerHostInducingCharacter_eq_twistedCharacter
    target e q d hq₄ hd₄ hq hd]
  exact ⟨selmerHostInducingCharacter_isPrimitive _ _,
    selmerHostInducingCharacter_ne_one _ (selmerSurvivor_auxiliary_ne_zero target e i)⟩

theorem selmerAuxiliaryValue_eq
    [Fintype (SelmerHostBaseGroup target e)]
    (avg : ExcessAverageData (SelmerHostBaseGroup target e))
    (hgroup : avg.subgroup = selmerAveragingSubgroup target e)
    (hkept : avg.kept = selmerKeptCharacters target e)
    (prime : PrimeExcessData (SelmerHostBaseGroup target e))
    (hprime : HostInducingConditions prime
      (selmerHostInducingCharacter (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm))
    (x : ℝ) :
    avg.auxiliaryValue prime.smoothed x =
      ∑ i, ‖complexSmoothedCharacterSum (selmerAuxiliaryCharacter target q d hq₄ hd₄ i) x‖ := by
  rw [ExcessAverageData.auxiliaryValue, selmerSurvivingAuxiliary_eq avg hgroup hkept, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  rw [hprime.smoothed_eq_inducing (selmerSurvivor_auxiliary_ne_zero target e i)]
  change ‖complexSmoothedCharacterSum (selmerHostInducingCharacter
    (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm
    (selmerSurvivor target e i.1 i.2.val.1 i.2.val.2)) x‖ = _
  rw [selmerHostInducingCharacter_eq_twistedCharacter]
  rfl

private theorem selmerUntwisted_trivial_on_base_only_at_zero
    (e : ℕ) (i : Fin (orderOf target.character))
    (h : ∀ u, selmerUntwistedEmbedding target e i (0, 0, u) = 1) :
    (i : ℕ) = 0 := by
  by_contra hi
  apply pow_ne_one_of_lt_orderOf hi i.isLt
  apply MulChar.ext
  intro v
  let _ : NeZero (selmerBaseModulus target e) := ⟨(selmerBaseModulus_pos target e).ne'⟩
  have hdiv : (target.modulus : ℕ) ∣ selmerBaseModulus target e := Nat.dvd_lcm_right _ _
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hdiv v
  have hvalue : (selmerBaseTarget target e (QuotientGroup.mk u) : ℂ) = target.character v := by
    rw [selmerBaseTarget_mk]
    change (target.character.toUnitHom (ZMod.unitsMap hdiv u) : ℂ) = _
    rw [hu, MulChar.coe_toUnitHom]
  have ht := h (Additive.ofMul (QuotientGroup.mk u))
  change selmerSurvivor target e i false false (0, 0, Additive.ofMul (QuotientGroup.mk u)) = 1 at ht
  simp only [selmerSurvivor_apply, Bool.toNat_false, pow_zero, mul_one] at ht
  change (selmerBaseTarget target e (QuotientGroup.mk u) : ℂ) ^ (i : ℕ) = 1 at ht
  simpa only [hvalue, MulChar.pow_apply_coe, MulChar.one_apply_coe] using ht

theorem selmerMainValue_eq
    [Fintype (SelmerHostBaseGroup target e)]
    (avg : ExcessAverageData (SelmerHostBaseGroup target e))
    (hkept : avg.kept = selmerKeptCharacters target e)
    (hweight : avg.mainWeight = (3 * (orderOf target.character : ℝ) + 1)⁻¹)
    (prime : PrimeExcessData (SelmerHostBaseGroup target e))
    (hprime : HostInducingConditions prime
      (selmerHostInducingCharacter (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm))
    (x : ℝ) :
    avg.mainValue prime.smoothed x =
      smoothedCombination
        (fun i : Fin (orderOf target.character - 1) => selmerFixedCharacter target ((i : ℕ) + 1))
        (fun _ => (3 * (orderOf target.character : ℝ) + 1)⁻¹) x := by
  let _ : NeZero (target.modulus : ℕ) := ⟨target.modulus.pos.ne'⟩
  let o := orderOf target.character
  have ho₀ : 0 < o := orderOf_pos _
  have ho : o = o - 1 + 1 := by omega
  let f (i : Fin o) : ℝ := avg.coefficient (selmerUntwistedEmbedding target e i) *
    (prime.smoothed (selmerUntwistedEmbedding target e i) x).re
  rw [ExcessAverageData.mainValue, hkept, selmerKeptCharacters, Finset.sum_map]
  change (∑ i, f i) = _
  have hreindex : (∑ i, f i) = ∑ j : Fin (o - 1 + 1), f ((finCongr ho).symm j) :=
    Fintype.sum_equiv (finCongr ho) _ _ (fun _ => by simp)
  rw [hreindex, Fin.sum_univ_succ, smoothedCombination]
  congr 1
  · have hz : selmerUntwistedEmbedding target e ((finCongr ho).symm 0) = 0 :=
      selmerSurvivor_zero target e
    dsimp only [f]
    rw [hz]
    simp [ExcessAverageData.coefficient]
  · apply Finset.sum_congr rfl
    intro j _
    let i := (finCongr ho).symm j.succ
    let ψ := selmerUntwistedEmbedding target e i
    have hi : (i : ℕ) = (j : ℕ) + 1 := rfl
    have hbase : ¬ ∀ u, ψ (0, 0, u) = 1 := by
      intro h
      have hzero := selmerUntwisted_trivial_on_base_only_at_zero target e i h
      omega
    have hψ : ψ ≠ 0 := fun he => hbase (fun u => by simp [he])
    change avg.coefficient ψ * (prime.smoothed ψ x).re = _
    rw [ExcessAverageData.coefficient, ite_eq_right hbase, hweight, hprime.smoothed_eq_inducing hψ]
    change _ * (complexSmoothedCharacterSum (selmerHostInducingCharacter
      (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm
        (selmerSurvivor target e i false false)) x).re = _
    rw [selmerHostInducingCharacter_untwisted, hi]

end Auxiliary

/-- The primes selected at the base scale are coprime to the host base level
once the modulus of the fixed target is in the small-prime range. -/
theorem SelmerWindowPair.coprime_host_base_modulus
    {ε base : ℝ} {q d : ℕ+} (pair : SelmerWindowPair ε base q d)
    (target : BundledDirichletCharacter) (e : ℕ)
    (hsize : ((target.modulus : ℕ) : ℝ) ≤ base ^ (ε / 5)) :
    (selmerBaseModulus target e).Coprime q ∧
      (selmerBaseModulus target e * (q : ℕ)).Coprime d := by
  let z := base ^ (ε / 5)
  have hz : 0 ≤ z := Real.rpow_nonneg (by linarith [pair.base_ge_two]) _
  have hsq := sq_nonneg (z - 2)
  have hlower : z < Real.exp (z / 2) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ z / 2 by linarith)
    nlinarith
  have hq₀ : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  have hqlarge : z < (q : ℕ) :=
    hlower.trans ((Real.lt_log_iff_exp_lt hq₀).mp pair.q_lower)
  have hqM : ¬ (q : ℕ) ∣ (target.modulus : ℕ) := by
    intro h
    have hle : ((q : ℕ) : ℝ) ≤ (target.modulus : ℕ) := by
      exact_mod_cast Nat.le_of_dvd target.modulus.pos h
    exact (not_le_of_gt hqlarge) (hle.trans hsize)
  have hd₂ : (d : ℕ) ≠ 2 := by have := pair.d_residue; omega
  have hq₂ : (q : ℕ) ≠ 2 := by have := pair.q_residue; omega
  have hdM : ¬ (d : ℕ) ∣ (target.modulus : ℕ) := by
    intro h
    have hle : ((d : ℕ) : ℝ) ≤ (target.modulus : ℕ) := by
      exact_mod_cast Nat.le_of_dvd target.modulus.pos h
    have hd₁ := pair.small_prime_dvd d pair.d_prime (pair.d_prime.odd_of_ne_two hd₂) (hle.trans hsize)
    exact pair.d_prime.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl (d : ℕ))).mpr hd₁)
  have hdq : (d : ℕ) ≠ (q : ℕ) := by
    intro h
    have hdiv : (d : ℕ) ∣ (d : ℕ) + 1 := h.symm ▸ pair.q_dvd
    exact pair.d_prime.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl (d : ℕ))).mpr hdiv)
  refine ⟨selmerBaseModulus_coprime_of_prime target e pair.q_prime hq₂
    (pair.q_prime.coprime_iff_not_dvd.mpr hqM), ?_⟩
  exact (selmerBaseModulus_coprime_of_prime target e pair.d_prime hd₂
    (pair.d_prime.coprime_iff_not_dvd.mpr hdM)).mul_left
    ((Nat.coprime_primes pair.q_prime pair.d_prime).mpr hdq.symm)

end Riemann
