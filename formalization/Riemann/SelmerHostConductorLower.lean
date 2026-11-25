module

public import Riemann.SelmerMinusBounds
import Mathlib.RingTheory.Ideal.Int
import Utilities.CyclotomicInertia
import Utilities.CyclotomicRamificationSupport
import Utilities.ZModUnits

@[expose] public section

open Utilities
open scoped NumberField

namespace Riemann

private theorem selmer_auxPrime_dvd_conductor
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    {p m : ℕ} [Fact p.Prime] (hp₄ : p % 4 = 3)
    (hmp : m.Coprime p) (hN : selmerHostModulus target e q d = m * p)
    (hpN : p ∣ selmerHostModulus target e q d)
    (hfix : selmerHostFixingUnits target e q d ≤
      (selmerSquareUnits p).comap (ZMod.unitsMap hpN)) :
    p ∣ selmerHostConductor target e q d := by
  let N := selmerHostModulus target e q d
  let K := CyclotomicField N ℚ
  let E := selmerHostField target e q d
  let : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let : NeZero (N : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  let : IsCyclotomicExtension {N} ℚ K := CyclotomicField.isCyclotomicExtension N ℚ
  let := selmerCyclotomic_isAbelianGalois target e q d
  let := selmerHostField_isAbelianGalois target e q d
  let M : Ideal ℤ := Ideal.span {(p : ℤ)}
  obtain ⟨P, hP, hPM⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral M (S := 𝓞 K)
  let : P.IsPrime := hP.isPrime
  let Q := P.under (𝓞 E)
  let : Q.IsPrime := hP.isPrime.comap (algebraMap (𝓞 E) (𝓞 K))
  let : P.LiesOver Q := Ideal.over_under P
  let : Q.LiesOver M := by
    constructor
    change M = (P.under (𝓞 E)).under ℤ
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over
  have hm : ¬ p ∣ m := (Fact.out : p.Prime).coprime_iff_not_dvd.mp hmp.symm
  let : NeZero m := ⟨fun h => hm (h ▸ dvd_zero _)⟩
  have hNeq : N = m * p := hN
  have hmN : m ∣ N := by rw [hNeq]; exact dvd_mul_right m p
  let c := Units.mapEquiv (ZMod.ringEquivCongr hNeq).toMulEquiv
  let u : (ZMod N)ˣ := c.symm ((zmodUnitsCRT hmp).symm (1, -1))
  have hu : ZMod.unitsMap hmN u = 1 ∧ ZMod.unitsMap hpN u = -1 := by
    have hcu : zmodUnitsCRT hmp (c u) = (1, -1) := by simp [u]
    dsimp only [c] at hcu
    have hdiv : m * p ∣ N := by rw [hNeq]
    rw [zmodUnitsCRT_apply, zmodUnitsCongr_apply _ hdiv, zmodUnitsMap_comp_apply,
      zmodUnitsMap_comp_apply] at hcu
    exact ⟨congrArg Prod.fst hcu, congrArg Prod.snd hcu⟩
  let γ := selmerCyclotomicUnitsEquiv target e q d
  let τ := γ.symm u
  have hker : (P.inertia (K ≃ₐ[ℚ] K)).map γ.toMonoidHom = (ZMod.unitsMap hmN).ker :=
    cyclotomic_inertia_map_eq_unitsMap_ker K P
      (by simpa [mul_comm] using hN : N = p ^ (0 + 1) * m) hm
  have hτ : τ ∈ P.inertia (K ≃ₐ[ℚ] K) := by
    have hu' : u ∈ (ZMod.unitsMap hmN).ker := hu.1
    rw [← hker] at hu'
    obtain ⟨σ, hσ, hσu⟩ := Subgroup.mem_map.mp hu'
    have heq : σ = τ := γ.injective (hσu.trans (γ.apply_symm_apply u).symm)
    exact heq ▸ hσ
  have hτE : τ.restrictNormal E ∈ Q.inertia (E ≃ₐ[ℚ] E) := by
    rw [← numberField_inertia_map_restrictNormal E Q P]
    exact Subgroup.mem_map_of_mem _ hτ
  have hτ₁ : τ.restrictNormal E ≠ 1 := by
    intro h
    have hu₁ : (QuotientGroup.mk u : (ZMod N)ˣ ⧸ selmerHostFixingUnits target e q d) = 1 := by
      apply (selmerHostGalQuotient target e q d).injective
      rw [selmerHostGalQuotient_mk, map_one]
      exact h
    have huSq := hfix ((QuotientGroup.eq_one_iff _).mp hu₁)
    change ZMod.unitsMap hpN u ∈ selmerSquareUnits p at huSq
    rw [hu.2] at huSq
    exact selmerSquareClass_neg_one_ne_one hp₄ ((QuotientGroup.eq_one_iff _).mpr huSq)
  have hram : 1 < Q.ramificationIdx ℤ := by
    rw [numberField_ramificationIdx_eq_inertia_card E p Fact.out Q]
    apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
    refine ⟨Nat.card_pos.ne', fun h => ?_⟩
    have hb := (Q.inertia (E ≃ₐ[ℚ] E)).eq_bot_of_card_eq h
    exact hτ₁ (by simpa [hb] using hτE)
  let f := selmerHostConductor target e q d
  let : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let : IsCyclotomicExtension {f} ℚ (CyclotomicField f ℚ) :=
    CyclotomicField.isCyclotomicExtension f ℚ
  exact prime_dvd_cyclotomicModulus_of_ramification (N := f)
    (selmerHostConductorEmbedding target e q d) Q hram

/-- The conductor contains both auxiliary primes from the prepared Selmer host. -/
theorem selmerHostConductor_auxPrimes_dvd (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (hpair : SelmerEstimatePrimePair target q d) :
    (q : ℕ) * (d : ℕ) ∣ selmerHostConductor target e q d := by
  let m := selmerBaseModulus target e
  have hq₂ : (q : ℕ) ≠ 2 := by have := hpair.q_residue; omega
  have hd₂ : (d : ℕ) ≠ 2 := by have := hpair.d_residue; omega
  have hqd : (q : ℕ) ≠ d := by
    have := hpair.q_residue
    have := hpair.d_residue
    omega
  have hcop := (Nat.coprime_primes hpair.q_prime hpair.d_prime).mpr hqd
  obtain ⟨hqN₀, hdN₀⟩ := Nat.coprime_mul_iff_left.mp hpair.coprime
  have hq := selmerBaseModulus_coprime_of_prime target e hpair.q_prime hq₂ hqN₀
  have hd := selmerBaseModulus_coprime_of_prime target e hpair.d_prime hd₂ hdN₀
  have hN := selmerHostModulus_eq_mul target e q d hq (hd.mul_left hcop)
  let : Fact (q : ℕ).Prime := ⟨hpair.q_prime⟩
  let : Fact (d : ℕ).Prime := ⟨hpair.d_prime⟩
  have hq₄ : (q : ℕ) % 4 = 3 := by have := hpair.q_residue; omega
  have hd₄ : (d : ℕ) % 4 = 3 := by have := hpair.d_residue; omega
  have hqdvd := dvd_trans (Nat.dvd_lcm_right m (q : ℕ)) (Nat.dvd_lcm_left _ (d : ℕ))
  have hddvd := Nat.dvd_lcm_right (Nat.lcm m q) (d : ℕ)
  apply hcop.mul_dvd_of_dvd_of_dvd
  · apply selmer_auxPrime_dvd_conductor target e q d hq₄ (hq.mul_left hcop.symm)
      (hN.trans (by ring)) hqdvd
    exact inf_le_left.trans inf_le_right
  · apply selmer_auxPrime_dvd_conductor target e q d hd₄ (hd.mul_left hcop) hN hddvd
    exact inf_le_right

/-- The host level is polynomial in its conductor, as required by the
generic count in Proposition 17.14. -/
theorem selmerHostModulus_le_target_mul_conductor_sq
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hpair : SelmerEstimatePrimePair target q d) :
    selmerHostModulus target e q d ≤ (target.modulus : ℕ) * selmerHostConductor target e q d ^ 2 := by
  let f := selmerHostConductor target e q d
  have hqd : (q : ℕ) * (d : ℕ) ≤ f :=
    Nat.le_of_dvd (selmerHostConductor_pos target e q d)
      (selmerHostConductor_auxPrimes_dvd target e q d hpair)
  have hpow : 2 ^ (e + 2) ≤ f := by
    have hn := selmerHostDegree_le_conductor target e q d
    rw [selmerHostDegree_eq_dyadic_mul target e q d hpair] at hn
    let : NeZero (selmerBaseModulus target e) := ⟨(selmerBaseModulus_pos target e).ne'⟩
    exact (Nat.le_mul_of_pos_left _ Nat.card_pos).trans hn
  calc
    _ ≤ 2 ^ (e + 2) * (target.modulus : ℕ) * (q : ℕ) * (d : ℕ) :=
      selmerHostModulus_le_product target e q d
    _ = (2 ^ (e + 2) * (target.modulus : ℕ)) * ((q : ℕ) * (d : ℕ)) := by ring
    _ ≤ (2 ^ (e + 2) * (target.modulus : ℕ)) * f :=
      Nat.mul_le_mul_left _ hqd
    _ ≤ (f * (target.modulus : ℕ)) * f := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow)
    _ = _ := by ring

/-- The ambient level in Proposition 17.14 is even and at least sixteen
for the admissible dyadic range. -/
theorem sixteen_dvd_selmerHostModulus (target : BundledDirichletCharacter)
    {e : ℕ} (he : 2 ≤ e) (q d : ℕ+) :
    16 ∣ selmerHostModulus target e q d := by
  have hp : (2 : ℕ) ^ 4 ∣ 2 ^ (e + 2) := Nat.pow_dvd_pow _ (by omega)
  exact hp.trans ((Nat.dvd_lcm_left _ _).trans
    ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _)))

/-- The modulus-based polynomial budget for the generic count can be
written as a conductor-based budget on the auxiliary-prime range. -/
theorem selmerHostModulus_cutoff_pow_le_conductor
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hpair : SelmerEstimatePrimePair target q d) (hq : (target.modulus : ℕ) ≤ q)
    {t : ℕ} (ht : 0 < t) (C : ℕ) :
    ((selmerHostModulus target e q d : ℝ) * t) ^ C ≤
      ((selmerHostConductor target e q d : ℝ) * t) ^ (3 * C) := by
  let f := selmerHostConductor target e q d
  have hqf : (q : ℕ) ≤ f :=
    Nat.le_of_dvd (selmerHostConductor_pos target e q d)
      ((dvd_mul_right (q : ℕ) (d : ℕ)).trans (selmerHostConductor_auxPrimes_dvd target e q d hpair))
  have hN : selmerHostModulus target e q d ≤ f ^ 3 := by
    refine (selmerHostModulus_le_target_mul_conductor_sq target e q d hpair).trans ?_
    rw [show f ^ 3 = f * f ^ 2 by ring]
    exact Nat.mul_le_mul_right _ (hq.trans hqf)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hN' : (selmerHostModulus target e q d : ℝ) ≤ (f : ℝ) ^ 3 := by exact_mod_cast hN
  have hmul : (selmerHostModulus target e q d : ℝ) * t ≤ ((f : ℝ) * t) ^ 3 := by
    rw [mul_pow]
    exact mul_le_mul hN' (le_self_pow₀ ht' (by decide)) (by positivity) (by positivity)
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) hmul C

/-- An odd prime outside the target level and below both auxiliary primes
does not divide the host modulus. -/
theorem selmerHostModulus_coprime_of_prime_lt_auxiliary
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hpair : SelmerEstimatePrimePair target q d) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (htarget : ¬ ℓ ∣ (target.modulus : ℕ))
    (hq : ℓ < (q : ℕ)) (hd : ℓ < (d : ℕ)) :
    ℓ.Coprime (selmerHostModulus target e q d) := by
  have hbase := selmerBaseModulus_coprime_of_prime target e hℓ hodd
    (hℓ.coprime_iff_not_dvd.mpr htarget)
  apply hℓ.coprime_iff_not_dvd.mpr
  intro h
  unfold selmerHostModulus at h
  rcases hℓ.dvd_mul.mp (h.trans (Nat.lcm_dvd_mul _ _)) with h | h
  · rcases hℓ.dvd_mul.mp (h.trans (Nat.lcm_dvd_mul _ _)) with hb | hq'
    · exact (hℓ.coprime_iff_not_dvd.mp hbase.symm) hb
    · exact hq.ne ((Nat.prime_dvd_prime_iff_eq hℓ hpair.q_prime).mp hq')
  · exact hd.ne ((Nat.prime_dvd_prime_iff_eq hℓ hpair.d_prime).mp h)

/-- Outside the fixed target level, small odd primes lie outside the host
level whenever both auxiliary primes are beyond the residue-prime range. -/
theorem selmerHostModulus_coprime_residuePrime
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hpair : SelmerEstimatePrimePair target q d) {ℓ t : ℕ}
    (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (htarget : ¬ ℓ ∣ (target.modulus : ℕ))
    (hsmall : ℓ ≤ 2 * t) (hq : 2 * t < (q : ℕ)) (hd : 2 * t < (d : ℕ)) :
    ℓ.Coprime (selmerHostModulus target e q d) :=
  selmerHostModulus_coprime_of_prime_lt_auxiliary target e q d hpair hℓ hodd htarget
    (hsmall.trans_lt hq) (hsmall.trans_lt hd)

end Riemann
