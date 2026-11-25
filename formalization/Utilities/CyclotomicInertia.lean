module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Data.Nat.Factorization.Basic
import Utilities.InertiaRestriction
import Utilities.NumberFieldTorsion

@[expose] public section

open scoped NumberField IntermediateField
open IsCyclotomicExtension

namespace Utilities

/-- Inertia at a prime in a Galois subfield is the image of inertia upstairs. -/
theorem numberField_inertia_map_restrictNormal {K : Type*} [Field K] [NumberField K]
    [IsGalois ℚ K] (F : IntermediateField ℚ K) [Normal ℚ F]
    (Q : Ideal (𝓞 F)) (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver Q] :
    (P.inertia (K ≃ₐ[ℚ] K)).map (AlgEquiv.restrictNormalHom F) = Q.inertia (F ≃ₐ[ℚ] F) := by
  exact numberField_inertia_map_restrictNormal_tower (K := ℚ) Q P

/-- Inertia in a cyclotomic extension is trivial on any cyclotomic subfield
whose conductor is prime to the residue characteristic. -/
theorem cyclotomic_inertia_map_le_unitsMap_ker {n m p : ℕ} [NeZero n] [NeZero m]
    [Fact p.Prime] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hmn : m ∣ n) (hm : ¬ p ∣ m) :
    (P.inertia (K ≃ₐ[ℚ] K)).map (Rat.galEquivZMod n K).toMonoidHom ≤
      (ZMod.unitsMap hmn).ker := by
  have hfactor : ∃ r, n = m * r := hmn
  obtain ⟨r, hr⟩ := hfactor
  let ζ := zeta n ℚ K ^ r
  have hζ : IsPrimitiveRoot ζ m := (zeta_spec n ℚ K).pow (NeZero.pos n)
    (hr.trans (mul_comm m r))
  let F := ℚ⟮ζ⟯
  let hF : IsCyclotomicExtension {m} ℚ F :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let localGalois : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  let localGaloisF : IsGalois ℚ F := IsCyclotomicExtension.isGalois {m} ℚ F
  let Q := P.under (𝓞 F)
  let localOver : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    constructor
    change Ideal.span {(p : ℤ)} = (P.under (𝓞 F)).under ℤ
    rw [Ideal.under_under, ← P.over_def (Ideal.span {(p : ℤ)})]
  have hcard : Nat.card (Q.inertia (F ≃ₐ[ℚ] F)) = 1 :=
    (numberField_ramificationIdx_eq_inertia_card F p Fact.out Q).symm.trans
      (Rat.ramificationIdx_eq_of_not_dvd p F Q hm)
  have hbot := (Q.inertia (F ≃ₐ[ℚ] F)).eq_bot_of_card_eq hcard
  rintro _ ⟨σ, hσ, rfl⟩
  have hrestrict : σ.restrictNormal F = 1 := by
    have hmem : σ.restrictNormal F ∈ Q.inertia (F ≃ₐ[ℚ] F) := by
      rw [← numberField_inertia_map_restrictNormal F Q P]
      exact Subgroup.mem_map_of_mem _ hσ
    rwa [hbot, Subgroup.mem_bot] at hmem
  change ZMod.unitsMap hmn (Rat.galEquivZMod n K σ) = 1
  rw [← Rat.galEquivZMod_restrictNormal_apply n K F hmn σ, hrestrict, map_one]

/-- The inertia group is trivial at primes outside the cyclotomic conductor. -/
theorem cyclotomic_inertia_eq_bot_of_not_dvd {n p : ℕ} [NeZero n] [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hp : ¬ p ∣ n) : P.inertia (K ≃ₐ[ℚ] K) = ⊥ := by
  let _ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  apply Subgroup.eq_bot_of_card_eq
  rw [← numberField_ramificationIdx_eq_inertia_card K p Fact.out P,
    Rat.ramificationIdx_eq_of_not_dvd p K P hp]

/-- If `n = p^(k+1) * m` with `p ∤ m`, the inertia subgroup in cyclotomic
unit coordinates is exactly the kernel of reduction modulo `m`. -/
theorem cyclotomic_inertia_map_eq_unitsMap_ker {n m p k : ℕ} [NeZero n] [NeZero m]
    [Fact p.Prime] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    (P.inertia (K ≃ₐ[ℚ] K)).map (Rat.galEquivZMod n K).toMonoidHom =
      (ZMod.unitsMap (hn ▸ dvd_mul_left m (p ^ (k + 1)))).ker := by
  let f := ZMod.unitsMap (hn ▸ dvd_mul_left m (p ^ (k + 1)))
  let localGalois : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  have hp : p.Prime := Fact.out
  apply Subgroup.eq_of_le_of_card_ge (cyclotomic_inertia_map_le_unitsMap_ker K P _ hm)
  have hcardMap := Subgroup.card_map_of_injective (K := P.inertia (K ≃ₐ[ℚ] K))
    (f := (Rat.galEquivZMod n K).toMonoidHom) (Rat.galEquivZMod n K).injective
  rw [hcardMap, ← numberField_ramificationIdx_eq_inertia_card K p hp P,
    Rat.ramificationIdx_eq n K P hn hm]
  change Nat.card f.ker ≤ p ^ k * (p - 1)
  have hindex : f.ker.index = m.totient := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ (ZMod.unitsMap_surjective _),
      Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have htotient : n.totient = p ^ k * (p - 1) * m.totient := by
    rw [hn, Nat.totient_mul ((hp.coprime_iff_not_dvd.mpr hm).pow_left (k + 1)),
      Nat.totient_prime_pow_succ hp]
  have hsize := Subgroup.card_mul_index f.ker
  rw [hindex, Nat.card_eq_fintype_card (α := (ZMod n)ˣ), ZMod.card_units_eq_totient, htotient] at hsize
  exact (Nat.mul_right_cancel (Nat.totient_pos.mpr (NeZero.pos m)) hsize).le

/-- Cyclotomic inertia at `p` is the kernel of reduction to the
prime-to-`p` part of the level. -/
theorem cyclotomic_inertia_map_eq_ordCompl_ker {n p : ℕ} [NeZero n] [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (P.inertia (K ≃ₐ[ℚ] K)).map (Rat.galEquivZMod n K).toMonoidHom =
      (ZMod.unitsMap (Nat.ordCompl_dvd n p)).ker := by
  let m := ordCompl[p] n
  have hp : p.Prime := Fact.out
  let _ : NeZero m := ⟨(Nat.ordCompl_pos p (NeZero.ne n)).ne'⟩
  have hm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (NeZero.ne n)
  by_cases hval : n.factorization p = 0
  · have heq : m = n := by simp only [m, hval, pow_zero, Nat.div_one]
    have hpn : ¬ p ∣ n := heq ▸ hm
    rw [cyclotomic_inertia_eq_bot_of_not_dvd K P hpn, Subgroup.map_bot]
    have hker (m' : ℕ) (h : m' = n) (hd : m' ∣ n) : (ZMod.unitsMap hd).ker = ⊥ := by
      subst m'
      rw [ZMod.unitsMap_self, MonoidHom.ker_id]
    exact (hker m heq (Nat.ordCompl_dvd n p)).symm
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hval
    have hn : n = p ^ (k + 1) * m := by
      have heq : n = p ^ n.factorization p * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      simpa only [hk] using heq
    exact cyclotomic_inertia_map_eq_unitsMap_ker K P hn hm

end Utilities
