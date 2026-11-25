module

public import Riemann.SelmerHostConductorLower
public import Utilities.CyclotomicInertia
import Utilities.ZModUnits
import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

open Utilities
open scoped NumberField

namespace Riemann

/-- A character trivial on the host fixing subgroup has order dividing
the degree of the actual host. -/
theorem orderOf_selmerHostCharacter_dvd_degree
    {O : Type*} [CommRing O] (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (ψ : DirichletCharacter O (selmerHostModulus target e q d))
    (hψ : selmerHostFixingUnits target e q d ≤ ψ.toUnitHom.ker) :
    orderOf ψ ∣ Module.finrank ℚ (selmerHostField target e q d) := by
  let H := selmerHostFixingUnits target e q d
  let := selmerHostField_isAbelianGalois target e q d
  have hindex : H.index = Module.finrank ℚ (selmerHostField target e q d) := by
    change Nat.card _ = _
    rw [Nat.card_congr (selmerHostGalQuotient target e q d).toEquiv,
      IsGalois.card_aut_eq_finrank]
  rw [← hindex]
  apply orderOf_dvd_of_pow_eq_one
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have hu := hψ (Subgroup.pow_index_mem H u)
  rw [MonoidHom.mem_ker, map_pow] at hu
  exact congrArg Units.val hu

/-- Away from the target character's order, an odd prime does not divide
the order of any host character. -/
theorem odd_prime_not_dvd_selmerHostCharacter_order
    {O : Type*} [CommRing O] (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hpair : SelmerEstimatePrimePair target q d) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (horder : ¬ℓ ∣ orderOf target.character)
    (ψ : DirichletCharacter O (selmerHostModulus target e q d))
    (hψ : selmerHostFixingUnits target e q d ≤ ψ.toUnitHom.ker) :
    ¬ℓ ∣ orderOf ψ := fun h =>
  horder (odd_prime_dvd_order_of_dvd_selmerHostDegree target e q d hpair hℓ hodd
    (h.trans (orderOf_selmerHostCharacter_dvd_degree target e q d ψ hψ)))

/-- The local character over the primes outside the target modulus has
order at most two on cyclotomic inertia. -/
theorem selmerHostCharacter_sq_eq_one_of_ordCompl_units
    {O : Type*} [CommRing O] (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (htarget : ¬ℓ ∣ (target.modulus : ℕ))
    (ψ : DirichletCharacter O (selmerHostModulus target e q d))
    (hψ : selmerHostFixingUnits target e q d ≤ ψ.toUnitHom.ker)
    (u : (ZMod (selmerHostModulus target e q d))ˣ)
    (hu : ZMod.unitsMap (Nat.ordCompl_dvd (selmerHostModulus target e q d) ℓ) u = 1) :
    (ψ.toUnitHom u) ^ 2 = 1 := by
  let base := selmerBaseModulus target e
  let N := selmerHostModulus target e q d
  have hbN : base ∣ N := (Nat.dvd_lcm_left base q).trans (Nat.dvd_lcm_left _ d)
  have hb : ¬ℓ ∣ base := hℓ.coprime_iff_not_dvd.mp
    (selmerBaseModulus_coprime_of_prime target e hℓ hodd (hℓ.coprime_iff_not_dvd.mpr htarget)).symm
  have hbcompl := Nat.dvd_ordCompl_of_dvd_not_dvd hbN hb
  have hred : ZMod.unitsMap hbN u = 1 := by
    rw [← zmodUnitsMap_comp_apply hbcompl (Nat.ordCompl_dvd N ℓ), hu, map_one]
  have hqN : (q : ℕ) ∣ N := (Nat.dvd_lcm_right base q).trans (Nat.dvd_lcm_left _ d)
  have hdN : (d : ℕ) ∣ N := Nat.dvd_lcm_right _ _
  have hfix : u ^ 2 ∈ selmerHostFixingUnits target e q d := by
    change u ^ 2 ∈ (selmerBaseFixingUnits target e).comap (ZMod.unitsMap hbN) ⊓
      (selmerSquareUnits q).comap (ZMod.unitsMap hqN) ⊓
      (selmerSquareUnits d).comap (ZMod.unitsMap hdN)
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, map_pow]
    refine ⟨⟨by rw [hred, one_pow]; exact Subgroup.one_mem _, ?_⟩, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_top _, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_top _, rfl⟩
  have h := hψ hfix
  rwa [MonoidHom.mem_ker, map_pow] at h

/-- The order-two restriction above on the actual cyclotomic inertia group. -/
theorem selmerHostCharacter_sq_eq_one_on_cyclotomicInertia
    {O : Type*} [CommRing O] (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    {ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ ≠ 2) (htarget : ¬ℓ ∣ (target.modulus : ℕ))
    (ψ : DirichletCharacter O (selmerHostModulus target e q d))
    (hψ : selmerHostFixingUnits target e q d ≤ ψ.toUnitHom.ker)
    (P : Ideal (𝓞 (CyclotomicField (selmerHostModulus target e q d) ℚ))) [P.IsPrime]
    [P.LiesOver (Ideal.span {(ℓ : ℤ)})]
    (σ : CyclotomicField (selmerHostModulus target e q d) ℚ ≃ₐ[ℚ]
      CyclotomicField (selmerHostModulus target e q d) ℚ)
    (hσ : σ ∈ P.inertia _) :
    (ψ.toUnitHom (selmerCyclotomicUnitsEquiv target e q d σ)) ^ 2 = 1 := by
  let N := selmerHostModulus target e q d
  let K := CyclotomicField N ℚ
  let : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let : NeZero (N : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  let : IsCyclotomicExtension {N} ℚ K := CyclotomicField.isCyclotomicExtension N ℚ
  apply selmerHostCharacter_sq_eq_one_of_ordCompl_units target e q d Fact.out hodd htarget ψ hψ
  change IsCyclotomicExtension.Rat.galEquivZMod N K σ ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N ℓ)).ker
  rw [← cyclotomic_inertia_map_eq_ordCompl_ker K P]
  exact Subgroup.mem_map_of_mem _ hσ

/-- At the nongeneric small primes the ambient cyclotomic inertia acts
trivially on host characters. -/
theorem selmerHostCharacter_eq_one_of_residuePrime_inertia
    {O : Type*} [CommRing O] (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hpair : SelmerEstimatePrimePair target q d) {ℓ t : ℕ}
    (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (htarget : ¬ℓ ∣ (target.modulus : ℕ))
    (hsmall : ℓ ≤ 2 * t) (hq : 2 * t < (q : ℕ)) (hd : 2 * t < (d : ℕ))
    (ψ : DirichletCharacter O (selmerHostModulus target e q d))
    (u : (ZMod (selmerHostModulus target e q d))ˣ)
    (hu : ZMod.unitsMap (Nat.ordCompl_dvd (selmerHostModulus target e q d) ℓ) u = 1) :
    ψ.toUnitHom u = 1 := by
  let N := selmerHostModulus target e q d
  have hcop := selmerHostModulus_coprime_residuePrime target e q d hpair hℓ hodd htarget hsmall hq hd
  have heq : ordCompl[ℓ] N = N :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd N hℓ).mpr
      (Or.inr (hℓ.coprime_iff_not_dvd.mp hcop))
  have h' (a : ℕ) (ha : a = N) (hdiv : a ∣ N) :
      ZMod.unitsMap hdiv u = 1 → u = 1 := by
    subst a
    rw [ZMod.unitsMap_self, MonoidHom.id_apply]
    exact id
  exact (h' _ heq _ hu) ▸ map_one _

end Riemann
