module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Utilities.DirichletCharacter
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Utilities.ExponentialGrowth
import Utilities.NumberFieldTorsion
import Utilities.QuadraticResidue
public import Utilities.ZModUnits

@[expose] public section

open Utilities
open scoped BigOperators IsMulCommutative

namespace Riemann

/-- The auxiliary prime pair at one base scale, Definition 17.9. -/
structure SelmerWindowPair (ε base : ℝ) (q d : ℕ+) : Prop where
  base_ge_two : 2 ≤ base
  q_prime : (q : ℕ).Prime
  d_prime : (d : ℕ).Prime
  q_residue : (q : ℕ) % 8 = 3
  d_residue : (d : ℕ) % 16 = 7
  q_lower : base ^ (ε / 5) / 2 < Real.log (q : ℕ)
  q_upper : Real.log (q : ℕ) ≤ base ^ (ε / 5)
  d_lower : base ^ (ε / 5) * Real.log base ^ (2 : ℕ) / 2 < Real.log (d : ℕ)
  d_upper : Real.log (d : ℕ) ≤ base ^ (ε / 5) * Real.log base ^ (2 : ℕ)
  q_dvd : (q : ℕ) ∣ (d : ℕ) + 1
  small_prime_dvd : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ base ^ (ε / 5) →
    p ∣ (d : ℕ) + 1

/-- Every excluded prime splits in the quadratic factor at `d` once the
small-prime range contains the target modulus. -/
theorem SelmerWindowPair.isSquare_excluded {ε base : ℝ} {q d : ℕ+}
    (h : SelmerWindowPair ε base q d) {N p : ℕ} (hN : 0 < N)
    (hsize : (N : ℝ) ≤ base ^ (ε / 5))
    (hp : p.Prime) (hex : p ∣ 2 * (q : ℕ) * N) : IsSquare (p : ZMod (d : ℕ)) := by
  let _ : Fact (d : ℕ).Prime := ⟨h.d_prime⟩
  have hdmod := h.d_residue
  have hd₂ : (d : ℕ) ≠ 2 := by omega
  by_cases hp₂ : p = 2
  · subst p
    simpa only [Nat.cast_ofNat] using
      (ZMod.exists_sq_eq_two_iff hd₂).mpr (Or.inr (by omega))
  · let _ : Fact p.Prime := ⟨hp⟩
    apply isSquare_zmod_of_dvd_add_one hp₂ (by omega)
    rcases hp.dvd_mul.mp hex with hleft | hright
    · rcases hp.dvd_mul.mp hleft with htwo | hq
      · exact (hp₂ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp htwo)).elim
      · have hqeq := (Nat.prime_dvd_prime_iff_eq hp h.q_prime).mp hq
        exact hqeq.symm ▸ h.q_dvd
    · have hpN : (p : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_dvd hN hright)
      exact h.small_prime_dvd p hp (hp.odd_of_ne_two hp₂) (hpN.trans hsize)

def selmerBaseModulus (target : BundledDirichletCharacter) (e : ℕ) : ℕ :=
  Nat.lcm (2 ^ (e + 2)) (target.modulus : ℕ)

theorem selmerBaseModulus_pos (target : BundledDirichletCharacter) (e : ℕ) :
    0 < selmerBaseModulus target e :=
  Nat.lcm_pos_iff.mpr ⟨by positivity, target.modulus.pos⟩

theorem selmerBaseModulus_coprime_of_prime (target : BundledDirichletCharacter) (e : ℕ)
    {p : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (hcop : p.Coprime target.modulus) :
    (selmerBaseModulus target e).Coprime p := by
  have htwo : ¬ p ∣ 2 ^ (e + 2) := fun h =>
    hp₂ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  exact (hp.coprime_iff_not_dvd.mpr
    (hp.not_dvd_lcm htwo (hp.coprime_iff_not_dvd.mp hcop))).symm

def selmerHostModulus (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+) : ℕ :=
  Nat.lcm (Nat.lcm (selmerBaseModulus target e) q) d

theorem selmerHostModulus_pos (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+) :
    0 < selmerHostModulus target e q d := by
  unfold selmerHostModulus
  exact Nat.lcm_pos_iff.mpr ⟨Nat.lcm_pos_iff.mpr
    ⟨selmerBaseModulus_pos target e, q.pos⟩, d.pos⟩

theorem selmerHostModulus_le_product (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) :
    selmerHostModulus target e q d ≤
      2 ^ (e + 2) * (target.modulus : ℕ) * (q : ℕ) * (d : ℕ) := by
  have hbase : selmerBaseModulus target e ≤ 2 ^ (e + 2) * (target.modulus : ℕ) :=
    Nat.le_of_dvd (mul_pos (by positivity) target.modulus.pos) (Nat.lcm_dvd_mul _ _)
  have hq : 0 < Nat.lcm (selmerBaseModulus target e) q :=
    Nat.lcm_pos_iff.mpr ⟨selmerBaseModulus_pos target e, q.pos⟩
  unfold selmerHostModulus
  exact (Nat.le_of_dvd (mul_pos hq d.pos) (Nat.lcm_dvd_mul _ _)).trans
    (Nat.mul_le_mul_right _ ((Nat.le_of_dvd (mul_pos (selmerBaseModulus_pos target e) q.pos)
      (Nat.lcm_dvd_mul _ _)).trans (Nat.mul_le_mul_right _ hbase)))

/-- The two conditions at the base modulus `N₁` of Proposition 5.14. -/
noncomputable def selmerBaseFixingUnits (target : BundledDirichletCharacter) (e : ℕ) :
    Subgroup (ZMod (selmerBaseModulus target e))ˣ := by
  let r : ℕ := 2 ^ (e + 2)
  let f : ℕ := target.modulus
  exact (Subgroup.zpowers (-1 : (ZMod r)ˣ)).comap (ZMod.unitsMap (Nat.dvd_lcm_left r f)) ⊓
    target.character.toUnitHom.ker.comap (ZMod.unitsMap (Nat.dvd_lcm_right r f))

def selmerSquareUnits (p : ℕ) : Subgroup (ZMod p)ˣ :=
  (⊤ : Subgroup (ZMod p)ˣ).map (powMonoidHom 2)

theorem selmerSquareClass_card {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    Nat.card ((ZMod p)ˣ ⧸ selmerSquareUnits p) = 2 := by
  change (selmerSquareUnits p).index = 2
  rw [selmerSquareUnits, ← MonoidHom.range_eq_map, IsCyclic.index_powMonoidHom_range,
    Nat.card_units, Nat.card_zmod, Nat.gcd_eq_right_iff_dvd]
  omega

/-- The quadratic sign in additive coordinates, with the square class at zero. -/
noncomputable def selmerSquareClassSign {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    ((ZMod p)ˣ ⧸ selmerSquareUnits p) ≃* Multiplicative (ZMod 2) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply mulEquivOfPrimeCardEq (selmerSquareClass_card hp)
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)

theorem selmerSquareClass_neg_one_ne_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    (QuotientGroup.mk (-1) : (ZMod p)ˣ ⧸ selmerSquareUnits p) ≠ 1 := by
  intro h
  have hmem := (QuotientGroup.eq_one_iff (-1 : (ZMod p)ˣ)).mp h
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp hmem
  have hsq : (u : ZMod p) ^ 2 = -1 := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) hu
  exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq) hp

theorem selmerSquareClassSign_neg_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    selmerSquareClassSign hp (QuotientGroup.mk (-1)) = Multiplicative.ofAdd 1 := by
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)
  obtain ⟨_, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : Multiplicative (ZMod 2))).mp hcard
  have hneg : selmerSquareClassSign hp (QuotientGroup.mk (-1)) ≠ 1 := by
    intro h
    exact selmerSquareClass_neg_one_ne_one hp ((selmerSquareClassSign hp).injective
      (h.trans (map_one _).symm))
  have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by
    intro h
    exact one_ne_zero (show (1 : ZMod 2) = 0 from h)
  exact (hunique _ hneg).trans (hunique _ hone).symm

/-- The subgroup of cyclotomic units that fixes the field in Definition 17.10. -/
noncomputable def selmerHostFixingUnits (target : BundledDirichletCharacter) (e : ℕ)
    (q d : ℕ+) : Subgroup (ZMod (selmerHostModulus target e q d))ˣ := by
  let N₁ := selmerBaseModulus target e
  let N := selmerHostModulus target e q d
  have hbase : N₁ ∣ N := dvd_trans (Nat.dvd_lcm_left N₁ q) (Nat.dvd_lcm_left _ d)
  have hq : (q : ℕ) ∣ N := dvd_trans (Nat.dvd_lcm_right N₁ q) (Nat.dvd_lcm_left _ d)
  have hd : (d : ℕ) ∣ N := Nat.dvd_lcm_right _ d
  exact (selmerBaseFixingUnits target e).comap (ZMod.unitsMap hbase) ⊓
    (selmerSquareUnits q).comap (ZMod.unitsMap hq) ⊓
    (selmerSquareUnits d).comap (ZMod.unitsMap hd)

noncomputable def selmerCyclotomicUnitsEquiv (target : BundledDirichletCharacter) (e : ℕ)
    (q d : ℕ+) :
    (CyclotomicField (selmerHostModulus target e q d) ℚ ≃ₐ[ℚ]
      CyclotomicField (selmerHostModulus target e q d) ℚ) ≃* (ZMod (selmerHostModulus target e q d))ˣ := by
  let N := selmerHostModulus target e q d
  letI : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  letI : NeZero (N : ℚ) := ⟨by exact_mod_cast (NeZero.ne N)⟩
  letI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  exact IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)

/-- The fixed field E of Definition 17.10, in Mathlib's cyclotomic field. -/
noncomputable def selmerHostField (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+) :
    IntermediateField ℚ (CyclotomicField (selmerHostModulus target e q d) ℚ) :=
  IntermediateField.fixedField ((selmerHostFixingUnits target e q d).comap
    (selmerCyclotomicUnitsEquiv target e q d).toMonoidHom)

theorem selmerCyclotomic_isAbelianGalois (target : BundledDirichletCharacter) (e : ℕ)
    (q d : ℕ+) : IsAbelianGalois ℚ (CyclotomicField (selmerHostModulus target e q d) ℚ) := by
  let N := selmerHostModulus target e q d
  let localNatNonzero : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let localNonzero : NeZero (N : ℚ) :=
    ⟨by exact_mod_cast (selmerHostModulus_pos target e q d).ne'⟩
  let localCyclotomic : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  exact IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)

theorem selmerHostField_isAbelianGalois (target : BundledDirichletCharacter) (e : ℕ)
    (q d : ℕ+) : IsAbelianGalois ℚ (selmerHostField target e q d) := by
  let localAbelian := selmerCyclotomic_isAbelianGalois target e q d
  infer_instance

/-- The quotient description of the Galois group of the host in §5.7. -/
noncomputable def selmerHostGalQuotient (target : BundledDirichletCharacter) (e : ℕ)
    (q d : ℕ+) :
    ((ZMod (selmerHostModulus target e q d))ˣ ⧸ selmerHostFixingUnits target e q d) ≃*
      (selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d) := by
  let γ := selmerCyclotomicUnitsEquiv target e q d
  let U := selmerHostFixingUnits target e q d
  let V := U.comap γ.toMonoidHom
  letI := selmerCyclotomic_isAbelianGalois target e q d
  have hmap : U.map γ.symm.toMonoidHom = V :=
    Subgroup.map_equiv_eq_comap_symm γ.symm U
  exact (QuotientGroup.congr U V γ.symm hmap).trans (IsGalois.normalAutEquivQuotient V)

theorem selmerHostGalQuotient_mk (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (u : (ZMod (selmerHostModulus target e q d))ˣ) :
    letI := selmerHostField_isAbelianGalois target e q d
    selmerHostGalQuotient target e q d (QuotientGroup.mk u) =
      ((selmerCyclotomicUnitsEquiv target e q d).symm u).restrictNormal
        (selmerHostField target e q d) := by
  rfl

/-- On a cyclotomic field, complex conjugation has exponent `-1`. -/
theorem cyclotomicGalEquivZMod_eq_neg_one_of_embedding_conj (n : ℕ) [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (ι : K →ₐ[ℚ] ℂ) (σ : K ≃ₐ[ℚ] K) (hσ : ∀ z, ι (σ z) = star (ι z)) :
    IsCyclotomicExtension.Rat.galEquivZMod n K σ = -1 := by
  let ζ := IsCyclotomicExtension.zeta n ℚ K
  have hζ : IsPrimitiveRoot ζ n := IsCyclotomicExtension.zeta_spec n ℚ K
  let u := IsCyclotomicExtension.Rat.galEquivZMod n K σ
  have hnorm : ‖ι ζ‖ = 1 := by
    apply IsOfFinOrder.norm_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, by
      rw [← map_pow, hζ.pow_eq_one, map_one]⟩
  have hinv : σ ζ = ζ⁻¹ := by
    apply ι.injective
    change ι (σ ζ) = ι (ζ⁻¹)
    rw [hσ, map_inv₀]
    exact (Complex.inv_eq_conj hnorm).symm
  have hp : σ ζ = ζ ^ (u : ZMod n).val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n K σ hζ.pow_eq_one
  have hpow : ζ ^ ((u : ZMod n).val + 1) = 1 := by
    rw [pow_succ, ← hp, hinv, inv_mul_cancel₀ (hζ.ne_zero (NeZero.ne n))]
  have hdvd := hζ.dvd_of_pow_eq_one _ hpow
  have hzero := (CharP.cast_eq_zero_iff (ZMod n) n _).mpr hdvd
  rw [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one] at hzero
  apply Units.ext
  change (u : ZMod n) = -1
  exact eq_neg_of_add_eq_zero_left hzero

/-- In the host quotient, conjugation is represented by `-1` for every embedding. -/
theorem selmerHostGalQuotient_neg_one_of_embedding_conj (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ι : selmerHostField target e q d →ₐ[ℚ] ℂ)
    (σ : selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d)
    (hσ : ∀ z, ι (σ z) = star (ι z)) :
    selmerHostGalQuotient target e q d (QuotientGroup.mk (-1)) = σ := by
  let N := selmerHostModulus target e q d
  let K := CyclotomicField N ℚ
  let E := selmerHostField target e q d
  let localNonzero : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let localRatNonzero : NeZero (N : ℚ) := ⟨by exact_mod_cast (NeZero.ne N)⟩
  let localCyclotomic : IsCyclotomicExtension {N} ℚ K := CyclotomicField.isCyclotomicExtension N ℚ
  let localAmbient : IsAbelianGalois ℚ K := selmerCyclotomic_isAbelianGalois target e q d
  let localHost : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
  obtain ⟨j, hj⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := ℚ) (L := E) (M := ℂ) (E := K) ι
  obtain ⟨τ, hτ, _⟩ := existsUnique_numberFieldConjugation K j
  have hneg : selmerCyclotomicUnitsEquiv target e q d τ = -1 :=
    cyclotomicGalEquivZMod_eq_neg_one_of_embedding_conj N K j τ hτ
  rw [selmerHostGalQuotient_mk, ← hneg, MulEquiv.symm_apply_apply]
  have hj' (z : E) : j (algebraMap E K z) = ι z := DFunLike.congr_fun hj z
  apply AlgEquiv.ext
  intro z
  apply ι.injective
  calc
    ι (τ.restrictNormal E z) = j (algebraMap E K (τ.restrictNormal E z)) := (hj' _).symm
    _ = j (τ (algebraMap E K z)) := congrArg j (τ.restrictNormal_commutes E z)
    _ = ι (σ z) := by rw [hτ, hj', hσ]

theorem selmerHostModulus_eq_mul (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d) :
    selmerHostModulus target e q d = selmerBaseModulus target e * (q : ℕ) * (d : ℕ) := by
  simp only [selmerHostModulus, hq.lcm_eq_mul, hd.lcm_eq_mul]

/-- The CRT splitting at the base modulus and the two auxiliary primes. -/
noncomputable def selmerHostUnitsCRT (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d) :
    (ZMod (selmerHostModulus target e q d))ˣ ≃*
      ((ZMod (selmerBaseModulus target e))ˣ × (ZMod (q : ℕ))ˣ) × (ZMod (d : ℕ))ˣ :=
  (Units.mapEquiv (ZMod.ringEquivCongr (selmerHostModulus_eq_mul target e q d hq hd)).toMulEquiv).trans
    ((zmodUnitsCRT hd).trans (MulEquiv.prodCongr (zmodUnitsCRT hq) (MulEquiv.refl _)))

theorem selmerHostUnitsCRT_apply (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
    (u : (ZMod (selmerHostModulus target e q d))ˣ) :
    selmerHostUnitsCRT target e q d hq hd u =
      ((ZMod.unitsMap (dvd_trans (Nat.dvd_lcm_left _ q) (Nat.dvd_lcm_left _ d)) u,
        ZMod.unitsMap (dvd_trans (Nat.dvd_lcm_right (selmerBaseModulus target e) _)
          (Nat.dvd_lcm_left _ d)) u), ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) := by
  have hdiv : selmerBaseModulus target e * (q : ℕ) * (d : ℕ) ∣
      selmerHostModulus target e q d := by rw [selmerHostModulus_eq_mul target e q d hq hd]
  let v := Units.mapEquiv (ZMod.ringEquivCongr (selmerHostModulus_eq_mul target e q d hq hd)).toMulEquiv u
  change (zmodUnitsCRT hq (zmodUnitsCRT hd v).1, (zmodUnitsCRT hd v).2) = _
  dsimp only [v]
  simp only [zmodUnitsCongr_apply _ hdiv, zmodUnitsCRT_apply, zmodUnitsMap_comp_apply]
  rfl

/-- The first two CRT components vanish together precisely when reduction
modulo `N₁ q` is trivial. -/
theorem selmerHostUnitsCRT_fst_eq_one (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
    (hm : selmerBaseModulus target e * (q : ℕ) ∣ selmerHostModulus target e q d)
    (u : (ZMod (selmerHostModulus target e q d))ˣ) :
    (selmerHostUnitsCRT target e q d hq hd u).1 = 1 ↔ ZMod.unitsMap hm u = 1 := by
  have heq := selmerHostModulus_eq_mul target e q d hq hd
  have hdiv : selmerBaseModulus target e * (q : ℕ) * (d : ℕ) ∣
      selmerHostModulus target e q d := by rw [heq]
  let v := Units.mapEquiv (ZMod.ringEquivCongr heq).toMulEquiv u
  change zmodUnitsCRT hq (zmodUnitsCRT hd v).1 = 1 ↔ _
  rw [(zmodUnitsCRT hq).map_eq_one_iff, zmodUnitsCRT_apply]
  dsimp only [v, Prod.fst]
  rw [zmodUnitsCongr_apply _ hdiv]
  rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]

/-- Proposition 5.14(i), with each of the quadratic factors expressed as a square-class quotient. -/
noncomputable def selmerHostGalCRT (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d) :
    (selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d) ≃*
      (((ZMod (selmerBaseModulus target e))ˣ ⧸ selmerBaseFixingUnits target e) ×
        ((ZMod (q : ℕ))ˣ ⧸ selmerSquareUnits q)) × ((ZMod (d : ℕ))ˣ ⧸ selmerSquareUnits d) := by
  let crt := selmerHostUnitsCRT target e q d hq hd
  let U := selmerHostFixingUnits target e q d
  let B := selmerBaseFixingUnits target e
  let Q := selmerSquareUnits q
  let D := selmerSquareUnits d
  have hmem (u : (ZMod (selmerHostModulus target e q d))ˣ) :
      u ∈ U ↔ crt u ∈ (B.prod Q).prod D := by
    dsimp only [crt, U]
    rw [selmerHostUnitsCRT_apply]
    rfl
  have hmap : U.map crt.toMonoidHom = (B.prod Q).prod D := by
    rw [Subgroup.map_equiv_eq_comap_symm' crt U]
    ext v
    change crt.symm v ∈ U ↔ v ∈ (B.prod Q).prod D
    simpa only [MulEquiv.apply_symm_apply] using hmem (crt.symm v)
  let splitBase := MulEquiv.prodCongr
    (M := ((ZMod (selmerBaseModulus target e))ˣ × (ZMod (q : ℕ))ˣ) ⧸ B.prod Q)
    (M' := ((ZMod (selmerBaseModulus target e))ˣ ⧸ B) × ((ZMod (q : ℕ))ˣ ⧸ Q))
    (QuotientGroup.prodMulEquiv B Q)
    (MulEquiv.refl ((ZMod (d : ℕ))ˣ ⧸ D))
  exact (selmerHostGalQuotient target e q d).symm.trans <|
    (QuotientGroup.congr U _ crt hmap).trans ((QuotientGroup.prodMulEquiv (B.prod Q) D).trans splitBase)

theorem selmerHostGalCRT_mk (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
    (u : (ZMod (selmerHostModulus target e q d))ˣ) :
    let v := selmerHostUnitsCRT target e q d hq hd u
    selmerHostGalCRT target e q d hq hd (selmerHostGalQuotient target e q d (QuotientGroup.mk u)) =
      ((QuotientGroup.mk v.1.1, QuotientGroup.mk v.1.2), QuotientGroup.mk v.2) := by
  unfold selmerHostGalCRT
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

/-- Restriction to the host takes each cyclotomic CRT coordinate to its quotient. -/
theorem selmerHostGalCRT_restrictNormal (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
    (τ : CyclotomicField (selmerHostModulus target e q d) ℚ ≃ₐ[ℚ]
      CyclotomicField (selmerHostModulus target e q d) ℚ) :
    letI := selmerHostField_isAbelianGalois target e q d
    let v := selmerHostUnitsCRT target e q d hq hd (selmerCyclotomicUnitsEquiv target e q d τ)
    selmerHostGalCRT target e q d hq hd (τ.restrictNormal (selmerHostField target e q d)) =
      ((QuotientGroup.mk v.1.1, QuotientGroup.mk v.1.2), QuotientGroup.mk v.2) := by
  let _ := selmerHostField_isAbelianGalois target e q d
  dsimp only
  simpa only [selmerHostGalQuotient_mk, MulEquiv.symm_apply_apply] using
    selmerHostGalCRT_mk target e q d hq hd (selmerCyclotomicUnitsEquiv target e q d τ)

theorem selmerHostGalCRT_conjugation (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
    (ι : selmerHostField target e q d →ₐ[ℚ] ℂ)
    (σ : selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d)
    (hσ : ∀ z, ι (σ z) = star (ι z)) :
    selmerHostGalCRT target e q d hq hd σ =
      ((QuotientGroup.mk (-1), QuotientGroup.mk (-1)), QuotientGroup.mk (-1)) := by
  rw [← selmerHostGalQuotient_neg_one_of_embedding_conj target e q d ι σ hσ, selmerHostGalCRT_mk]
  have hneg : selmerHostUnitsCRT target e q d hq hd (-1) = ((-1, -1), -1) := by
    rw [selmerHostUnitsCRT_apply]
    exact Prod.ext (Prod.ext (zmodUnitsMap_neg_one _) (zmodUnitsMap_neg_one _)) (zmodUnitsMap_neg_one _)
  rw [hneg]

noncomputable def selmerTwistLength (lengths : ℕ → ℕ → WithTop ℕ) (cutoff ℓ : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 cutoff, (((lengths ℓ i).untopD 0 : ℕ) : ℝ)

noncomputable def selmerWeightedLength (lengths : ℕ → ℕ → WithTop ℕ) (cutoff ℓ : ℕ) : ℝ :=
  Real.log (ℓ : ℝ) * selmerTwistLength lengths cutoff ℓ

/-- The finite-length conditions and weighted sum in (D6). The sum is expressed
by upper bounds on all finite partial sums of its nonnegative terms. -/
def SelmerLengthBound (lengths : ℕ → ℕ → WithTop ℕ) (cutoff : ℕ) (B : ℝ) : Prop :=
  (∀ ℓ : ℕ, ℓ.Prime → ∀ i ∈ Finset.Ico 1 cutoff, lengths ℓ i ≠ ⊤) ∧
  ∀ primes : Finset ℕ, (∀ ℓ ∈ primes, ℓ.Prime) →
    (∑ ℓ ∈ primes, selmerWeightedLength lengths cutoff ℓ) ≤ B

theorem SelmerLengthBound.mono {lengths : ℕ → ℕ → WithTop ℕ}
    {small large : ℕ} {B B' : ℝ} (h : SelmerLengthBound lengths large B)
    (hcutoff : small ≤ large) (hB : B ≤ B') : SelmerLengthBound lengths small B' := by
  have hsubset : Finset.Ico 1 small ⊆ Finset.Ico 1 large := by
    intro i hi
    obtain ⟨hi₁, hi₂⟩ := Finset.mem_Ico.mp hi
    exact Finset.mem_Ico.mpr ⟨hi₁, hi₂.trans_le hcutoff⟩
  refine ⟨fun ℓ hℓ i hi => h.1 ℓ hℓ i (hsubset hi), fun primes hprimes => ?_⟩
  have hsum : (∑ ℓ ∈ primes, selmerWeightedLength lengths small ℓ) ≤
      ∑ ℓ ∈ primes, selmerWeightedLength lengths large ℓ := by
    apply Finset.sum_le_sum
    intro ℓ hℓ
    have hlog : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg (by exact_mod_cast (hprimes ℓ hℓ).one_lt.le)
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => Nat.cast_nonneg _) hlog
  exact hsum.trans ((h.2 primes hprimes).trans hB)

/-- The weighted Selmer estimate survives the cutoff change in Proposition 18.3. -/
theorem selmerLengthBound_rescale {lengths : ℕ → ℕ → WithTop ℕ} {θ y ε : ℝ}
    (hθ : 1 ≤ θ) (hy : 0 < y) (hscale : θ ^ (400 : ℕ) ≤ y) (hε : 0 ≤ ε)
    (h : SelmerLengthBound lengths (Nat.floor (y ^ (401 : ℕ))) (Real.exp (y ^ ε / 2))) :
    SelmerLengthBound lengths (Nat.floor ((θ * y) ^ (400 : ℕ)))
      (Real.exp ((θ * y) ^ ε / 2)) := by
  have hp : (θ * y) ^ (400 : ℕ) ≤ y ^ (401 : ℕ) := by
    calc
      _ = θ ^ (400 : ℕ) * y ^ (400 : ℕ) := mul_pow _ _ _
      _ ≤ y * y ^ (400 : ℕ) := mul_le_mul_of_nonneg_right hscale (pow_nonneg hy.le _)
      _ = _ := by rw [mul_comm, ← pow_succ]
  have hxy : y ≤ θ * y := le_mul_of_one_le_left hy.le hθ
  have hxp := Real.rpow_le_rpow hy.le hxy hε
  exact h.mono (Nat.floor_mono hp)
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hxp (by norm_num)))

/-- Scaling a quadratic window by θ leaves a (3/2)-window after reducing the width. -/
theorem mem_quadratic_window_of_rescale {θ W x : ℝ} (hθ : 0 < θ) (hW : θ ≤ W)
    (hx : x ∈ Set.Icc (θ * W) ((θ * W) ^ (3 / 2 : ℝ))) :
    x / θ ∈ Set.Icc W (W ^ (2 : ℕ)) := by
  have hW₀ := hθ.trans_le hW
  have hθpow : θ ^ (3 / 2 : ℝ) = θ * θ ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hθ, Real.rpow_one]
  have hWpow : W ^ (1 / 2 : ℝ) * W ^ (3 / 2 : ℝ) = W ^ (2 : ℕ) := by
    rw [← Real.rpow_add hW₀, show (1 / 2 + 3 / 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  refine ⟨(le_div_iff₀ hθ).mpr (by simpa only [mul_comm W θ] using hx.1), ?_⟩
  apply (div_le_iff₀ hθ).mpr
  calc
    x ≤ (θ * W) ^ (3 / 2 : ℝ) := hx.2
    _ = θ ^ (3 / 2 : ℝ) * W ^ (3 / 2 : ℝ) := Real.mul_rpow hθ.le hW₀.le
    _ ≤ (θ * W ^ (1 / 2 : ℝ)) * W ^ (3 / 2 : ℝ) := by
      rw [hθpow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hθ.le hW (by norm_num)) hθ.le) (Real.rpow_nonneg hW₀.le _)
    _ = W ^ (2 : ℕ) * θ := by rw [mul_assoc, hWpow, mul_comm]

/-- The local length data needed by §18, for each host field and twist. -/
abbrev NumberFieldSelmerLengths :=
  (F : Type) → [Field F] → [NumberField F] → ℕ → ℕ → WithTop ℕ

/-- Rescale the window and lower the twist cutoff, preserving the actual host
when the chosen 2-power exponents agree under the rescaling. -/
theorem selmerHostBounds_on_rescaled_window (lengths : NumberFieldSelmerLengths)
    (target : BundledDirichletCharacter) (q d : ℕ+) (e e' : ℝ → ℕ) {θ W ε : ℝ}
    (hθ : 1 ≤ θ) (hW : θ ≤ W) (hlarge : θ ^ (400 : ℕ) ≤ W) (hε : 0 ≤ ε)
    (hexponent : ∀ y ∈ Set.Icc W (W ^ (2 : ℕ)), e' y = e (θ * y))
    (hwindow : ∀ y ∈ Set.Icc W (W ^ (2 : ℕ)),
      SelmerLengthBound (lengths (selmerHostField target (e' y) q d))
        (Nat.floor (y ^ (401 : ℕ))) (Real.exp (y ^ ε / 2))) :
    ∀ x ∈ Set.Icc (θ * W) ((θ * W) ^ (3 / 2 : ℝ)),
      SelmerLengthBound (lengths (selmerHostField target (e x) q d))
        (Nat.floor (x ^ (400 : ℕ))) (Real.exp (x ^ ε / 2)) := by
  intro x hx
  have hθ₀ : 0 < θ := zero_lt_one.trans_le hθ
  let y := x / θ
  have hy : y ∈ Set.Icc W (W ^ (2 : ℕ)) := mem_quadratic_window_of_rescale hθ₀ hW hx
  have hy₀ : 0 < y := (hθ₀.trans_le hW).trans_le hy.1
  have hmul : θ * y = x := by
    dsimp [y]
    rw [mul_comm, div_mul_cancel₀ _ hθ₀.ne']
  have hlength := selmerLengthBound_rescale hθ hy₀ (hlarge.trans hy.1) hε (hwindow y hy)
  rw [hexponent y hy, hmul] at hlength
  exact hlength

/-- Hypothesis 17.11 for the local lengths of the specified number fields.
This is a predicate on a realization of the Selmer kernels. -/
def HasSelmerWindowBound (lengths : NumberFieldSelmerLengths) : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∀ e : ℝ → ℕ,
      (∀ x ≥ 1, x ^ (2 + 8 * ε) ≤ (2 : ℝ) ^ e x ∧
        (2 : ℝ) ^ e x ≤ 2 * x ^ (2 + 8 * ε)) →
      ∃ J X₀ : ℝ, 1 ≤ J ∧ 1 ≤ X₀ ∧ ∀ X ≥ X₀,
        let base := X ^ (1 / J)
        ∀ q d : ℕ+, SelmerWindowPair ε base q d →
          ∃ Y : ℝ, base ≤ Y ∧ Y ≤ X ^ (1 / 2 : ℝ) ∧
            ∀ x ∈ Set.Icc Y (Y ^ (2 : ℕ)),
              SelmerLengthBound (lengths (selmerHostField target (e x) q d))
                (Nat.floor (x ^ (401 : ℕ))) (Real.exp (x ^ ε / 2))

/-- The rescaled window conclusion of Proposition 18.3, with the original
2-power indices and the D6 cutoff. -/
def HasRescaledSelmerWindowBound (lengths : NumberFieldSelmerLengths) : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∀ xe c₀ : ℝ, 1 ≤ xe → 1 ≤ c₀ →
      ∀ e : ℝ → ℕ,
        (∀ x ≥ xe, x ^ (2 + 8 * ε) ≤ c₀ * (2 : ℝ) ^ e x ∧
          c₀ * (2 : ℝ) ^ e x ≤ 2 * x ^ (2 + 8 * ε)) →
        ∃ J X₀ : ℝ, 1 ≤ J ∧ xe ^ J ≤ X₀ ∧ ∀ X ≥ X₀,
          let base := X ^ (1 / J)
          ∀ q d : ℕ+, SelmerWindowPair ε base q d →
            ∃ Y : ℝ, base ≤ Y ∧ Y ^ (2 : ℕ) ≤ base ^ (J + 1) ∧
              ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)),
                SelmerLengthBound (lengths (selmerHostField target (e x) q d))
                  (Nat.floor (x ^ (400 : ℕ))) (Real.exp (x ^ ε / 2))

theorem HasSelmerWindowBound.to_rescaled {lengths : NumberFieldSelmerLengths}
    (h : HasSelmerWindowBound lengths) : HasRescaledSelmerWindowBound lengths := by
  classical
  intro target hprimitive ε hε hε₀ xe c₀ hxe hc₀ e he
  let α : ℝ := 2 + 8 * ε
  let θ := c₀ ^ (1 / α)
  have hα : 0 < α := by dsimp [α]; positivity
  have hcpos : 0 < c₀ := zero_lt_one.trans_le hc₀
  have hθ : 1 ≤ θ := Real.one_le_rpow hc₀ (by positivity)
  have hθpos := zero_lt_one.trans_le hθ
  have hθα : θ ^ α = c₀ := by
    dsimp [θ]
    rw [one_div, Real.rpow_inv_rpow hcpos.le hα.ne']
  have hdyadic (y : ℝ) :
      ∃ n : ℕ, 1 ≤ y → y ^ α ≤ (2 : ℝ) ^ n ∧ (2 : ℝ) ^ n ≤ 2 * y ^ α := by
    by_cases hy : 1 ≤ y
    · obtain ⟨n, hn⟩ := exists_dyadic_cover (Real.one_le_rpow hy hα.le)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun hy' => (hy hy').elim⟩
  let e' (y : ℝ) := if xe ≤ θ * y then e (θ * y) else Classical.choose (hdyadic y)
  have he' : ∀ y ≥ 1, y ^ α ≤ (2 : ℝ) ^ e' y ∧ (2 : ℝ) ^ e' y ≤ 2 * y ^ α := by
    intro y hy
    by_cases hyx : xe ≤ θ * y
    · obtain ⟨hlo, hhi⟩ := he (θ * y) hyx
      have hscaled : (θ * y) ^ α = c₀ * y ^ α := by
        rw [Real.mul_rpow hθpos.le (zero_le_one.trans hy), hθα]
      change (θ * y) ^ α ≤ c₀ * (2 : ℝ) ^ e (θ * y) at hlo
      change c₀ * (2 : ℝ) ^ e (θ * y) ≤ 2 * (θ * y) ^ α at hhi
      rw [hscaled] at hlo hhi
      simp only [e', ite_eq_left hyx]
      exact ⟨le_of_mul_le_mul_left hlo hcpos, le_of_mul_le_mul_left (by linarith) hcpos⟩
    · simpa only [e', ite_eq_right hyx] using Classical.choose_spec (hdyadic y) hy
  obtain ⟨J, X₁, hJ, hX₁, hwindows⟩ := h target hprimitive ε hε hε₀ e' he'
  let T : ℝ := max 2 (max xe (θ ^ (400 : ℕ)))
  let X₀ : ℝ := max X₁ (T ^ J)
  have hT : 0 ≤ T := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)
  have hxeT : xe ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hθT : θ ^ (400 : ℕ) ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hJpos := zero_lt_one.trans_le hJ
  refine ⟨J, X₀, hJ, (Real.rpow_le_rpow (zero_le_one.trans hxe) hxeT hJpos.le).trans
    (le_max_right _ _), fun X hX => ?_⟩
  intro base q d hpair
  have hX₁X : X₁ ≤ X := (le_max_left _ _).trans hX
  have hXpos := zero_lt_one.trans_le (hX₁.trans hX₁X)
  have hbaseT : T ≤ base := by
    have hTpow : T ^ J ≤ X := (le_max_right _ _).trans hX
    have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hT J) hTpow
      (one_div_nonneg.mpr hJpos.le)
    rw [one_div, Real.rpow_rpow_inv hT hJpos.ne'] at hmono
    simpa only [base, one_div] using hmono
  have hbasepos : 0 < base := Real.rpow_pos_of_pos hXpos _
  have hbaseX : base ^ J = X := by
    dsimp [base]
    rw [one_div, Real.rpow_inv_rpow hXpos.le hJpos.ne']
  obtain ⟨W, hWbase, hWX, hwindow⟩ := hwindows X hX₁X q d hpair
  have hWpos := hbasepos.trans_le hWbase
  have hlarge : θ ^ (400 : ℕ) ≤ W := hθT.trans (hbaseT.trans hWbase)
  have hθW : θ ≤ W := (le_self_pow₀ hθ (by decide : (400 : ℕ) ≠ 0)).trans hlarge
  have hθ2 : θ ^ (2 : ℕ) ≤ base :=
    (pow_right_mono₀ hθ (by decide : (2 : ℕ) ≤ 400)).trans (hθT.trans hbaseT)
  have hW2 : W ^ (2 : ℕ) ≤ X := by
    calc
      _ ≤ (X ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := pow_le_pow_left₀ hWpos.le hWX _
      _ = _ := by
        simpa only [one_div, Nat.cast_ofNat] using
          Real.rpow_inv_natCast_pow hXpos.le (by decide : (2 : ℕ) ≠ 0)
  refine ⟨θ * W, hWbase.trans (le_mul_of_one_le_left hWpos.le hθ), ?_, ?_⟩
  · calc
      (θ * W) ^ (2 : ℕ) = θ ^ (2 : ℕ) * W ^ (2 : ℕ) := mul_pow _ _ _
      _ ≤ base * X := mul_le_mul hθ2 hW2 (sq_nonneg W) hbasepos.le
      _ = base ^ (J + 1) := by rw [Real.rpow_add hbasepos, Real.rpow_one, hbaseX, mul_comm]
  · apply selmerHostBounds_on_rescaled_window lengths target q d e e' hθ hθW hlarge hε.le
      _ hwindow
    intro y hy
    have hypos := hWpos.trans_le hy.1
    have hyx := (hxeT.trans (hbaseT.trans hWbase)).trans
      (hy.1.trans (le_mul_of_one_le_left hypos.le hθ))
    simp only [e', ite_eq_left hyx]

end Riemann
