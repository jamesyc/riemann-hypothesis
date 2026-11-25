module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

@[expose] public section

open scoped NumberField IntermediateField

namespace Utilities

variable (E : Type) [Field E] [NumberField E]

noncomputable def numberFieldUnitsAut (σ : E ≃ₐ[ℚ] E) : MulAut (𝓞 E)ˣ :=
  Units.mapEquiv (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv).toMulEquiv

omit [NumberField E] in
theorem map_numberFieldTorsion (f : (𝓞 E)ˣ →* (𝓞 E)ˣ) {z : (𝓞 E)ˣ}
    (hz : z ∈ NumberField.Units.torsion E) :
    f z ∈ NumberField.Units.torsion E := by
  change f z ∈ CommGroup.torsion (𝓞 E)ˣ
  change z ∈ CommGroup.torsion (𝓞 E)ˣ at hz
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hz ⊢
  obtain ⟨n, hn, heq⟩ := hz
  exact ⟨n, hn, by rw [← map_pow, heq, map_one]⟩

noncomputable def numberFieldTorsionAut (σ : E ≃ₐ[ℚ] E) :
    MulAut (NumberField.Units.torsion E) where
  toFun z := ⟨numberFieldUnitsAut E σ z,
    map_numberFieldTorsion E (numberFieldUnitsAut E σ).toMonoidHom z.prop⟩
  invFun z := ⟨(numberFieldUnitsAut E σ).symm z,
    map_numberFieldTorsion E (numberFieldUnitsAut E σ).symm.toMonoidHom z.prop⟩
  left_inv z := Subtype.ext ((numberFieldUnitsAut E σ).symm_apply_apply z)
  right_inv z := Subtype.ext ((numberFieldUnitsAut E σ).apply_symm_apply z)
  map_mul' z w := Subtype.ext ((numberFieldUnitsAut E σ).map_mul z w)

private theorem numberFieldTorsionAut_apply_coe (σ : E ≃ₐ[ℚ] E)
    (z : NumberField.Units.torsion E) :
    (((numberFieldTorsionAut E σ z).val : 𝓞 E) : E) = σ (((z.val : 𝓞 E) : E)) := by
  rfl

/-- The Galois action on the finite cyclic group of roots of unity. -/
noncomputable def numberFieldTorsionAction : (E ≃ₐ[ℚ] E) →* MulAut (NumberField.Units.torsion E) where
  toFun := numberFieldTorsionAut E
  map_one' := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    apply Units.ext
    apply NumberField.RingOfIntegers.coe_injective
    change (((numberFieldTorsionAut E 1 z).val : 𝓞 E) : E) = ((z.val : 𝓞 E) : E)
    simp only [numberFieldTorsionAut_apply_coe, AlgEquiv.one_apply]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    apply Units.ext
    apply NumberField.RingOfIntegers.coe_injective
    change (((numberFieldTorsionAut E (σ * τ) z).val : 𝓞 E) : E) =
      (((numberFieldTorsionAut E σ (numberFieldTorsionAut E τ z)).val : 𝓞 E) : E)
    simp only [numberFieldTorsionAut_apply_coe, AlgEquiv.mul_apply]

/-- The action in coordinates on the cyclic roots-of-unity group. -/
noncomputable def numberFieldTorsionCharacter :
    (E ≃ₐ[ℚ] E) →* (ZMod (NumberField.Units.torsionOrder E))ˣ :=
  (IsCyclic.mulAutMulEquiv (NumberField.Units.torsion E)).toMonoidHom.comp
    (numberFieldTorsionAction E)

/-- Inversion on a cyclic group is multiplication by minus one in its
cyclic coordinates. -/
theorem cyclicAutMulEquiv_eq_neg_one_of_inv {G : Type*} [Group G] [hG : IsCyclic G]
    (σ : MulAut G) (hσ : ∀ z, σ z = z⁻¹) :
    IsCyclic.mulAutMulEquiv G σ = -1 := by
  let coordinate := zmodCyclicMulEquiv hG
  apply Units.ext
  change (coordinate.symm (σ (coordinate
    (Multiplicative.ofAdd (1 : ZMod (Nat.card G)))))).toAdd = (-1 : ZMod (Nat.card G))
  rw [hσ, map_inv, coordinate.symm_apply_apply]
  rfl

theorem numberFieldTorsionCharacter_eq_neg_one_of_inv (σ : E ≃ₐ[ℚ] E)
    (hσ : ∀ z, numberFieldTorsionAut E σ z = z⁻¹) :
    numberFieldTorsionCharacter E σ = -1 :=
  cyclicAutMulEquiv_eq_neg_one_of_inv (numberFieldTorsionAut E σ) hσ

/-- Inertia fixes torsion when its reduction in the residue field is injective. -/
theorem numberFieldTorsionAut_eq_self_of_mem_inertia {P : Ideal (𝓞 E)}
    {σ : E ≃ₐ[ℚ] E} (hσ : σ ∈ P.inertia (E ≃ₐ[ℚ] E))
    (hproper : P.absNorm ≠ 1) (hcoprime : P.absNorm.Coprime (NumberField.Units.torsionOrder E))
    (z : NumberField.Units.torsion E) : numberFieldTorsionAut E σ z = z := by
  apply Ideal.torsionMapQuot_injective hproper hcoprime
  apply Units.ext
  change Ideal.Quotient.mk P ((numberFieldTorsionAut E σ z).val : 𝓞 E) =
    Ideal.Quotient.mk P (z.val : 𝓞 E)
  have hact : ((numberFieldTorsionAut E σ z).val : 𝓞 E) = σ • (z.val : 𝓞 E) := by
    apply NumberField.RingOfIntegers.coe_injective
    exact numberFieldTorsionAut_apply_coe E σ z
  rw [hact, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (Ideal.mem_inertia.mp hσ) (z.val : 𝓞 E)

/-- An automorphism that induces complex conjugation under an embedding
inverts the roots of unity. -/
theorem numberFieldTorsionAut_eq_inv_of_embedding_conj (ι : E →ₐ[ℚ] ℂ)
    (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x : E, ι (σ x) = star (ι x))
    (z : NumberField.Units.torsion E) : numberFieldTorsionAut E σ z = z⁻¹ := by
  let φ : (𝓞 E)ˣ →* ℂˣ :=
    Units.map (ι.toRingHom.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hfinite : IsOfFinOrder (z.val : (𝓞 E)ˣ) := (CommGroup.mem_torsion _).mp z.prop
  have hnorm : ‖(φ z.val : ℂ)‖ = 1 :=
    (((Units.coeHom ℂ).comp φ).isOfFinOrder hfinite).norm_eq_one
  apply Subtype.ext
  apply Units.ext
  apply NumberField.RingOfIntegers.coe_injective
  apply ι.injective
  change ι (((numberFieldTorsionAut E σ z).val : 𝓞 E) : E) = (φ (z.val⁻¹) : ℂ)
  rw [numberFieldTorsionAut_apply_coe, hσ, map_inv]
  change star (φ z.val : ℂ) = ((φ z.val)⁻¹ : ℂˣ)
  simpa using (Complex.inv_eq_conj hnorm).symm

/-- Complex conjugation transported to a normal extension of `ℚ` by an embedding. -/
noncomputable def algEquiv_complexConjugation (K : Type*) [Field K] [Algebra ℚ K]
    [Normal ℚ K] (ι : K →ₐ[ℚ] ℂ) : K ≃ₐ[ℚ] K :=
  let _localAlgebra : Algebra K ℂ := ι.toRingHom.toAlgebra
  let _localTower : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  (Complex.conjAe.restrictScalars ℚ).restrictNormal K

theorem algEquiv_complexConjugation_apply (K : Type*) [Field K] [Algebra ℚ K]
    [Normal ℚ K] (ι : K →ₐ[ℚ] ℂ) (x : K) :
    ι (algEquiv_complexConjugation K ι x) = star (ι x) := by
  let _localAlgebra : Algebra K ℂ := ι.toRingHom.toAlgebra
  let _localTower : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  exact (Complex.conjAe.restrictScalars ℚ).restrictNormal_commutes K x

theorem algEquiv_complexConjugation_involutive (K : Type*) [Field K] [Algebra ℚ K]
    [Normal ℚ K] (ι : K →ₐ[ℚ] ℂ) :
    Function.Involutive (algEquiv_complexConjugation K ι) := by
  intro x
  apply ι.injective
  change ι (algEquiv_complexConjugation K ι (algEquiv_complexConjugation K ι x)) = ι x
  rw [algEquiv_complexConjugation_apply, algEquiv_complexConjugation_apply, star_star]

/-- Normality realizes complex conjugation as a unique automorphism
under any chosen complex embedding. -/
theorem existsUnique_numberFieldConjugation [Normal ℚ E] (ι : E →ₐ[ℚ] ℂ) :
    ∃! σ : E ≃ₐ[ℚ] E, ∀ x : E, ι (σ x) = star (ι x) := by
  refine ⟨algEquiv_complexConjugation E ι, algEquiv_complexConjugation_apply E ι, fun σ hσ => ?_⟩
  apply AlgEquiv.ext
  intro x
  exact ι.injective ((hσ x).trans (algEquiv_complexConjugation_apply E ι x).symm)

theorem exists_primitiveRoot_torsionOrder :
    ∃ ζ : E, IsPrimitiveRoot ζ (NumberField.Units.torsionOrder E) := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (NumberField.Units.torsion E))
  have horder : orderOf (g.val : (𝓞 E)ˣ) = NumberField.Units.torsionOrder E :=
    (Subgroup.orderOf_coe g).trans (orderOf_eq_card_of_zpowers_eq_top hg)
  have hζ : IsPrimitiveRoot (g.val : E) (NumberField.Units.torsionOrder E) := by
    rw [← horder]
    exact IsPrimitiveRoot.coe_coe_iff.mpr (IsPrimitiveRoot.orderOf g.val)
  exact ⟨_, hζ⟩

private theorem le_parity_mul_totient_sq (n : ℕ) :
    n ≤ (if Even n then 2 else 1) * n.totient ^ 2 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p k hp =>
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.totient_prime_pow_succ hp, mul_pow, pow_succ' p k]
      have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
      have hpk₂ : p ^ k ≤ (p ^ k) ^ 2 := by nlinarith
      rcases eq_or_ne p 2 with rfl | hp₂
      · have hEven : Even (2 * 2 ^ k) := even_two.mul_right _
        simp [hEven]
        omega
      · have hGe : 3 ≤ p := by have := hp.two_le; omega
        have hle : p ≤ (p - 1) ^ 2 := by
          have hpred : p - 1 + 1 = p := by omega
          nlinarith
        exact (Nat.mul_le_mul hle hpk₂).trans (by
          rw [mul_comm ((p - 1) ^ 2)]
          exact Nat.le_mul_of_pos_left _ (by split <;> decide))
  | coprime a b ha hb hab hia hib =>
    rw [Nat.totient_mul hab, mul_pow]
    refine (Nat.mul_le_mul hia hib).trans ?_
    by_cases hea : Even a <;> by_cases heb : Even b
    · exact (Nat.Prime.not_dvd_one Nat.prime_two
        (hab.gcd_eq_one ▸ Nat.dvd_gcd hea.two_dvd heb.two_dvd)).elim
    · simp [hea, heb, hea.mul_right b, mul_assoc]
    · simp [hea, heb, heb.mul_left a, mul_left_comm]
    · simp only [hea, heb, ite_false, one_mul]
      split <;> omega

/-- The roots of unity in a number field have order at most twice the square of its degree. -/
theorem torsionOrder_le_two_mul_finrank_sq :
    NumberField.Units.torsionOrder E ≤ 2 * Module.finrank ℚ E ^ 2 := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_torsionOrder E
  let F := ℚ⟮ζ⟯
  let : IsCyclotomicExtension {NumberField.Units.torsionOrder E} ℚ F :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hdeg := IsCyclotomicExtension.Rat.finrank (NumberField.Units.torsionOrder E) F
  have htot : (NumberField.Units.torsionOrder E).totient ≤ Module.finrank ℚ E :=
    hdeg ▸ Submodule.finrank_le F.toSubmodule
  exact (le_parity_mul_totient_sq _).trans (by split <;> gcongr; omega)

/-- A prime dividing the torsion order forces the ramification of the
corresponding prime cyclotomic subfield. -/
theorem prime_sub_one_le_ramificationIdx_of_dvd_torsionOrder (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hdiv : p ∣ NumberField.Units.torsionOrder E) :
    p - 1 ≤ P.ramificationIdx ℤ := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_torsionOrder E
  obtain ⟨n, hn⟩ := hdiv
  have hprimitive : IsPrimitiveRoot (ζ ^ n) p :=
    IsPrimitiveRoot.pow (NumberField.Units.torsionOrder_pos E) hζ (by rw [hn, mul_comm])
  let F := ℚ⟮ζ ^ n⟯
  let localCyclotomic : IsCyclotomicExtension {p} ℚ F :=
    hprimitive.intermediateField_adjoin_isCyclotomicExtension ℚ
  let Q := P.under (𝓞 F)
  let localPrimeQ : Q.IsPrime := (inferInstance : P.IsPrime).comap (algebraMap (𝓞 F) (𝓞 E))
  let localLiesOverQ : P.LiesOver Q := Ideal.over_under (A := 𝓞 F) P
  let localLiesOverBase : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    change Ideal.span {(p : ℤ)} = (P.under (𝓞 F)).under ℤ
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over
  rw [← IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p F Q]
  exact Ideal.ramificationIdx_below_le Q P

/-- The ramification index of an integral prime in a Galois number field is
the order of its inertia subgroup. -/
theorem numberField_ramificationIdx_eq_inertia_card (F : Type*) [Field F] [NumberField F]
    [IsGalois ℚ F] (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 F)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.ramificationIdx ℤ = Nat.card (P.inertia (F ≃ₐ[ℚ] F)) := by
  let Q := Ideal.span {(p : ℤ)}
  let localPrime : Q.IsPrime := by
    change (Ideal.span {(p : ℤ)}).IsPrime
    rw [Ideal.over_def P (Ideal.span {(p : ℤ)})]
    exact (inferInstance : P.IsPrime).comap (algebraMap ℤ (𝓞 F))
  let localNonzero : NeZero (p : ℤ) := ⟨by exact_mod_cast hp.ne_zero⟩
  calc
    P.ramificationIdx ℤ = Q.ramificationIdxIn (𝓞 F) :=
      (Ideal.ramificationIdxIn_eq_ramificationIdx Q P (F ≃ₐ[ℚ] F)).symm
    _ = Nat.card (P.inertia (F ≃ₐ[ℚ] F)) :=
      (Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[ℚ] F) Q P).symm

end Utilities
