module

public import Utilities.ArtinIdeal
public import Utilities.IdealPairPrimeTransport
import Utilities.InertiaRestriction
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

namespace Utilities

private theorem finiteField_card_le_of_pow_eq_self {F : Type*} [Field F] [Fintype F]
    {q : ℕ} (hq : 1 < q) (hpow : ∀ x : F, x ^ q = x) : Fintype.card F ≤ q := by
  have hu (z : Fˣ) : z ^ (q - 1) = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    apply mul_right_cancel₀ z.ne_zero
    rw [← pow_succ, Nat.sub_add_cancel hq.le, hpow, one_mul]
  have hdvd := (FiniteField.forall_pow_eq_one_iff F (q - 1)).mp hu
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hq) hdvd
  omega

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Trivial arithmetic Frobenius at a prime forces its residue field to
have the same cardinality as the residue field below it. -/
theorem absNorm_eq_of_numberFieldPrimeArtin_eq_one (v : HeightOneSpectrum (𝓞 K))
    (Q : v.asIdeal.primesOver (𝓞 L)) (h : numberFieldPrimeArtin K L v = 1) :
    Ideal.absNorm Q.val = Ideal.absNorm v.asIdeal := by
  let P := Q.val
  let _ : v.asIdeal.IsMaximal := v.isMaximal
  let _ : P.IsPrime := Q.property.1
  let _ : P.LiesOver v.asIdeal := Q.property.2
  let _ : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P v.asIdeal
  let k := 𝓞 L ⧸ P
  let _ : Field k := Ideal.Quotient.field P
  let _ : Finite k := numberField_finite_residue_above K L v Q
  let _ : Fintype k := Fintype.ofFinite k
  let q := Ideal.absNorm v.asIdeal
  have hq₀ := Ideal.absNorm_pos_of_nonZeroDivisors (heightOnePrimeIdeal K v)
  have hq : 1 < q := by
    have hne : q ≠ 1 := fun he => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp he)
    change 0 < q at hq₀
    omega
  have hpow (x : k) : x ^ q = x := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hf := numberFieldPrimeArtin_spec K L v Q
    rw [h] at hf
    have hz := hf z
    change (1 : Gal(L/K)) • z - z ^ Nat.card (𝓞 K ⧸ P.under (𝓞 K)) ∈ P at hz
    rw [one_smul, ← Ideal.over_def P v.asIdeal, ← Ideal.absNorm_eq_natCard] at hz
    simpa only [map_pow] using (Ideal.Quotient.eq.mpr hz).symm
  have hCard : Fintype.card k = Ideal.absNorm P := by
    rw [← Nat.card_eq_fintype_card, ← Ideal.absNorm_eq_natCard]
  have hupper : Ideal.absNorm P ≤ q := hCard ▸ finiteField_card_le_of_pow_eq_self hq hpow
  have hlow := Nat.card_le_card_of_injective (algebraMap (𝓞 K ⧸ P.under (𝓞 K)) k)
    (Ideal.algebraMap_quotient_injective (R := 𝓞 K) (I := P))
  rw [← Ideal.absNorm_eq_natCard, ← Ideal.absNorm_eq_natCard, ← Ideal.over_def P v.asIdeal] at hlow
  exact le_antisymm hupper hlow

private theorem card_galois_eq_one_of_primeArtin_eq_one_off_summable
    (s : Set (HeightOneSpectrum (𝓞 K)))
    (hs : Summable (fun v : s => (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹))
    (hI : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ s →
      ∀ Q : v.asIdeal.primesOver (𝓞 L), ∀ σ ∈ Q.val.inertia Gal(L/K), σ = 1)
    (hF : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ s → numberFieldPrimeArtin K L v = 1) :
    Nat.card Gal(L/K) = 1 := by
  have hcard : 0 < Nat.card Gal(L/K) := Nat.card_pos
  by_contra hne
  have hgt : 1 < Nat.card Gal(L/K) := by omega
  apply not_forall_two_normPreserving_primesOver_off_summable K L s hs
  intro v hv
  let p := v.asIdeal
  obtain ⟨Q⟩ := numberField_primesOver_nonempty K L v
  let P := Q.val
  let _ : P.IsPrime := Q.property.1
  let _ : P.LiesOver p := Q.property.2
  let _ : p.IsPrime := v.isPrime
  have hcardI : Nat.card (P.inertia Gal(L/K)) = 1 := by
    let _ : Subsingleton (P.inertia Gal(L/K)) := ⟨fun x y => Subtype.ext
      ((hI v hv Q x.val x.property).trans (hI v hv Q y.val y.property).symm)⟩
    exact Nat.card_of_subsingleton 1
  have he : p.ramificationIdxIn (𝓞 L) = 1 :=
    (Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) p P).symm.trans hcardI
  have hnorm : Ideal.absNorm P = Ideal.absNorm p :=
    absNorm_eq_of_numberFieldPrimeArtin_eq_one K L v Q (hF v hv)
  have hpow := Ideal.absNorm_pow_inertiaDeg p P
  rw [hnorm] at hpow
  have hq : 1 < Ideal.absNorm p := by
    have hn := Ideal.absNorm_pos_of_nonZeroDivisors (heightOnePrimeIdeal K v)
    have heq : Ideal.absNorm p ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    change 0 < Ideal.absNorm p at hn
    omega
  have hf : P.inertiaDeg (𝓞 K) = 1 :=
    (pow_right_injective₀ (zero_lt_one.trans hq) (ne_of_gt hq)) (hpow.trans (pow_one _).symm)
  have hn := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 L) Gal(L/K)
  rw [he, Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(L/K), hf, one_mul, mul_one] at hn
  have hgt' : 1 < Nat.card (p.primesOver (𝓞 L)) := by
    change 1 < (p.primesOver (𝓞 L)).ncard
    rw [hn]
    exact hgt
  let _ : Finite (p.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite (B := 𝓞 L) p).to_subtype
  let _ : Nontrivial (p.primesOver (𝓞 L)) := (Finite.one_lt_card_iff_nontrivial).mp hgt'
  obtain ⟨Q₀, Q₁, hne'⟩ := exists_pair_ne (p.primesOver (𝓞 L))
  let w (J : p.primesOver (𝓞 L)) : HeightOneSpectrum (𝓞 L) :=
    let _ : J.val.LiesOver p := J.property.2
    ⟨J.val, J.property.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot J.val⟩
  exact ⟨w Q₀, w Q₁, fun h => hne' (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)),
    Q₀.property.2.over.symm, Q₁.property.2.over.symm,
    absNorm_eq_of_numberFieldPrimeArtin_eq_one K L v Q₀ (hF v hv),
    absNorm_eq_of_numberFieldPrimeArtin_eq_one K L v Q₁ (hF v hv)⟩

/-- A nontrivial abelian extension has a nontrivial Frobenius outside
a set of primes with summable inverse norms if inertia is trivial there. -/
theorem exists_primeArtin_ne_one_off_summable
    (s : Set (HeightOneSpectrum (𝓞 K)))
    (hs : Summable (fun v : s => (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹))
    (hI : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ s →
      ∀ Q : v.asIdeal.primesOver (𝓞 L), ∀ σ ∈ Q.val.inertia Gal(L/K), σ = 1)
    (hdegree : 1 < Nat.card Gal(L/K)) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ s ∧ numberFieldPrimeArtin K L v ≠ 1 := by
  classical
  by_contra! hf
  exact hdegree.ne' (card_galois_eq_one_of_primeArtin_eq_one_off_summable K L s hs hI hf)

/-- Arithmetic Frobenius generates the Galois group of a finite abelian
extension unramified at the finite primes. -/
theorem numberFieldIdealArtin_surjective
    (hI : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ → ∀ σ ∈ P.inertia Gal(L/K), σ = 1) :
    Function.Surjective (numberFieldIdealArtin K L) := by
  let H := (numberFieldIdealArtin K L).range
  let M := IntermediateField.fixedField H
  let _ : NumberField M := NumberField.of_module_finite K M
  let _ : IsAbelianGalois K M := IsAbelianGalois.tower_bot K M L
  have hI' : ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime], Q ≠ ⊥ → ∀ τ ∈ Q.inertia Gal(M/K), τ = 1 := by
    intro Q _ hQ τ hτ
    let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral Q (S := 𝓞 L)
    let _ : P.IsPrime := hP.isPrime
    let _ : P.LiesOver Q := hPQ
    have hmap := numberField_inertia_map_restrictNormal_tower (K := K) Q P
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hτ)
    rw [hI P (Ideal.ne_bot_of_liesOver_of_ne_bot hQ P) σ hσ, map_one]
  have hF : ∀ v : HeightOneSpectrum (𝓞 K), numberFieldPrimeArtin K M v = 1 := by
    intro v
    rw [← numberFieldPrimeArtin_restrictNormal K L M v (fun Q τ hτ => by
      let _ : Q.val.IsPrime := Q.property.1
      let _ : Q.val.LiesOver v.asIdeal := Q.property.2
      exact hI' Q.val (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.val) τ hτ)]
    have hmem : numberFieldPrimeArtin K L v ∈ H :=
      ⟨FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩,
        numberFieldIdealArtin_mk0_prime K L v⟩
    change AlgEquiv.restrictNormalHom M (numberFieldPrimeArtin K L v) = 1
    apply MonoidHom.mem_ker.mp
    rw [M.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField H]
    exact hmem
  let _ : Finite (↥(∅ : Set (HeightOneSpectrum (𝓞 K)))) := Set.finite_empty.to_subtype
  have hcard := card_galois_eq_one_of_primeArtin_eq_one_off_summable K M ∅ Summable.of_finite
    (fun v _ Q σ hσ => by
      let _ : Q.val.IsPrime := Q.property.1
      let _ : Q.val.LiesOver v.asIdeal := Q.property.2
      exact hI' Q.val (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.val) σ hσ)
    (fun v _ => hF v)
  have hM : M = ⊥ := (IntermediateField.finrank_eq_one_iff : Module.finrank K M = 1 ↔ M = ⊥).mp <|
    (IsGalois.card_aut_eq_finrank K M).symm.trans hcard
  have hH : H = ⊤ := by rw [← IntermediateField.fixingSubgroup_fixedField H,
    show IntermediateField.fixedField H = M from rfl, hM, IntermediateField.fixingSubgroup_bot]
  intro σ
  change σ ∈ H
  exact hH.symm ▸ (Subgroup.mem_top σ)

/-- Once the Artin map kills principal ideals its induced class-group map is surjective. -/
theorem numberFieldClassGroupArtinOfPrincipal_surjective
    (hp : ∀ x : Kˣ, numberFieldIdealArtin K L (toPrincipalIdeal (𝓞 K) K x) = 1)
    (hI : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ → ∀ σ ∈ P.inertia Gal(L/K), σ = 1) :
    Function.Surjective (numberFieldClassGroupArtinOfPrincipal K L hp) := by
  intro σ
  obtain ⟨I, hIσ⟩ := numberFieldIdealArtin_surjective K L hI σ
  refine ⟨ClassGroup.mk K I, ?_⟩
  change classGroupHomOfTrivialPrincipal (numberFieldIdealArtin K L) hp (ClassGroup.mk K I) = σ
  rw [classGroupHomOfTrivialPrincipal_mk, hIσ]

end Utilities
