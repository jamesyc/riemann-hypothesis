module

public import Utilities.WeightOneStickelbergerClassGroup
public import Utilities.ResiduePowerCharacters
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open IsDedekindDomain NumberField IsCyclotomicExtension
open scoped NumberField Pointwise nonZeroDivisors

namespace Utilities

/-- Ring homomorphisms into `ZMod p` with the same kernel agree. -/
theorem ringHom_eq_of_ker_eq_zmod {R : Type*} [CommRing R] {p : ℕ} [NeZero p]
    {f g : R →+* ZMod p} (h : RingHom.ker f = RingHom.ker g) : f = g := by
  ext x
  let n := (g x).val
  have hn : g (n : R) = g x := by rw [map_natCast]; exact ZMod.natCast_zmod_val _
  have hz : x - (n : R) ∈ RingHom.ker g := RingHom.mem_ker.mpr (by rw [map_sub, hn, sub_self])
  rw [← h] at hz
  have hf := RingHom.mem_ker.mp hz
  rw [map_sub, sub_eq_zero, map_natCast] at hf
  rw [map_natCast] at hn
  exact hf.trans hn

variable (N : ℕ) [NeZero N] (E : Type*) [Field E] [NumberField E]
  [IsCyclotomicExtension {N} ℚ E]

local notation "χ" => MulEquiv.symm (IsCyclotomicExtension.Rat.galEquivZMod N E)

/-- The conjugate of a prime indexed as in the carry product. -/
noncomputable def cyclotomicConjugatePrime (v : HeightOneSpectrum (𝓞 E)) (b : (ZMod N)ˣ) :
    HeightOneSpectrum (𝓞 E) :=
  HeightOneSpectrum.equivOfRingEquiv
    (RingOfIntegers.mapRingEquiv ((χ b)⁻¹ : Gal(E/ℚ)).toRingEquiv) v

theorem cyclotomicConjugatePrime_asIdeal (v : HeightOneSpectrum (𝓞 E)) (b : (ZMod N)ˣ) :
    (cyclotomicConjugatePrime N E v b).asIdeal = (χ b)⁻¹ • v.asIdeal := by
  rw [Ideal.pointwise_smul_def]
  change v.asIdeal.comap (RingOfIntegers.mapRingEquiv ((χ b)⁻¹ : Gal(E/ℚ)).toRingEquiv).symm =
    v.asIdeal.map (MulSemiringAction.toRingEquiv Gal(E/ℚ) (𝓞 E) (χ b)⁻¹)
  rw [Ideal.comap_symm]
  rfl

variable (p : ℕ) [Fact p.Prime]

/-- A residue map at the conjugate prime is obtained by applying the direct
cyclotomic automorphism before reducing. -/
noncomputable def cyclotomicConjugateResidue (red : 𝓞 E →+* ZMod p) (b : (ZMod N)ˣ) :
    𝓞 E →+* ZMod p :=
  red.comp (RingOfIntegers.mapRingEquiv (χ b).toRingEquiv).toRingHom

theorem cyclotomicConjugateResidue_ker (red : 𝓞 E →+* ZMod p) (v : HeightOneSpectrum (𝓞 E))
    (hred : RingHom.ker red = v.asIdeal) (b : (ZMod N)ˣ) :
    RingHom.ker (cyclotomicConjugateResidue N E p red b) = (cyclotomicConjugatePrime N E v b).asIdeal := by
  have he : (RingOfIntegers.mapRingEquiv ((χ b)⁻¹ : Gal(E/ℚ)).toRingEquiv).symm =
      RingOfIntegers.mapRingEquiv (χ b).toRingEquiv := by ext z; rfl
  change RingHom.ker (red.comp (RingOfIntegers.mapRingEquiv (χ b).toRingEquiv).toRingHom) =
    v.asIdeal.comap (RingOfIntegers.mapRingEquiv ((χ b)⁻¹ : Gal(E/ℚ)).toRingEquiv).symm.toRingHom
  rw [← hred, he]
  rfl

/-- A degree-one prime over a prime coprime to the modulus has trivial
decomposition group in the cyclotomic extension. -/
theorem cyclotomic_stabilizer_eq_one_of_degreeOne
    (red : 𝓞 E →+* ZMod p) (v : HeightOneSpectrum (𝓞 E)) (hred : RingHom.ker red = v.asIdeal)
    (hpN : ¬ p ∣ N) (σ : Gal(E/ℚ)) (hσ : σ • v.asIdeal = v.asIdeal) : σ = 1 := by
  let b := (Rat.galEquivZMod N E) σ
  have hb : χ b = σ := (Rat.galEquivZMod N E).symm_apply_apply σ
  have hσinv : σ⁻¹ • v.asIdeal = v.asIdeal :=
    (congrArg (fun I : Ideal (𝓞 E) => σ⁻¹ • I) hσ).symm.trans (inv_smul_smul σ v.asIdeal)
  have hker : RingHom.ker (cyclotomicConjugateResidue N E p red b) = RingHom.ker red := by
    rw [cyclotomicConjugateResidue_ker N E p red v hred, cyclotomicConjugatePrime_asIdeal, hb, hσinv, hred]
  let ζ := (zeta_spec N ℚ E).toInteger
  have hζ := (zeta_spec N ℚ E).toInteger_isPrimitiveRoot
  have hζbar := isPrimitiveRoot_residue_of_not_dvd p N red hpN hζ
  have hfix := DFunLike.congr_fun (ringHom_eq_of_ker_eq_zmod hker) ζ
  change red (RingOfIntegers.mapRingEquiv (χ b).toRingEquiv ζ) = red ζ at hfix
  rw [hb] at hfix
  change red (σ • ζ) = red ζ at hfix
  rw [Rat.galEquivZMod_smul_of_pow_eq N E σ hζ.pow_eq_one, map_pow] at hfix
  have heq : (red ζ) ^ b.val.val = (red ζ) ^ (1 : ℕ) := hfix.trans (pow_one _).symm
  rw [(hζbar.isOfFinOrder (NeZero.ne N)).pow_inj_mod, ← hζbar.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val] at heq
  apply (Rat.galEquivZMod N E).injective
  rw [map_one]
  apply Units.ext
  change (b : ZMod N) = (1 : ZMod N)
  simpa only [Nat.cast_one] using heq

omit [NumberField E] in
/-- A prime whose residue map targets a prime field lies over the
corresponding rational prime. -/
theorem liesOver_intPrime_of_residueMap
    (red : 𝓞 E →+* ZMod p) (v : HeightOneSpectrum (𝓞 E))
    (hred : RingHom.ker red = v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  rw [← hred]
  ext x
  change x ∈ Ideal.span ({(p : ℤ)} : Set ℤ) ↔ red (x : 𝓞 E) = 0
  rw [Ideal.mem_span_singleton, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The conjugates of a degree-one prime enumerate the distinct primes
above the rational prime, each with ramification index one. -/
theorem cyclotomic_degreeOne_conjugates_split
    (red : 𝓞 E →+* ZMod p) (v : HeightOneSpectrum (𝓞 E)) (hred : RingHom.ker red = v.asIdeal)
    (hpN : ¬ p ∣ N) :
    Function.Injective (cyclotomicConjugatePrime N E v) ∧
      Ideal.span ({(p : 𝓞 E)} : Set (𝓞 E)) =
        ∏ b, (cyclotomicConjugatePrime N E v b).asIdeal := by
  classical
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {N} ℚ E
  let A := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hA : A ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  let _ : A.IsMaximal := inferInstanceAs (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal
  let _ : v.asIdeal.LiesOver A := liesOver_intPrime_of_residueMap E p red v hred
  let f (b : (ZMod N)ˣ) : A.primesOver (𝓞 E) :=
    ⟨(χ b)⁻¹ • v.asIdeal, inferInstance, inferInstance⟩
  have hfi : Function.Injective f := by
    intro b c hbc
    have heq : (χ b)⁻¹ • v.asIdeal = (χ c)⁻¹ • v.asIdeal := congrArg Subtype.val hbc
    have hstab : ((χ c) * (χ b)⁻¹) • v.asIdeal = v.asIdeal := by
      rw [mul_smul, heq, smul_inv_smul]
    have hw := cyclotomic_stabilizer_eq_one_of_degreeOne N E p red v hred hpN _ hstab
    exact (χ).injective (mul_inv_eq_one.mp hw).symm
  have hfs : Function.Surjective f := by
    intro Q
    let _ : Q.val.IsPrime := Q.property.1
    let _ : Q.val.LiesOver A := Q.property.2
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup A v.asIdeal Q.val Gal(E/ℚ)
    refine ⟨(Rat.galEquivZMod N E) σ⁻¹, Subtype.ext ?_⟩
    change ((χ ((Rat.galEquivZMod N E) σ⁻¹))⁻¹) • v.asIdeal = Q.val
    rw [MulEquiv.symm_apply_apply, inv_inv, hσ]
  refine ⟨fun b c hbc => hfi (Subtype.ext ?_), ?_⟩
  · simpa only [cyclotomicConjugatePrime_asIdeal] using congrArg HeightOneSpectrum.asIdeal hbc
  · have hnorm : ∀ Q : A.primesOver (𝓞 E), Q.val.ramificationIdx ℤ = 1 := by
      intro Q
      let _ : Q.val.IsPrime := Q.property.1
      let _ : Q.val.LiesOver A := Q.property.2
      exact Rat.ramificationIdx_eq_of_not_dvd p E Q.val hpN
    calc
      _ = A.map (algebraMap ℤ (𝓞 E)) := by simp [A, Ideal.map_span]
      _ = ∏ Q : A.primesOver (𝓞 E), Q.val ^ Q.val.ramificationIdx ℤ := by
        rw [Ideal.map_algebraMap_eq_finsetProd_pow hA, ← Finset.prod_set_coe]
      _ = ∏ Q : A.primesOver (𝓞 E), Q.val := by simp only [hnorm, pow_one]
      _ = _ := by
        symm
        apply Fintype.prod_equiv (Equiv.ofBijective f ⟨hfi, hfs⟩)
        intro b
        exact cyclotomicConjugatePrime_asIdeal N E v b

/-- A rational prime congruent to one modulo the cyclotomic level
has a prime above it with a prime-field residue map. -/
theorem exists_cyclotomic_degreeOne_residue
    (hcong : p ≡ 1 [MOD N]) :
    ∃ (v : HeightOneSpectrum (𝓞 E)) (red : 𝓞 E →+* ZMod p),
      RingHom.ker red = v.asIdeal := by
  have hp : p.Prime := Fact.out
  have hcop : p.Coprime N := Nat.coprime_of_mul_modEq_one 1 (by simpa only [mul_one] using hcong)
  have hpN : ¬ p ∣ N := hp.coprime_iff_not_dvd.mp hcop
  let A := Ideal.span ({(p : ℤ)} : Set ℤ)
  let _ : A.IsMaximal := inferInstanceAs (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal
  obtain ⟨P, hP, hPA⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral A (S := 𝓞 E)
  let _ : P.IsPrime := hP.isPrime
  let _ : P.LiesOver A := hPA
  have hA : A ≠ ⊥ := by
    change Ideal.span {(p : ℤ)} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot hA P⟩
  have hf : P.inertiaDeg ℤ = 1 := by
    have he : (p : ZMod N) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hcong
    rw [Rat.inertiaDeg_eq_of_not_dvd (p := p) E P hpN, he, orderOf_one]
  have hnorm := Ideal.absNorm_pow_inertiaDeg A P
  have hcard : Nat.card (𝓞 E ⧸ P) = p := by
    rw [← Ideal.absNorm_eq_natCard, ← hnorm, hf, pow_one, Ideal.absNorm_eq_natCard]
    change Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p
    rw [Int.card_ideal_quot]
  let _ : Finite (𝓞 E ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let _ : Fintype (𝓞 E ⧸ P) := Fintype.ofFinite _
  let e₀ := ZMod.ringEquivOfPrime (R := 𝓞 E ⧸ P) hp (Nat.card_eq_fintype_card.symm.trans hcard)
  let red := e₀.symm.toRingHom.comp (Ideal.Quotient.mk P)
  refine ⟨v, red, ?_⟩
  ext x
  change e₀.symm (Ideal.Quotient.mk P x) = 0 ↔ x ∈ P
  rw [map_eq_zero_iff _ e₀.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

end Utilities
