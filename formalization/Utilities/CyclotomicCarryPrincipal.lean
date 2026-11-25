module

public import Utilities.CyclotomicDegreeOnePrime
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Utilities.IdealClassPrimeSieve

@[expose] public section

open IsDedekindDomain NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace Utilities

variable (N : ℕ) [NeZero N] (E : Type*) [Field E] [NumberField E]
  [IsCyclotomicExtension {N} ℚ E]

local notation "χ" => MulEquiv.symm (IsCyclotomicExtension.Rat.galEquivZMod N E)

variable (p : ℕ) [Fact p.Prime]

/-- The reduction at the conjugate prime multiplies the exponent parameter
by the cyclotomic unit. -/
theorem cyclotomicConjugateResidue_of_mulChar
    (red : 𝓞 E →+* ZMod p) (d : ℕ) (hd : p - 1 = N * d) (hd₀ : 0 < d)
    (x : ZMod N) (hx : x ≠ 0) (θ : MulChar (ZMod p) (𝓞 E))
    (hθ : ∀ z, red (θ z) = z ^ (d * x.val)) (hθN : ∀ z ≠ 0, (θ z) ^ N = 1)
    (b : (ZMod N)ˣ) (z : ZMod p) :
    cyclotomicConjugateResidue N E p red b (θ z) = z ^ (d * (x * (b : ZMod N)).val) := by
  by_cases hz : z = 0
  · have hx' : (x * (b : ZMod N)).val ≠ 0 := fun h0 =>
      hx (b.mul_left_eq_zero.mp ((ZMod.val_eq_zero _).mp h0))
    rw [hz, θ.map_zero, map_zero, zero_pow (mul_ne_zero hd₀.ne' hx')]
  · change red ((χ b) • θ z) = _
    rw [Rat.galEquivZMod_smul_of_pow_eq N E _ (hθN z hz), MulEquiv.apply_symm_apply,
      map_pow, hθ, ← pow_mul, ZMod.val_mul]
    let a := x.val * b.val.val
    have hm : d * x.val * b.val.val = d * (a % N) + (p - 1) * (a / N) := by
      calc
        _ = d * a := by dsimp [a]; ring
        _ = d * (a % N + N * (a / N)) := congrArg (d * ·) (Nat.mod_add_div a N).symm
        _ = _ := by rw [hd]; ring
    rw [hm, pow_add, pow_mul z (p - 1), ZMod.pow_card_sub_one_eq_one hz, one_pow, mul_one]

private theorem mulChar_ne_one_of_residue_pow
    {R : Type*} [CommRing R] (red : R →+* ZMod p) (θ : MulChar (ZMod p) R) (n : ℕ)
    (hn : ¬(p - 1) ∣ n) (hθ : ∀ z, red (θ z) = z ^ n) : θ ≠ 1 := by
  intro h
  apply hn
  have hall (u : (ZMod p)ˣ) : u ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hθ, h, MulChar.one_apply_coe, map_one, Units.val_one]
  simpa only [ZMod.card] using (FiniteField.forall_pow_eq_one_iff (ZMod p) n).mp hall

private theorem cyclotomicCarryIdealProduct_principal_nondegenerate
    (red : 𝓞 E →+* ZMod p) (v : HeightOneSpectrum (𝓞 E)) (hred : RingHom.ker red = v.asIdeal)
    (hpN : ¬ p ∣ N) (x y : ZMod N) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    (cyclotomicCarryIdealProduct N E x y
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩).val.IsPrincipal := by
  let ζ := (zeta_spec N ℚ E).toInteger
  have hζ := (zeta_spec N ℚ E).toInteger_isPrimitiveRoot
  have hζbar := isPrimitiveRoot_residue_of_not_dvd p N red hpN hζ
  have hζbar₀ : red ζ ≠ 0 := by
    intro heq
    have hpow : red ζ ^ N = 1 := hζbar.pow_eq_one
    rw [heq, zero_pow (NeZero.ne N)] at hpow
    exact zero_ne_one hpow
  obtain ⟨d, hd⟩ := hζbar.dvd_of_pow_eq_one (p - 1) (ZMod.pow_card_sub_one_eq_one hζbar₀)
  have hd₀ : 0 < d := by
    have hp := (Fact.out : p.Prime).two_le
    by_contra hd'
    have h : d = 0 := by omega
    rw [h, Nat.mul_zero] at hd
    omega
  have hpos {z : ZMod N} (hz : z ≠ 0) : 0 < d * z.val :=
    Nat.mul_pos hd₀ (Nat.pos_of_ne_zero fun h => hz ((ZMod.val_eq_zero _).mp h))
  obtain ⟨θ, hθ, hθN⟩ := exists_mulChar_of_residue_power p N red hpN hζ d x.val hd (hpos hx)
  obtain ⟨φ, hφ, hφN⟩ := exists_mulChar_of_residue_power p N red hpN hζ d y.val hd (hpos hy)
  have hnd (n : ℕ) (hn : (n : ZMod N) ≠ 0) : ¬(p - 1) ∣ d * n := by
    rw [hd, Nat.mul_comm N d, Nat.mul_dvd_mul_iff_left hd₀, ← ZMod.natCast_eq_zero_iff]
    exact hn
  have hθne : θ ≠ 1 := mulChar_ne_one_of_residue_pow p red θ _
    (hnd x.val (by simpa only [ZMod.natCast_zmod_val] using hx)) hθ
  have hφne : φ ≠ 1 := mulChar_ne_one_of_residue_pow p red φ _
    (hnd y.val (by simpa only [ZMod.natCast_zmod_val] using hy)) hφ
  have hθφ : θ * φ ≠ 1 := by
    apply mulChar_ne_one_of_residue_pow p red (θ * φ) (d * (x.val + y.val))
      (hnd _ (by simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hxy))
    intro z
    rw [MulChar.mul_apply, map_mul, hθ, hφ, ← pow_add, ← Nat.mul_add]
  obtain ⟨hinj, hs⟩ := cyclotomic_degreeOne_conjugates_split N E p red v hred hpN
  let I : (Ideal (𝓞 E))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  rw [cyclotomicCarryIdealProduct_eq_span_of_split_reductions N E p d hd hd₀ x y hx I
    (cyclotomicConjugatePrime N E v) hinj hs
    (fun b => Ideal.comap_symm (RingOfIntegers.mapRingEquiv ((χ b)⁻¹ : Gal(E/ℚ)).toRingEquiv))
    (cyclotomicConjugateResidue N E p red) (cyclotomicConjugateResidue_ker N E p red v hred)
    hθne hφne hθφ
    (cyclotomicConjugateResidue_of_mulChar N E p red d hd hd₀ x hx θ hθ hθN)
    (cyclotomicConjugateResidue_of_mulChar N E p red d hd hd₀ y hy φ hφ hφN)]
  exact ⟨⟨_, rfl⟩⟩

private theorem cyclotomicCarryIdealProduct_principal_neg (x : ZMod N) (hx : x ≠ 0)
    (I : (Ideal (𝓞 E))⁰) : (cyclotomicCarryIdealProduct N E x (-x) I).val.IsPrincipal := by
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {N} ℚ E
  let _ : Fintype Gal(E/ℚ) := Fintype.ofFinite _
  have hcarry (b : (ZMod N)ˣ) :
      zmodCarry (x * (b : ZMod N)) ((-x) * (b : ZMod N)) = 1 := by
    let a := x * (b : ZMod N)
    let _ : NeZero a := ⟨fun h => hx (b.mul_left_eq_zero.mp h)⟩
    rw [neg_mul]
    change zmodCarry a (-a) = 1
    rw [zmodCarry, ZMod.val_neg_of_ne_zero, Nat.add_sub_of_le (ZMod.val_lt a).le,
      Nat.div_self (NeZero.pos N)]
  let J := (cyclotomicCarryIdealProduct N E x (-x) I).val
  have hJ : J = (Ideal.relNorm ℤ I.val).map (algebraMap ℤ (𝓞 E)) := by
    change (nonZeroDivisors (Ideal (𝓞 E))).subtype (∏ b : (ZMod N)ˣ,
      nonzeroIdealMapOfRingEquiv (RingOfIntegers.mapRingEquiv ((χ b)⁻¹ : Gal(E/ℚ)).toRingEquiv) I ^
        zmodCarry (x * (b : ZMod N)) ((-x) * (b : ZMod N))) = _
    simp only [hcarry, pow_one, map_prod]
    let e : (ZMod N)ˣ ≃ Gal(E/ℚ) := (χ).toEquiv.trans (Equiv.inv _)
    exact (Equiv.prod_comp e fun σ => I.val.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv)).trans
      (prod_galois_map_ideal_eq_map_relNorm_int I.val (mem_nonZeroDivisors_iff_ne_zero.mp I.property))
  change J.IsPrincipal
  rw [hJ, Ideal.relNorm_int, Ideal.map_span, Set.image_singleton]
  exact ⟨⟨_, rfl⟩⟩

/-- The carry product at a degree-one prime coprime to the cyclotomic
level is principal for every pair of residues. -/
theorem cyclotomicCarryIdealProduct_principal_of_degreeOne
    (red : 𝓞 E →+* ZMod p) (v : HeightOneSpectrum (𝓞 E)) (hred : RingHom.ker red = v.asIdeal)
    (hpN : ¬ p ∣ N) (x y : ZMod N) :
    (cyclotomicCarryIdealProduct N E x y
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩).val.IsPrincipal := by
  by_cases hx : x = 0
  · have hcarry (z : ZMod N) : zmodCarry (0 : ZMod N) z = 0 := by
      rw [zmodCarry, ZMod.val_zero, zero_add, Nat.div_eq_of_lt (ZMod.val_lt z)]
    simp [hx, cyclotomicCarryIdealProduct, hcarry, Ideal.one_eq_top]
    exact top_isPrincipal
  by_cases hy : y = 0
  · have hcarry (z : ZMod N) : zmodCarry z (0 : ZMod N) = 0 := by
      rw [zmodCarry, ZMod.val_zero, add_zero, Nat.div_eq_of_lt (ZMod.val_lt z)]
    simp [hy, cyclotomicCarryIdealProduct, hcarry, Ideal.one_eq_top]
    exact top_isPrincipal
  by_cases hxy : x + y = 0
  · rw [show y = -x by linear_combination hxy]
    exact cyclotomicCarryIdealProduct_principal_neg N E x hx _
  · exact cyclotomicCarryIdealProduct_principal_nondegenerate N E p red v hred hpN x y hx hy hxy

/-- The weight-one element kills the class of each suitable degree-one prime. -/
theorem cyclotomicWeightOneClassAction_eq_zero_on_degreeOne
    (red : 𝓞 E →+* ZMod p) (v : HeightOneSpectrum (𝓞 E)) (hred : RingHom.ker red = v.asIdeal)
    (hpN : ¬p ∣ N) (a : ℕ) (ha : a.Coprime N) :
    (numberFieldClassGroupGaloisAction ℚ E).asAlgebraHom
      (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha)
      (Additive.ofMul (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) = 0 := by
  let I : (Ideal (𝓞 E))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  rw [cyclotomicWeightOneClassAction_apply_mk0]
  change Additive.ofMul (ClassGroup.mk0 (cyclotomicSmoothingQuotientIdealProduct N E a ha I)) =
    Additive.ofMul 1
  apply congrArg Additive.ofMul
  rw [cyclotomicSmoothingQuotientIdealProduct_eq_prod_carry, map_prod]
  apply Finset.prod_eq_one
  intro j _
  exact (ClassGroup.mk0_eq_one_iff _).mpr (cyclotomicCarryIdealProduct_principal_of_degreeOne N E p
    red v hred hpN _ _)

/-- Degree-one representatives away from the modulus suffice to conclude
weight-one annihilation from the Jacobi-sum principal-ideal identities. -/
theorem cyclotomicWeightOneClassAction_eq_zero_of_degreeOne_representatives
    (hrep : ∀ c : ClassGroup (𝓞 E),
      ∃ q : ℕ, q.Prime ∧ ¬q ∣ N ∧ ∃ (v : HeightOneSpectrum (𝓞 E)) (red : 𝓞 E →+* ZMod q),
        RingHom.ker red = v.asIdeal ∧
        ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ = c)
    (a : ℕ) (ha : a.Coprime N) (c : Additive (ClassGroup (𝓞 E))) :
    (numberFieldClassGroupGaloisAction ℚ E).asAlgebraHom
      (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha) c = 0 := by
  obtain ⟨q, hq, hqN, v, red, hred, hc⟩ := hrep c.toMul
  let _ : Fact q.Prime := ⟨hq⟩
  rw [show c = Additive.ofMul (ClassGroup.mk0
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩) from congrArg Additive.ofMul hc.symm]
  exact cyclotomicWeightOneClassAction_eq_zero_on_degreeOne N E q red v hred hqN a ha

/-- The primes excluded from the Jacobi-sum proof are the primes with no
degree-one residue map at a rational prime coprime to the modulus. -/
def cyclotomicExcludedPrimeSet : Set (HeightOneSpectrum (𝓞 E)) :=
  {v | ¬ ∃ q : ℕ, q.Prime ∧ ¬q ∣ N ∧ ∃ red : 𝓞 E →+* ZMod q, RingHom.ker red = v.asIdeal}

-- The remaining primes generate the class group, so a homomorphism can be
-- checked on the degree-one primes away from the conductor.
omit [NeZero N] [IsCyclotomicExtension {N} ℚ E] in
private theorem classGroupHom_eq_one_of_cyclotomicDegreeOne
    (hs : Summable (fun v : cyclotomicExcludedPrimeSet N E => (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹))
    (f : ClassGroup (𝓞 E) →* ClassGroup (𝓞 E))
    (h : ∀ (q : ℕ) [Fact q.Prime], ¬ q ∣ N → ∀ (v : HeightOneSpectrum (𝓞 E))
      (red : 𝓞 E →+* ZMod q), RingHom.ker red = v.asIdeal →
        f (ClassGroup.mk0 (heightOnePrimeIdeal E v)) = 1)
    (c : ClassGroup (𝓞 E)) : f c = 1 := by
  let S := cyclotomicExcludedPrimeSet N E
  let G : Set (ClassGroup (𝓞 E)) := Set.range (fun v : ↥(Sᶜ : Set (HeightOneSpectrum (𝓞 E))) =>
    ClassGroup.mk0 (heightOnePrimeIdeal E v.val))
  have hle : Subgroup.closure G ≤ f.ker := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨v, hv⟩, rfl⟩
    have hex : ¬ ¬ ∃ q : ℕ, q.Prime ∧ ¬q ∣ N ∧ ∃ red : 𝓞 E →+* ZMod q, RingHom.ker red = v.asIdeal :=
      hv
    obtain ⟨q, hq, hqN, red, hred⟩ := not_not.mp hex
    let _ : Fact q.Prime := ⟨hq⟩
    exact h q hqN v red hred
  have htop : Subgroup.closure G = ⊤ := closure_primeClasses_compl_eq_top_of_summable E S hs
  exact MonoidHom.mem_ker.mp (hle (htop.symm ▸ Subgroup.mem_top c))

/-- Principality of the individual Jacobi carry products extends to every
nonzero ideal once degree-one primes generate the class group. -/
theorem cyclotomicCarryIdealProduct_principal_of_summable_excludedPrimes
    (hs : Summable (fun v : cyclotomicExcludedPrimeSet N E => (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹))
    (x y : ZMod N) (I : (Ideal (𝓞 E))⁰) :
    (cyclotomicCarryIdealProduct N E x y I).val.IsPrincipal := by
  let c (t : (ZMod N)ˣ) := zmodCarry (x * t.val) (y * t.val)
  let e (t : (ZMod N)ˣ) := RingOfIntegers.mapRingEquiv ((χ t)⁻¹ : Gal(E/ℚ)).toRingEquiv
  let f : ClassGroup (𝓞 E) →* ClassGroup (𝓞 E) :=
    { toFun := fun z => ∏ t : (ZMod N)ˣ, classGroupMulEquivOfRingEquiv E E (e t) z ^ c t
      map_one' := by simp
      map_mul' := by intro a b; simp only [map_mul, mul_pow, Finset.prod_mul_distrib] }
  have hf (J : (Ideal (𝓞 E))⁰) :
      f (ClassGroup.mk0 J) = ClassGroup.mk0 (cyclotomicCarryIdealProduct N E x y J) := by
    change (∏ t : (ZMod N)ˣ, classGroupMulEquivOfRingEquiv E E (e t) (ClassGroup.mk0 J) ^ c t) =
      ClassGroup.mk0 (∏ t : (ZMod N)ˣ, cyclotomicInverseConjugateIdeal N E t J ^ c t)
    rw [map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [map_pow]
    exact congrArg (· ^ c t) (classGroupMulEquivOfRingEquiv_mk0_map E E (e t) J)
  apply (ClassGroup.mk0_eq_one_iff _).mp
  rw [← hf]
  apply classGroupHom_eq_one_of_cyclotomicDegreeOne N E hs f _ (ClassGroup.mk0 I)
  intro q _ hqN v red hred
  rw [hf]
  exact (ClassGroup.mk0_eq_one_iff _).mpr
    (cyclotomicCarryIdealProduct_principal_of_degreeOne N E q red v hred hqN x y)

/-- The weight-one annihilation follows from summability of the inverse
norms of the excluded primes, via generation by the remaining classes. -/
theorem cyclotomicWeightOneClassAction_eq_zero_of_summable_excludedPrimes
    (hs : Summable (fun v : cyclotomicExcludedPrimeSet N E => (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹))
    (a : ℕ) (ha : a.Coprime N) (c : Additive (ClassGroup (𝓞 E))) :
    (numberFieldClassGroupGaloisAction ℚ E).asAlgebraHom
      (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha) c = 0 := by
  let A := (numberFieldClassGroupGaloisAction ℚ E).asAlgebraHom
    (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha)
  let f : ClassGroup (𝓞 E) →* ClassGroup (𝓞 E) := MonoidHom.toAdditive.symm A.toAddMonoidHom
  apply congrArg Additive.ofMul (classGroupHom_eq_one_of_cyclotomicDegreeOne N E hs f _ c.toMul)
  intro q _ hqN v red hred
  exact congrArg Additive.toMul
    (cyclotomicWeightOneClassAction_eq_zero_on_degreeOne N E q red v hred hqN a ha)

end Utilities
