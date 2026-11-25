module

public import Utilities.ClassGroupGaloisAction
public import Utilities.HigherStickelbergerCoefficients
public import Utilities.JacobiSumSplitIdeal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

@[expose] public section

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors

namespace Utilities

/-- The carry in adding the two least nonnegative residues. -/
def zmodCarry {N : ℕ} (x y : ZMod N) : ℕ := (x.val + y.val) / N

theorem zmodCarry_eq_ite {N : ℕ} [NeZero N] (x y : ZMod N) :
    zmodCarry x y = if N ≤ x.val + y.val then 1 else 0 := by
  unfold zmodCarry
  have hlt : x.val + y.val < N * 2 := by
    have hx := ZMod.val_lt x
    have hy := ZMod.val_lt y
    omega
  by_cases h : N ≤ x.val + y.val
  · rw [ite_eq_left h]
    have hl : 1 ≤ (x.val + y.val) / N := (Nat.le_div_iff_mul_le (NeZero.pos N)).mpr (by simpa using h)
    have hr : (x.val + y.val) / N < 2 := (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr (by simpa [mul_comm] using hlt)
    omega
  · rw [ite_eq_right h, Nat.div_eq_of_lt (lt_of_not_ge h)]

/-- The quotient of a multiple of a residue is the sum of the successive
binary carries. -/
theorem mul_div_eq_sum_zmodCarry {N : ℕ} [NeZero N] (a : ℕ) (y : ZMod N) :
    a * y.val / N = ∑ j ∈ Finset.range a, zmodCarry ((j : ZMod N) * y) y := by
  induction a with
  | zero => simp
  | succ j hj =>
    rw [Finset.sum_range_succ, ← hj]
    have hval : ((j : ZMod N) * y).val = (j * y.val) % N := by
      calc
        _ = ((j : ZMod N) * (y.val : ZMod N)).val :=
          congrArg (fun z : ZMod N => ((j : ZMod N) * z).val) (ZMod.natCast_zmod_val y).symm
        _ = _ := by rw [← Nat.cast_mul, ZMod.val_natCast]
    have hstep : (j + 1) * y.val = ((j * y.val) % N + y.val) + N * (j * y.val / N) := by
      calc
        _ = j * y.val + y.val := by rw [Nat.add_mul, one_mul]
        _ = ((j * y.val) % N + N * (j * y.val / N)) + y.val :=
          congrArg (fun x => x + y.val) (Nat.mod_add_div (j * y.val) N).symm
        _ = _ := by ac_rfl
    rw [zmodCarry, hval, hstep, Nat.add_mul_div_left _ _ (NeZero.pos N), add_comm]

variable (N : ℕ) [NeZero N] (E : Type*) [Field E] [NumberField E]
  [IsCyclotomicExtension {N} ℚ E]

local notation "χ" => MulEquiv.symm (IsCyclotomicExtension.Rat.galEquivZMod N E)
local notation "ρ" => numberFieldClassGroupGaloisAction ℚ E

/-- Transport an integral ideal by the inverse of a cyclotomic automorphism. -/
noncomputable def cyclotomicInverseConjugateIdeal (t : (ZMod N)ˣ) :
    (Ideal (𝓞 E))⁰ →* (Ideal (𝓞 E))⁰ :=
  nonzeroIdealMapOfRingEquiv (RingOfIntegers.mapRingEquiv ((χ t)⁻¹ : Gal(E/ℚ)).toRingEquiv)

/-- The ideal product with the Euclidean quotients from smoothing as exponents. -/
noncomputable def cyclotomicSmoothingQuotientIdealProduct (a : ℕ) (ha : a.Coprime N)
    (I : (Ideal (𝓞 E))⁰) : (Ideal (𝓞 E))⁰ :=
  ∏ b : (ZMod N)ˣ, (cyclotomicInverseConjugateIdeal N E b I) ^
    (a * inverseSmoothingResidue a ha b / N)

/-- The product with the binary carry exponents in the Jacobi-sum ideal formula. -/
noncomputable def cyclotomicCarryIdealProduct (x y : ZMod N) (I : (Ideal (𝓞 E))⁰) :
    (Ideal (𝓞 E))⁰ :=
  ∏ b : (ZMod N)ˣ, (cyclotomicInverseConjugateIdeal N E b I) ^
      zmodCarry (x * (b : ZMod N)) (y * (b : ZMod N))

/-- Once the split primes and residue reductions are identified, the
inverse Jacobi sum generates the cyclotomic carry product. -/
theorem cyclotomicCarryIdealProduct_eq_span_of_split_reductions
    (p : ℕ) [Fact p.Prime] (d : ℕ) (hd : p - 1 = N * d) (hd₀ : 0 < d)
    (x y : ZMod N) (hx : x ≠ 0) (I : (Ideal (𝓞 E))⁰)
    (P : (ZMod N)ˣ → HeightOneSpectrum (𝓞 E)) (hinj : Function.Injective P)
    (hs : Ideal.span ({(p : 𝓞 E)} : Set (𝓞 E)) = ∏ b, (P b).asIdeal)
    (hP : ∀ b, (P b).asIdeal = (cyclotomicInverseConjugateIdeal N E b I).val)
    (red : (ZMod N)ˣ → 𝓞 E →+* ZMod p) (hker : ∀ b, RingHom.ker (red b) = (P b).asIdeal)
    {θ φ : MulChar (ZMod p) (𝓞 E)} (hθ : θ ≠ 1) (hφ : φ ≠ 1) (hθφ : θ * φ ≠ 1)
    (hredθ : ∀ b z, red b (θ z) = z ^ (d * (x * (b : ZMod N)).val))
    (hredφ : ∀ b z, red b (φ z) = z ^ (d * (y * (b : ZMod N)).val)) :
    (cyclotomicCarryIdealProduct N E x y I).val = Ideal.span ({jacobiSum θ⁻¹ φ⁻¹} : Set (𝓞 E)) := by
  let i (b : (ZMod N)ˣ) := d * (x * (b : ZMod N)).val
  let j (b : (ZMod N)ˣ) := d * (y * (b : ZMod N)).val
  have hi (b : (ZMod N)ˣ) : 0 < i b :=
    Nat.mul_pos hd₀ (Nat.pos_of_ne_zero fun h =>
      hx (b.mul_left_eq_zero.mp ((ZMod.val_eq_zero _).mp h)))
  have hlt (z : ZMod N) : d * z.val < p - 1 := by
    rw [hd, Nat.mul_comm N d]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt z) hd₀
  have hJ := (jacobiSum_splitIdeal_factorization p P hinj hs red hker hθ hφ hθφ
    i j hi (fun b => hlt (x * (b : ZMod N))) (fun b => hlt (y * (b : ZMod N)))
    hredθ hredφ).2
  rw [hJ, Finset.prod_filter]
  change (nonZeroDivisors (Ideal (𝓞 E))).subtype (∏ b : (ZMod N)ˣ,
    (cyclotomicInverseConjugateIdeal N E b I) ^
      zmodCarry (x * (b : ZMod N)) (y * (b : ZMod N))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro b _
  rw [map_pow, zmodCarry_eq_ite, hP]
  have hb : p - 1 ≤ i b + j b ↔ N ≤ (x * (b : ZMod N)).val + (y * (b : ZMod N)).val := by
    dsimp only [i, j]
    rw [hd, Nat.mul_comm N d, ← Nat.mul_add, Nat.mul_le_mul_left_iff hd₀]
  simp only [hb]
  split_ifs <;> simp

/-- Products with floor exponents are products of binary carry ideals. -/
theorem cyclotomicFloorProduct_eq_prod_carry
    (a : ℕ) (u : ZMod N) (I : (Ideal (𝓞 E))⁰) :
    (∏ b : (ZMod N)ˣ, (cyclotomicInverseConjugateIdeal N E b I) ^
        (a * (u * (b : ZMod N)).val / N)) =
      ∏ j ∈ Finset.range a, cyclotomicCarryIdealProduct N E ((j : ZMod N) * u) u I := by
  let B (b : (ZMod N)ˣ) :=
    cyclotomicInverseConjugateIdeal N E b I
  change (∏ b : (ZMod N)ˣ, B b ^ (a * (u * (b : ZMod N)).val / N)) = _
  calc
    _ = ∏ b : (ZMod N)ˣ, ∏ j ∈ Finset.range a,
        B b ^ zmodCarry (((j : ZMod N) * u) * (b : ZMod N)) (u * (b : ZMod N)) := by
      apply Finset.prod_congr rfl
      intro b _
      rw [mul_div_eq_sum_zmodCarry, ← Finset.prod_pow_eq_pow_sum]
      simp only [mul_assoc]
    _ = _ := Finset.prod_comm

/-- The smoothing product is a product of the binary carry products. -/
theorem cyclotomicSmoothingQuotientIdealProduct_eq_prod_carry
    (a : ℕ) (ha : a.Coprime N) (I : (Ideal (𝓞 E))⁰) :
    let u : ZMod N := ((ZMod.unitOfCoprime a ha)⁻¹ : (ZMod N)ˣ).val
    cyclotomicSmoothingQuotientIdealProduct N E a ha I =
      ∏ j ∈ Finset.range a, cyclotomicCarryIdealProduct N E ((j : ZMod N) * u) u I :=
  cyclotomicFloorProduct_eq_prod_carry N E a ((ZMod.unitOfCoprime a ha)⁻¹ : (ZMod N)ˣ).val I

/-- The product of the conjugates with least-residue exponents, as in the
Gauss-sum ideal formula. -/
noncomputable def cyclotomicResidueIdealProduct (I : (Ideal (𝓞 E))⁰) : (Ideal (𝓞 E))⁰ :=
  ∏ b : (ZMod N)ˣ, (cyclotomicInverseConjugateIdeal N E b I) ^ (b : ZMod N).val

/-- For the project's smoothing parameter `2 * N + 1`, the smoothing product
is the square of the product with least-residue exponents. -/
theorem cyclotomicSmoothingQuotientIdealProduct_two_mul_add_one (I : (Ideal (𝓞 E))⁰) :
    cyclotomicSmoothingQuotientIdealProduct N E (2 * N + 1) (by simp) I =
      cyclotomicResidueIdealProduct N E I ^ 2 := by
  unfold cyclotomicSmoothingQuotientIdealProduct cyclotomicResidueIdealProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro b _
  have hb : inverseSmoothingResidue (2 * N + 1) (by simp) b = (b : ZMod N).val := by
    rw [inverseSmoothingResidue, zmodUnitOfCoprime_two_mul_add_one_eq_one, inv_one, one_mul]
  let w := (b : ZMod N).val
  have hdiv : (2 * N + 1) * w / N = w * 2 := by
    rw [show (2 * N + 1) * w = w + N * (w * 2) by ring,
      Nat.add_mul_div_left _ _ (NeZero.pos N), Nat.div_eq_of_lt (ZMod.val_lt (b : ZMod N)), zero_add]
  rw [hb, hdiv, pow_mul]

/-- The constant correction in the smoothed weight-one formula contributes
the norm element, whose class-group action is zero. -/
theorem cyclotomicWeightOneClassAction_eq_sum_smoothingQuotient (a : ℕ) (ha : a.Coprime N)
    (c : Additive (ClassGroup (𝓞 E))) :
    (ρ).asAlgebraHom (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha) c =
      ∑ b : (ZMod N)ˣ, ((a * inverseSmoothingResidue a ha b / N : ℕ) : ℤ) • ρ (χ b)⁻¹ c := by
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {N} ℚ E
  let _ : Fintype Gal(E/ℚ) := Fintype.ofFinite _
  have hnorm : (∑ b : (ZMod N)ˣ, ρ (χ b)⁻¹ c) = 0 := by
    let e : (ZMod N)ˣ ≃ Gal(E/ℚ) := (χ).toEquiv.trans (Equiv.inv _)
    exact (Equiv.sum_comp e fun σ => ρ σ c).trans (sum_numberFieldClassGroupGaloisAction_eq_zero c)
  rw [twistedWeightOneStickelberger, map_sum, LinearMap.sum_apply]
  simp only [pow_zero, mul_one, Representation.asAlgebraHom_single, LinearMap.smul_apply,
    MulEquiv.coe_toMonoidHom, smoothedWeightOneCoefficient, sub_smul, LinearMap.sub_apply,
    Finset.sum_sub_distrib,
    ← Finset.smul_sum, hnorm, smul_zero, sub_zero]

theorem cyclotomicWeightOneClassAction_apply_mk0 (a : ℕ) (ha : a.Coprime N) (I : (Ideal (𝓞 E))⁰) :
    (ρ).asAlgebraHom (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha)
        (Additive.ofMul (ClassGroup.mk0 I)) =
      Additive.ofMul (ClassGroup.mk0 (cyclotomicSmoothingQuotientIdealProduct N E a ha I)) := by
  rw [cyclotomicWeightOneClassAction_eq_sum_smoothingQuotient N E]
  let B (b : (ZMod N)ˣ) := (cyclotomicInverseConjugateIdeal N E b I) ^
      (a * inverseSmoothingResidue a ha b / N)
  have hterm (b : (ZMod N)ˣ) :
      ((a * inverseSmoothingResidue a ha b / N : ℕ) : ℤ) • ρ (χ b)⁻¹
          (Additive.ofMul (ClassGroup.mk0 I)) = Additive.ofMul (ClassGroup.mk0 (B b)) := by
    rw [numberFieldClassGroupGaloisAction_apply_mk0, ← ofMul_zpow, zpow_natCast]
    exact congrArg Additive.ofMul (map_pow _ _ _).symm
  rw [Finset.sum_congr rfl (fun b _ => hterm b), ← ofMul_prod, ← map_prod]
  rfl

/-- The weight-one annihilation is equivalent to principality of the
smoothing products on prime ideals. -/
theorem cyclotomicWeightOneClassAction_eq_zero_iff_primeProducts_principal
    (a : ℕ) (ha : a.Coprime N) :
    (∀ c : Additive (ClassGroup (𝓞 E)),
      (ρ).asAlgebraHom (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha) c = 0) ↔
      ∀ v : HeightOneSpectrum (𝓞 E),
        (cyclotomicSmoothingQuotientIdealProduct N E a ha
          ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩).val.IsPrincipal := by
  let T := (ρ).asAlgebraHom (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha)
  let f : ClassGroup (𝓞 E) →* ClassGroup (𝓞 E) := MonoidHom.toAdditive.symm T.toAddMonoidHom
  have hmk (I : (Ideal (𝓞 E))⁰) :
      f (ClassGroup.mk0 I) = ClassGroup.mk0 (cyclotomicSmoothingQuotientIdealProduct N E a ha I) :=
    congrArg Additive.toMul (cyclotomicWeightOneClassAction_apply_mk0 N E a ha I)
  constructor
  · intro h v
    let I : (Ideal (𝓞 E))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
    apply (ClassGroup.mk0_eq_one_iff (cyclotomicSmoothingQuotientIdealProduct N E a ha I).property).mp
    exact (hmk I).symm.trans (congrArg Additive.toMul (h (Additive.ofMul (ClassGroup.mk0 I))))
  · intro h c
    have hf : f = 1 := by
      apply classGroupHom_ext_on_primeClasses
      intro v
      let I : (Ideal (𝓞 E))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
      exact (hmk I).trans ((ClassGroup.mk0_eq_one_iff
        (cyclotomicSmoothingQuotientIdealProduct N E a ha I).property).mpr (h v))
    exact congrArg Additive.ofMul (DFunLike.congr_fun hf c.toMul)

/-- The Jacobi-sum principal-ideal identities on prime ideals imply the
weight-one Stickelberger annihilation. -/
theorem cyclotomicWeightOneClassAction_eq_zero_of_carryProducts_principal
    (a : ℕ) (ha : a.Coprime N)
    (h : ∀ (v : HeightOneSpectrum (𝓞 E)) (x y : ZMod N),
      (cyclotomicCarryIdealProduct N E x y
        ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩).val.IsPrincipal) :
    ∀ c : Additive (ClassGroup (𝓞 E)),
      (ρ).asAlgebraHom (twistedWeightOneStickelberger (χ).toMonoidHom 0 a ha) c = 0 := by
  apply (cyclotomicWeightOneClassAction_eq_zero_iff_primeProducts_principal N E a ha).mpr
  intro v
  let I : (Ideal (𝓞 E))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  let J := cyclotomicSmoothingQuotientIdealProduct N E a ha I
  apply (ClassGroup.mk0_eq_one_iff J.property).mp
  change ClassGroup.mk0 (cyclotomicSmoothingQuotientIdealProduct N E a ha I) = 1
  rw [cyclotomicSmoothingQuotientIdealProduct_eq_prod_carry, map_prod]
  apply Finset.prod_eq_one
  intro j _
  exact (ClassGroup.mk0_eq_one_iff _).mpr (h v _ _)

/-- For smoothing at `2 * N + 1`, the Gauss-sum ideal identities alone
suffice for weight-one annihilation. -/
theorem cyclotomicWeightOneClassAction_eq_zero_of_residueProducts_principal
    (h : ∀ v : HeightOneSpectrum (𝓞 E),
      (cyclotomicResidueIdealProduct N E
        ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩).val.IsPrincipal) :
    ∀ c : Additive (ClassGroup (𝓞 E)),
      (ρ).asAlgebraHom (twistedWeightOneStickelberger (χ).toMonoidHom 0 (2 * N + 1) (by simp)) c = 0 := by
  apply (cyclotomicWeightOneClassAction_eq_zero_iff_primeProducts_principal N E (2 * N + 1)
    (by simp)).mpr
  intro v
  let I : (Ideal (𝓞 E))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  let J := cyclotomicSmoothingQuotientIdealProduct N E (2 * N + 1) (by simp) I
  apply (ClassGroup.mk0_eq_one_iff J.property).mp
  change ClassGroup.mk0 (cyclotomicSmoothingQuotientIdealProduct N E (2 * N + 1) (by simp) I) = 1
  rw [cyclotomicSmoothingQuotientIdealProduct_two_mul_add_one, map_pow,
    (ClassGroup.mk0_eq_one_iff (cyclotomicResidueIdealProduct N E I).property).mpr (h v), one_pow]

end Utilities
