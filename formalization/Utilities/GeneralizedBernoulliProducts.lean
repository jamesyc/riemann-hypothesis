module

public import Utilities.GeneralizedBernoulli
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

open scoped BigOperators

namespace Utilities

/-- The Dirichlet characters whose unit-group kernels belong to a specified set. -/
def dirichletCharactersWithKernelIn (R : Type*) [CommRing R] {N : ℕ}
    (P : Set (Subgroup (ZMod N)ˣ)) : Set (DirichletCharacter R N) :=
  {χ | χ.toUnitHom.ker ∈ P}

/-- At most the index of `H` characters can have kernels containing `H`. -/
theorem ncard_dirichletCharactersWithKernelIn_le_index {N : ℕ} [NeZero N]
    (P : Set (Subgroup (ZMod N)ˣ)) (H : Subgroup (ZMod N)ˣ)
    (hP : ∀ K ∈ P, H ≤ K) :
    (dirichletCharactersWithKernelIn ℂ P).ncard ≤ H.index := by
  let : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  let D := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ H).ofDual
  let f (χ : dirichletCharactersWithKernelIn ℂ P) : D := ⟨χ.val, by
    apply MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff.mpr
    intro u hu
    have hm : u ∈ χ.val.toUnitHom.ker := hP _ χ.property hu
    have h := congrArg (fun z : ℂˣ => (z : ℂ)) (MonoidHom.mem_ker.mp hm)
    simpa only [MulChar.coe_toUnitHom, Units.val_one] using h⟩
  calc
    _ = Nat.card (dirichletCharactersWithKernelIn ℂ P) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card D := Nat.card_le_card_of_injective f (fun _ _ h => Subtype.ext (congrArg (fun x : D => x.val) h))
    _ = H.index := MulChar.card_subgroupOrderIsoSubgroupMulChar

theorem dirichletCharacter_ker_ringHomComp {R S : Type*} [CommRing R] [CommRing S]
    {N : ℕ} (f : R →+* S) (hf : Function.Injective f) (χ : DirichletCharacter R N) :
    (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one,
    MulChar.ringHomComp_apply, ← map_one f, hf.eq_iff]

theorem dirichletCharacter_ringHomComp_bijOn {K L : Type*} [Field K] [Field L]
    {N : ℕ} [NeZero N] [HasEnoughRootsOfUnity K (Monoid.exponent (ZMod N)ˣ)]
    (f : K →+* L) (P : Set (Subgroup (ZMod N)ˣ)) :
    Set.BijOn (fun χ : DirichletCharacter K N => (χ.ringHomComp f : DirichletCharacter L N))
      (dirichletCharactersWithKernelIn K P) (dirichletCharactersWithKernelIn L P) := by
  have hker := dirichletCharacter_ker_ringHomComp f f.injective (N := N)
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    simpa only [dirichletCharactersWithKernelIn, Set.mem_ofPred_eq, hker] using hχ
  · intro χ _ ψ _ hp
    ext u
    apply f.injective
    simpa only [MulChar.ringHomComp_apply] using congrArg (fun φ : DirichletCharacter L N => φ u) hp
  · intro χ hχ
    let m := Monoid.exponent (ZMod N)ˣ
    let : NeZero m := ⟨Monoid.exponent_ne_zero_of_finite⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K m
    have hne : (primitiveRoots m K).Nonempty := ⟨ζ, (mem_primitiveRoots (NeZero.pos _)).mpr hζ⟩
    have hmem (u : (ZMod N)ˣ) : χ.toUnitHom u ∈ rootsOfUnity m L := by
      rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
    let e := rootsOfUnityEquivOfPrimitiveRoots f.injective hne
    let ψ := MulChar.ofUnitHom <| (rootsOfUnity m K).subtype.comp
      (e.symm.toMonoidHom.comp (χ.toUnitHom.codRestrict _ hmem))
    have hψ : ψ.ringHomComp f = χ := by
      ext u
      dsimp only [ψ]
      rw [MulChar.ringHomComp_apply, MulChar.ofUnitHom_coe]
      change f ((e.symm ⟨χ.toUnitHom u, hmem u⟩ : Kˣ) : K) = χ u
      dsimp only [e]
      rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply]
      simp
    refine ⟨ψ, ?_, hψ⟩
    change ψ.toUnitHom.ker ∈ P
    rw [← hker ψ, hψ]
    exact hχ

theorem dirichletCharacter_conductor_ringHomComp {R S : Type*} [CommRing R] [CommRing S]
    {N : ℕ} [NeZero N] (f : R →+* S) (hf : Function.Injective f)
    (χ : DirichletCharacter R N) :
    DirichletCharacter.conductor (χ.ringHomComp f : DirichletCharacter S N) = χ.conductor := by
  have hker := dirichletCharacter_ker_ringHomComp f hf χ
  have hset : DirichletCharacter.conductorSet (χ.ringHomComp f : DirichletCharacter S N) = χ.conductorSet := by
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    constructor
    · intro hd
      apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd.dvd).mpr
      rw [← hker]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd.dvd).mp hd
    · intro hd
      apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd.dvd).mpr
      rw [hker]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd.dvd).mp hd
  unfold DirichletCharacter.conductor
  rw [hset]

private theorem dirichletCharacter_changeLevel_eq_of_ringHomComp
    {R S : Type*} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S)
    {d e : ℕ} (hde : e = d) (hd : d ∣ N) (he : e ∣ N)
    (φ : DirichletCharacter R d) (ψ : DirichletCharacter S e)
    (h : DirichletCharacter.changeLevel he ψ = (DirichletCharacter.changeLevel hd φ).ringHomComp f)
    (a : ℕ) : ψ (a : ZMod e) = f (φ (a : ZMod d)) := by
  subst e
  have hc : (DirichletCharacter.changeLevel hd φ).ringHomComp f =
      DirichletCharacter.changeLevel hd (φ.ringHomComp f) := by
    ext u
    simp [MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hψ := DirichletCharacter.changeLevel_injective hd (h.trans hc)
  rw [hψ, MulChar.ringHomComp_apply]

theorem map_primitiveBernoulliValue {R S : Type*} [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra ℚ S] {N : ℕ} [NeZero N] (f : R →+* S) (hf : Function.Injective f)
    (k : ℕ) (χ : DirichletCharacter R N) :
    f (primitiveBernoulliValue k χ) = primitiveBernoulliValue k (χ.ringHomComp f) := by
  let ψ : DirichletCharacter S N := χ.ringHomComp f
  have hc : ψ.conductor = χ.conductor := dirichletCharacter_conductor_ringHomComp f hf χ
  have hprim (a : ℕ) : ψ.primitiveCharacter (a : ZMod ψ.conductor) =
      f (χ.primitiveCharacter (a : ZMod χ.conductor)) :=
    dirichletCharacter_changeLevel_eq_of_ringHomComp f hc χ.conductor_dvd_level ψ.conductor_dvd_level
      χ.primitiveCharacter ψ.primitiveCharacter (by rw [DirichletCharacter.changeLevel_primitiveCharacter,
        DirichletCharacter.changeLevel_primitiveCharacter]) a
  simp only [primitiveBernoulliValue, generalizedBernoulliValue, map_sum]
  refine Finset.sum_congr (congrArg (Finset.Icc 1) hc.symm) ?_
  intro a _
  rw [map_mul, RingHom.map_rat_algebraMap]
  exact congrArg₂ (· * ·) (hprim a).symm
    (congrArg (fun m => algebraMap ℚ S (generalizedBernoulliCoefficient m k a)) hc.symm)

/-- The normalized Bernoulli value lies in the subring containing the
character values, even if that subring is only a ring of integers. -/
theorem normalized_primitiveBernoulliValue_ringHomComp_mem_subring
    {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N]
    (A : Subring R) (k : ℕ) (χ : DirichletCharacter A N) :
    (generalizedBernoulliDenominator N k : R) *
      primitiveBernoulliValue k (χ.ringHomComp A.subtype) ∈ A := by
  let ψ : DirichletCharacter R N := χ.ringHomComp A.subtype
  have hc : ψ.conductor = χ.conductor :=
    dirichletCharacter_conductor_ringHomComp A.subtype Subtype.val_injective χ
  have hprim (a : ℕ) : ψ.primitiveCharacter (a : ZMod ψ.conductor) =
      A.subtype (χ.primitiveCharacter (a : ZMod χ.conductor)) :=
    dirichletCharacter_changeLevel_eq_of_ringHomComp A.subtype hc χ.conductor_dvd_level
      ψ.conductor_dvd_level χ.primitiveCharacter ψ.primitiveCharacter (by
        rw [DirichletCharacter.changeLevel_primitiveCharacter,
          DirichletCharacter.changeLevel_primitiveCharacter]) a
  have hmem (a : ZMod ψ.conductor) : ψ.primitiveCharacter a ∈ A := by
    let : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
    rw [← ZMod.natCast_zmod_val a, hprim]
    exact Subtype.property _
  have hscaled := denominator_mul_generalizedBernoulliValue_mem_subring k
    (ψ.primitiveCharacter : ZMod ψ.conductor → R) A
    (Nat.pos_of_ne_zero ψ.conductor_ne_zero) hmem
  obtain ⟨u, hu⟩ := ψ.conductor_dvd_level
  have hden : generalizedBernoulliDenominator N k =
      u * generalizedBernoulliDenominator ψ.conductor k := by
    unfold generalizedBernoulliDenominator
    rw [← mul_assoc, mul_comm u ψ.conductor, ← hu]
  change (generalizedBernoulliDenominator N k : R) * primitiveBernoulliValue k ψ ∈ A
  rw [hden, Nat.cast_mul, mul_assoc, primitiveBernoulliValue]
  exact A.mul_mem (natCast_mem A u) hscaled

/-- A character product compatible with field embeddings has a single rational
value in every characteristic-zero field splitting the source group. -/
theorem exists_rat_dirichletCharacter_product {N : ℕ} [NeZero N]
    (P : Set (Subgroup (ZMod N)ˣ))
    (F : ∀ (K : Type) [Field K] [CharZero K], DirichletCharacter K N → K)
    (hF : ∀ (K L : Type) [Field K] [CharZero K] [Field L] [CharZero L]
      (f : K →+* L) (χ : DirichletCharacter K N), f (F K χ) = F L (χ.ringHomComp f)) :
    ∃ a : ℚ, ∀ (K : Type) [Field K] [CharZero K]
      [HasEnoughRootsOfUnity K (Monoid.exponent (ZMod N)ˣ)],
      ∏ᶠ χ ∈ dirichletCharactersWithKernelIn K P, F K χ = (a : K) := by
  let n := Monoid.exponent (ZMod N)ˣ
  let : NeZero n := ⟨Monoid.exponent_ne_zero_of_finite⟩
  let : NeZero (n : ℚ) := ⟨by exact_mod_cast (NeZero.ne n)⟩
  let L := CyclotomicField n ℚ
  let : IsCyclotomicExtension {n} ℚ L := CyclotomicField.isCyclotomicExtension n ℚ
  let : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  let : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {n} ℚ L
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ L) n :=
    IsCyclotomicExtension.zeta_spec n ℚ L
  let : HasEnoughRootsOfUnity L n := ⟨⟨_, hζ⟩, rootsOfUnity.isCyclic L n⟩
  have hfin (K : Type) [Field K] : (dirichletCharactersWithKernelIn K P).Finite := Set.toFinite _
  let prodL := ∏ᶠ χ ∈ dirichletCharactersWithKernelIn L P, F L χ
  have hfixed (σ : L ≃ₐ[ℚ] L) : σ prodL = prodL := by
    exact ((σ.toRingHom.toMonoidHom).map_finprod_mem (fun χ => F L χ) (hfin L)).trans
      (finprod_mem_eq_of_bijOn _ (dirichletCharacter_ringHomComp_bijOn σ.toRingHom P)
        (fun χ _ => hF _ _ σ.toRingHom χ))
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hfixed)
  refine ⟨a, fun K _ _ _ => ?_⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  have hmin : Polynomial.aeval ω (minpoly ℚ (hζ.powerBasis ℚ).gen) = 0 := by
    rw [IsPrimitiveRoot.powerBasis_gen, ← hζ.minpoly_eq_cyclotomic_of_irreducible
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)), Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hω.isRoot_cyclotomic (NeZero.pos n)
  let g := (hζ.powerBasis ℚ).lift ω hmin
  calc
    _ = ∏ᶠ χ ∈ dirichletCharactersWithKernelIn L P, g.toRingHom (F L χ) :=
      (finprod_mem_eq_of_bijOn _ (dirichletCharacter_ringHomComp_bijOn g.toRingHom P)
        (fun χ _ => hF _ _ g.toRingHom χ)).symm
    _ = g.toRingHom prodL := (g.toRingHom.toMonoidHom.map_finprod_mem _ (hfin L)).symm
    _ = (a : K) := by rw [← ha]; exact (g.commutes a).trans (eq_ratCast _ a)

/-- Under the parity condition, the normalized primitive Bernoulli factors
have a common nonzero integer product in every splitting coefficient field. -/
theorem exists_int_normalized_primitiveBernoulliProduct {N k : ℕ} [NeZero N] (hk : 2 ≤ k)
    (P : Set (Subgroup (ZMod N)ˣ))
    (hP : ∀ K ∈ P, ((-1 : (ZMod N)ˣ) ∈ K ↔ Even k)) :
    ∃ M : ℤ, M ≠ 0 ∧
      Real.log |(M : ℝ)| ≤ (dirichletCharactersWithKernelIn ℂ P).ncard *
        Real.log (generalizedBernoulliHeightBound N k) ∧
      ∀ (K : Type) [Field K] [CharZero K]
        [HasEnoughRootsOfUnity K (Monoid.exponent (ZMod N)ˣ)],
        ∏ᶠ χ ∈ dirichletCharactersWithKernelIn K P,
          (generalizedBernoulliDenominator N k : K) * primitiveBernoulliValue k χ = (M : K) := by
  obtain ⟨q, hq⟩ := exists_rat_dirichletCharacter_product P
    (fun K _ _ χ => (generalizedBernoulliDenominator N k : K) * primitiveBernoulliValue k χ)
    (fun _ _ _ _ _ _ f χ => by
      rw [map_mul, map_natCast, map_primitiveBernoulliValue f f.injective])
  let S := dirichletCharactersWithKernelIn ℂ P
  have hS : S.Finite := Set.toFinite _
  let : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hC := hq ℂ
  rw [finprod_mem_eq_finite_toFinset_prod _ hS] at hC
  have hint : IsIntegral ℤ (q : ℂ) := by
    rw [← hC]
    exact IsIntegral.prod _ (fun χ _ => isIntegral_normalized_primitiveBernoulliValue χ)
  obtain ⟨M, hM⟩ := hint.mem_range_ratCast_iff.mp ⟨q, rfl⟩
  have hMrat : (M : ℚ) = q := by exact_mod_cast hM
  subst q
  push_cast at hC
  have hparity (χ : DirichletCharacter ℂ N) (hχ : χ ∈ S) : χ (-1) = (-1) ^ k := by
    have hiff : ((-1 : (ZMod N)ˣ) ∈ χ.toUnitHom.ker) ↔ χ (-1) = 1 := by
      simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, Units.coe_neg_one]
    have hh : χ (-1) = 1 ↔ Even k := hiff.symm.trans (hP _ hχ)
    rcases Nat.even_or_odd k with he | ho
    · exact (hh.mpr he).trans he.neg_one_pow.symm
    · exact (χ.even_or_odd.resolve_left (fun h => (Nat.not_even_iff_odd.mpr ho) (hh.mp h))).trans ho.neg_one_pow.symm
  have hM₀ : M ≠ 0 := by
    have hcast : (M : ℂ) ≠ 0 := by
      rw [← hC]
      apply Finset.prod_ne_zero_iff.mpr
      intro χ hχ
      apply mul_ne_zero
      · exact Nat.cast_ne_zero.mpr ((Nat.mul_pos (NeZero.pos N) (primorial_pos _)).ne')
      · exact primitiveBernoulliValue_ne_zero hk χ (hparity χ (hS.mem_toFinset.mp hχ))
    exact_mod_cast hcast
  refine ⟨M, hM₀, ?_, fun K _ _ _ => ?_⟩
  · have habs : |(M : ℝ)| = ‖(M : ℂ)‖ := by simp
    have hbound := norm_prod_normalized_primitiveBernoulliValue_le hk hS.toFinset
    rw [hC, ← habs, ← Set.ncard_eq_toFinset_card _ hS] at hbound
    rw [← Real.log_pow]
    exact Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hM₀)) hbound
  · simpa only [Rat.cast_intCast] using hq K

/-- The normalized Bernoulli value is nonzero at the matching parity over
any characteristic-zero splitting field. -/
theorem normalized_primitiveBernoulliValue_ne_zero
    {K : Type} [Field K] [CharZero K] {N k : ℕ} [NeZero N]
    [HasEnoughRootsOfUnity K (Monoid.exponent (ZMod N)ˣ)]
    (hk : 2 ≤ k) (χ : DirichletCharacter K N) (hχ : χ (-1) = (-1) ^ k) :
    (generalizedBernoulliDenominator N k : K) * primitiveBernoulliValue k χ ≠ 0 := by
  let P : Set (Subgroup (ZMod N)ˣ) := {χ.toUnitHom.ker}
  have hP : ∀ H ∈ P, ((-1 : (ZMod N)ˣ) ∈ H ↔ Even k) := by
    intro H hH
    have hEq : H = χ.toUnitHom.ker := Set.mem_singleton_iff.mp hH
    rw [hEq]
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one,
      Units.coe_neg_one, hχ, neg_one_pow_eq_one_iff_even (by norm_num : (-1 : K) ≠ 1)]
  obtain ⟨m, hm, _, hprod⟩ := exists_int_normalized_primitiveBernoulliProduct hk P hP
  let S := dirichletCharactersWithKernelIn K P
  have hS : S.Finite := Set.toFinite _
  have h := hprod K
  rw [finprod_mem_eq_finite_toFinset_prod _ hS] at h
  have hn : (∏ θ ∈ hS.toFinset, (generalizedBernoulliDenominator N k : K) *
      primitiveBernoulliValue k θ) ≠ 0 := h.symm ▸ Int.cast_ne_zero.mpr hm
  exact Finset.prod_ne_zero_iff.mp hn χ (hS.mem_toFinset.mpr (Set.mem_singleton _))

end Utilities
