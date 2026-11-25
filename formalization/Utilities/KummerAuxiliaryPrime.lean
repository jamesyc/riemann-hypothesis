module

public import Utilities.FrobeniusRealization
public import Utilities.KummerFrobenius
public import Utilities.KummerCyclotomicExclusion
public import Utilities.PrimePowerFrobenius
public import Utilities.SubgroupAvoidance
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open NumberField
open scoped NumberField Pointwise

namespace Utilities

/-- Finite Frobenius realization turns three subgroup exclusions and
the Kummer and cyclotomic restrictions into an auxiliary rational prime. -/
theorem exists_kummerAuxiliaryPrime
    (hreal : HasFiniteRationalFrobeniusRealization)
    {L : Type} [Field L] [Algebra ℚ L] [IsGalois ℚ L] [IsAlgClosed L]
    {ℓ n m a : ℕ} (hn : n.Coprime ℓ) (hm : Odd m)
    (H A B C : OpenSubgroup Gal(L/ℚ))
    (hA : ¬ H.toSubgroup ≤ A.toSubgroup) (hB : ¬ H.toSubgroup ≤ B.toSubgroup)
    (hC : ¬ H.toSubgroup ≤ C.toSubgroup) (hpow : ∀ g ∈ H, g ^ m ∈ B)
    {z : L} (hz : z ^ m = (a : L))
    (hfix : ∀ g ∈ H, g z = z)
    (hroots : ∀ g ∈ H, ∀ w : L, w ^ (n * m) = 1 → g w = w)
    (hnext : ∀ g ∉ C, ¬ ∀ w : L, w ^ (n * m * ℓ) = 1 → g w = w)
    {t : ℕ} (ht : t ≠ 0) (hprod : n * m * ℓ * a ≠ 0) :
    ∃ (p : ℕ) (P : Ideal (𝓞 L)) (φ : Gal(L/ℚ)), p.Prime ∧ ¬ p ∣ t ∧ ¬ p ∣ n * m * ℓ * a ∧
      P.IsPrime ∧ (p : 𝓞 L) ∈ P ∧ IsArithFrobAt ℤ φ P ∧
      p ≡ 1 [MOD n * m] ∧ ¬ ℓ ∣ orderOf (a : ZMod p) ∧
      φ ∈ H ∧ φ ∉ A ∧ φ ∉ B ∧ φ ∉ C := by
  let U : Set Gal(L/ℚ) := H ∩ (A : Set Gal(L/ℚ))ᶜ ∩ (B : Set Gal(L/ℚ))ᶜ ∩ (C : Set Gal(L/ℚ))ᶜ
  have hU : IsOpen U :=
    ((H.isOpen.inter A.isClosed.isOpen_compl).inter B.isClosed.isOpen_compl).inter C.isClosed.isOpen_compl
  obtain ⟨g, hg, hgA, hgB, hgC⟩ := exists_mem_not_mem_three_subgroups_of_odd_pow
    H.toSubgroup A.toSubgroup B.toSubgroup C.toSubgroup hA hB hC hm hpow
  have hne : U.Nonempty := ⟨g, ⟨⟨⟨hg, hgA⟩, hgB⟩, hgC⟩⟩
  obtain ⟨p, P, φ, hp, hpT, hP, hPmem, hφ, hφH⟩ :=
    exists_rational_isArithFrobAt_in_open hreal U hU hne _ (mul_ne_zero ht hprod)
  obtain ⟨⟨⟨hφH, hφA⟩, hφB⟩, hφC⟩ := hφH
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : P.IsPrime := hP
  let _ : P.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_rationalPrime_of_mem P p hPmem
  have haway : ¬ p ∣ n * m * ℓ * a := fun h => hpT (h.trans (dvd_mul_left _ _))
  obtain ⟨hmod, horder⟩ := kummerAuxiliaryPrime_conditions_of_isArithFrobAt hn P hφ haway
    (hroots φ hφH) (hnext φ hφC) hz (hfix φ hφH)
  exact ⟨p, P, φ, hp, fun h => hpT (h.trans (dvd_mul_right _ _)), haway, hP, hPmem, hφ,
    hmod, horder, hφH, hφA, hφB, hφC⟩

/-- Select an auxiliary prime for the cyclotomic fields and two bounded
tests. The next-layer exclusion follows from the radical and level data. -/
theorem exists_kummerAuxiliaryPrime_of_cyclotomicLayers
    {L : Type} [Field L] [CharZero L] [IsGalois ℚ L] [IsAlgClosed L]
    {ℓ n m a r : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (hn : n.Coprime ℓ) (hm : m = ℓ ^ (r + 1)) (hnm : n * m ≠ 0) (ha : a ≠ 0)
    (E E' : FiniteGaloisIntermediateField ℚ L) [IsCyclotomicExtension {n * m} ℚ E]
    [IsCyclotomicExtension {n * m * ℓ} ℚ E']
    {β : L} (hβ : β ^ m = (a : L))
    (A B : OpenSubgroup Gal(L/ℚ))
    (hA : ¬ E.toIntermediateField.fixingSubgroup ⊓ MulAction.stabilizer Gal(L/ℚ) β ≤ A.toSubgroup)
    (hB : ¬ E.toIntermediateField.fixingSubgroup ⊓ MulAction.stabilizer Gal(L/ℚ) β ≤ B.toSubgroup)
    (hpow : ∀ g ∈ E.toIntermediateField.fixingSubgroup ⊓ MulAction.stabilizer Gal(L/ℚ) β,
      g ^ m ∈ A ∧ g ^ m ∈ B)
    {t : ℕ} (ht : t ≠ 0) :
    ∃ (p : ℕ) (P : Ideal (𝓞 L)) (φ : Gal(L/ℚ)), p.Prime ∧ ¬ p ∣ t ∧ ¬ p ∣ n * m * ℓ * a ∧
      P.IsPrime ∧ (p : 𝓞 L) ∈ P ∧ IsArithFrobAt ℤ φ P ∧
      p ≡ 1 [MOD n * m] ∧ ¬ ℓ ∣ orderOf (a : ZMod p) ∧
      φ ∈ E.toIntermediateField.fixingSubgroup ∧ φ β = β ∧
      φ ∉ A ∧ φ ∉ B ∧ φ ∉ E'.toIntermediateField.fixingSubgroup := by
  have hOdd : Odd m := hm.symm ▸ (hℓ.odd_of_ne_two hodd).pow
  have hℓm : ℓ ∣ m := hm.symm ▸ dvd_pow_self ℓ (Nat.succ_ne_zero r)
  have hN := mul_ne_zero (mul_ne_zero hnm hℓ.ne_zero) ha
  let _ : NeZero (n * m) := ⟨hnm⟩
  let _ : NeZero (n * m * ℓ) := ⟨mul_ne_zero hnm hℓ.ne_zero⟩
  let H : OpenSubgroup Gal(L/ℚ) :=
    ⟨E.toIntermediateField.fixingSubgroup ⊓ MulAction.stabilizer Gal(L/ℚ) β,
      E.toIntermediateField.fixingSubgroup_isOpen.inter (stabilizer_isOpen_of_isIntegral (K := ℚ) β)⟩
  let C : OpenSubgroup Gal(L/ℚ) := ⟨E'.toIntermediateField.fixingSubgroup, E'.toIntermediateField.fixingSubgroup_isOpen⟩
  have hC : ¬ H.toSubgroup ≤ C.toSubgroup :=
    radical_stabilizer_not_le_next_cyclotomic_fixingSubgroup hℓ hodd hnm
      (hℓm.trans (dvd_mul_left m n)) (dvd_mul_left m n) ha hβ E.toIntermediateField E'.toIntermediateField
  have hfix (g : Gal(L/ℚ)) (hg : g ∈ H) : g β = β := hg.2
  have hroots (g : Gal(L/ℚ)) (hg : g ∈ H) (z : L) (hz : z ^ (n * m) = 1) : g z = z :=
    (IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField g).mp hg.1 z
      (mem_cyclotomicLayer_of_pow_eq_one (n * m) E.toIntermediateField hz)
  have hpow' (g : Gal(L/ℚ)) (hg : g ∈ H) : g ^ (ℓ ^ (r + 1)) ∈ A ∧
      g ^ (ℓ ^ (r + 1)) ∈ B ∧ g ^ (ℓ ^ (r + 1)) ∈ C := by
    rw [← hm]
    obtain ⟨hA', hB'⟩ := hpow g hg
    refine ⟨hA', hB', ?_⟩
    have hgp : g ^ ℓ ∈ C := by
      apply mem_fixingSubgroup_of_fixes_cyclotomicLayer (n * m * ℓ) E'.toIntermediateField
      intro z hz
      exact algEquiv_pow_prime_fixes_next_roots hℓ hnm (hℓm.trans (dvd_mul_left m n)) g (hroots g hg) hz
    obtain ⟨k, hk⟩ := hℓm
    rw [hk, pow_mul]
    exact C.toSubgroup.pow_mem hgp k
  have hex := exists_mem_not_mem_three_subgroups_of_odd_pow H.toSubgroup A.toSubgroup
    B.toSubgroup C.toSubgroup hA hB hC hOdd (fun g hg => (hpow g hg).2)
  obtain ⟨p, P, φ, hp, hpt, hP, hpP, hφ, hH, hφA, hφB, hφC⟩ :=
    exists_rational_isArithFrobAt_off_openSubgroups_primePower hℓ H A B C hex hpow' _ (mul_ne_zero ht hN)
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : P.IsPrime := hP
  let _ : P.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_rationalPrime_of_mem P p hpP
  have hpa : ¬ p ∣ n * m * ℓ * a := fun h => hpt (h.trans (dvd_mul_left _ _))
  obtain ⟨hmod, horder⟩ := kummerAuxiliaryPrime_conditions_of_isArithFrobAt hn P hφ hpa
    (hroots φ hH) (fun hall => hφC (mem_fixingSubgroup_of_fixes_cyclotomicLayer
      (n * m * ℓ) E'.toIntermediateField φ hall)) hβ (hfix φ hH)
  exact ⟨p, P, φ, hp, fun h => hpt (h.trans (dvd_mul_right _ _)), hpa, hP, hpP, hφ, hmod, horder,
    hH.1, hfix φ hH, hφA, hφB, hφC⟩

private def openKernelOfAdditiveCharacter
    {G W : Type*} [Group G] [TopologicalSpace G] [AddGroup W]
    (U : OpenSubgroup G) (f : Additive U →+ W)
    (hf : IsLocallyConstant (fun u : U => f (Additive.ofMul u))) : OpenSubgroup G :=
  ⟨(AddMonoidHom.toMultiplicativeRight f).ker.map U.toSubgroup.subtype,
    U.isOpen.isOpenMap_subtype_val _ (hf.isOpen_fiber 0)⟩

private theorem mem_openKernelOfAdditiveCharacter
    {G W : Type*} [Group G] [TopologicalSpace G] [AddGroup W]
    (U : OpenSubgroup G) (f : Additive U →+ W)
    (hf : IsLocallyConstant (fun u : U => f (Additive.ofMul u))) (u : U) :
    u.val ∈ openKernelOfAdditiveCharacter U f hf ↔ f (Additive.ofMul u) = 0 := by
  constructor
  · rintro ⟨v, hv, he⟩
    have hvu : v = u := Subtype.ext he
    exact hvu ▸ hv
  · intro h
    exact ⟨u, h, rfl⟩

/-- Two locally constant character evaluations killed by a power of the
Tate prime can be made nonzero at one Frobenius once they are nonzero on
the radical stabilizer. -/
theorem exists_kummerAuxiliaryPrime_of_character_evaluations
    {L W X : Type} [Field L] [CharZero L] [IsGalois ℚ L] [IsAlgClosed L] [AddGroup W] [AddGroup X]
    {ℓ n m a r : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (hn : n.Coprime ℓ) (hm : m = ℓ ^ (r + 1)) (hnm : n * m ≠ 0) (ha : a ≠ 0)
    (E E' : FiniteGaloisIntermediateField ℚ L) [IsCyclotomicExtension {n * m} ℚ E]
    [IsCyclotomicExtension {n * m * ℓ} ℚ E']
    {β : L} (hβ : β ^ m = (a : L))
    (f : Additive E.toIntermediateField.fixingSubgroup →+ W)
    (c : Additive E.toIntermediateField.fixingSubgroup →+ X)
    (hf : IsLocallyConstant (fun u : E.toIntermediateField.fixingSubgroup => f (Additive.ofMul u)))
    (hc : IsLocallyConstant (fun u : E.toIntermediateField.fixingSubgroup => c (Additive.ofMul u)))
    (hfv : ∃ u : E.toIntermediateField.fixingSubgroup, u.val β = β ∧ f (Additive.ofMul u) ≠ 0)
    (hcv : ∃ u : E.toIntermediateField.fixingSubgroup, u.val β = β ∧ c (Additive.ofMul u) ≠ 0)
    (hfkill : ∀ u, m • f u = 0) (hckill : ∀ u, m • c u = 0) {t : ℕ} (ht : t ≠ 0) :
    ∃ (p : ℕ) (P : Ideal (𝓞 L)) (u : E.toIntermediateField.fixingSubgroup),
      p.Prime ∧ ¬ p ∣ t ∧ ¬ p ∣ n * m * ℓ * a ∧ P.IsPrime ∧ (p : 𝓞 L) ∈ P ∧
      IsArithFrobAt ℤ u.val P ∧ p ≡ 1 [MOD n * m] ∧ ¬ ℓ ∣ orderOf (a : ZMod p) ∧
      u.val β = β ∧ f (Additive.ofMul u) ≠ 0 ∧ c (Additive.ofMul u) ≠ 0 ∧
      u.val ∉ E'.toIntermediateField.fixingSubgroup := by
  let U : OpenSubgroup Gal(L/ℚ) := ⟨E.toIntermediateField.fixingSubgroup, E.toIntermediateField.fixingSubgroup_isOpen⟩
  let A := openKernelOfAdditiveCharacter U f hf
  let B := openKernelOfAdditiveCharacter U c hc
  let H := E.toIntermediateField.fixingSubgroup ⊓ MulAction.stabilizer Gal(L/ℚ) β
  have hA : ¬ H ≤ A.toSubgroup := by
    obtain ⟨u, hu, hfu⟩ := hfv
    exact fun h => hfu ((mem_openKernelOfAdditiveCharacter U f hf u).mp (h ⟨u.property, hu⟩))
  have hB : ¬ H ≤ B.toSubgroup := by
    obtain ⟨u, hu, hcu⟩ := hcv
    exact fun h => hcu ((mem_openKernelOfAdditiveCharacter U c hc u).mp (h ⟨u.property, hu⟩))
  have hpow (g : Gal(L/ℚ)) (hg : g ∈ H) : g ^ m ∈ A ∧ g ^ m ∈ B := by
    let u : U := ⟨g, hg.1⟩
    exact ⟨(mem_openKernelOfAdditiveCharacter U f hf (u ^ m)).mpr
        ((map_nsmul f m (Additive.ofMul u)).trans (hfkill (Additive.ofMul u))),
      (mem_openKernelOfAdditiveCharacter U c hc (u ^ m)).mpr
        ((map_nsmul c m (Additive.ofMul u)).trans (hckill (Additive.ofMul u)))⟩
  obtain ⟨p, P, g, hp, hpt, hpa, hP, hpP, hφ, hmod, horder, hgE, hβg, hgA, hgB, hgC⟩ :=
    exists_kummerAuxiliaryPrime_of_cyclotomicLayers hℓ hodd hn hm hnm ha E E' hβ A B hA hB hpow ht
  let u : U := ⟨g, hgE⟩
  exact ⟨p, P, u, hp, hpt, hpa, hP, hpP, hφ, hmod, horder, hβg,
    fun h => hgA ((mem_openKernelOfAdditiveCharacter U f hf u).mpr h),
    fun h => hgB ((mem_openKernelOfAdditiveCharacter U c hc u).mpr h), hgC⟩

end Utilities
