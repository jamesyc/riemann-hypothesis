module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Quotient.Card

@[expose] public section

namespace Utilities

private theorem card_eq_card_residueField_mul_of_covBy
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (h : P ⋖ Q) :
    Nat.card Q = Nat.card P * Nat.card (IsLocalRing.ResidueField R) := by
  let f := Submodule.inclusion h.le
  let U := f.range
  have hsimple : IsSimpleModule R (Q ⧸ U) := by
    exact (Submodule.quotEquivOfEq U _ (Submodule.range_inclusion P Q h.le)).isSimpleModule_iff.mpr
      ((covBy_iff_quot_is_simple h.le).mp h)
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  obtain rfl := IsLocalRing.eq_maximalIdeal hm
  have hf : Function.Injective f := Submodule.inclusion_injective _
  rw [Submodule.card_eq_card_quotient_mul_card U,
    ← Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv, Nat.card_congr e.toEquiv]
  rfl

/-- Over a local ring, the cardinality of a finite-length module is the
residue-field cardinality raised to its composition length. -/
theorem card_eq_card_residueField_pow_of_isFiniteLength (R M : Type*)
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) :
    Nat.card M = Nat.card (IsLocalRing.ResidueField R) ^ (Module.length R M).toNat := by
  obtain ⟨s, hbot, htop⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
  rw [← Module.length_compositionSeries s hbot htop, ENat.toNat_natCast]
  suffices hall : ∀ i : Fin (s.length + 1),
      Nat.card (s i) = Nat.card (IsLocalRing.ResidueField R) ^ (i : ℕ) by
    rw [← Fin.val_last s.length, ← hall, ← RelSeries.last, htop]
    exact (Nat.card_congr (Submodule.topEquiv (R := R) (M := M)).toEquiv).symm
  intro i
  induction i using Fin.induction with
  | zero =>
    rw [← RelSeries.head, hbot]
    simp
  | succ i hi =>
    rw [card_eq_card_residueField_mul_of_covBy (s.step i), hi, Fin.val_succ, Fin.val_castSucc, pow_succ]

theorem card_eq_padic_prime_pow_of_isFiniteLength (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*)
    [AddCommGroup M] [Module ℤ_[ℓ] M] (h : IsFiniteLength ℤ_[ℓ] M) :
    Nat.card M = ℓ ^ (Module.length ℤ_[ℓ] M).toNat := by
  rw [card_eq_card_residueField_pow_of_isFiniteLength ℤ_[ℓ] M h,
    Nat.card_congr PadicInt.residueField.toEquiv, Nat.card_zmod]

/-- Finite length and finite cardinality coincide for modules over ℓ-adic integers. -/
theorem padicModule_isFiniteLength_iff_finite (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*)
    [AddCommGroup M] [Module ℤ_[ℓ] M] :
    IsFiniteLength ℤ_[ℓ] M ↔ Finite M := by
  constructor
  · intro h
    apply Nat.finite_of_card_ne_zero
    rw [card_eq_padic_prime_pow_of_isFiniteLength ℓ M h]
    exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  · intro h
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨inferInstance, isArtinian_of_finite⟩

/-- A finite module over the ℓ-adic integers has cardinality a power of ℓ. -/
theorem exists_card_eq_padic_prime_pow (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*)
    [AddCommGroup M] [Module ℤ_[ℓ] M] [Finite M] :
    ∃ n : ℕ, Nat.card M = ℓ ^ n :=
  ⟨_, card_eq_padic_prime_pow_of_isFiniteLength ℓ M
    ((padicModule_isFiniteLength_iff_finite ℓ M).mpr inferInstance)⟩

end Utilities
