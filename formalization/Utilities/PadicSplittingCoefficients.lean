module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

namespace Utilities

open Polynomial IsLocalRing
open scoped NNReal

private theorem isIntegral_iff_norm_padicEmbedding_le_one (ℓ : ℕ) [Fact ℓ.Prime]
    {K : Type*} [Field K] [Algebra ℚ_[ℓ] K] [Algebra ℤ_[ℓ] K] [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] K]
    [Algebra.IsIntegral ℚ_[ℓ] K] (j : K →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ) (x : K) :
    IsIntegral ℤ_[ℓ] x ↔ ‖j x‖ ≤ 1 := by
  have hmonic := minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[ℓ]) x)
  change IsIntegral ℤ_[ℓ] x ↔ spectralValue (minpoly ℚ_[ℓ] (j x)) ≤ 1
  rw [minpoly.algHom_eq j j.injective, spectralValue_le_one_iff hmonic]
  constructor
  · intro hx k
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[ℓ] hx, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro hx
    have hlift : minpoly ℚ_[ℓ] x ∈ Polynomial.lifts (algebraMap ℤ_[ℓ] ℚ_[ℓ]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun k => ⟨⟨_, hx k⟩, rfl⟩
    obtain ⟨P, hP, _, hmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
    exact ⟨P, hmonic, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[ℓ], hP, minpoly.aeval]⟩

/-- A finite cyclotomic layer of the p-adic algebraic closure supplies a
discrete valuation ring containing all roots of the prescribed order. -/
theorem exists_padicSplittingCoefficients (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) [NeZero n] :
    ∃ O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ), IsDiscreteValuationRing O ∧
      Module.Finite ℤ_[ℓ] O ∧ HasEnoughRootsOfUnity O n := by
  let _ : NeZero (n : PadicAlgCl ℓ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl ℓ) n
  let K := IntermediateField.adjoin ℚ_[ℓ] ({ζ} : Set (PadicAlgCl ℓ))
  let _ : FiniteDimensional ℚ_[ℓ] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  let A := integralClosure ℤ_[ℓ] K
  let V := (Valuation.comap K.val.toRingHom (PadicAlgCl.valued ℓ).v).valuationSubring
  have hAV : A.toSubring = V.toSubring := by
    apply SetLike.ext
    intro x
    change IsIntegral ℤ_[ℓ] x ↔ x ∈ V
    rw [isIntegral_iff_norm_padicEmbedding_le_one ℓ K.val]
    change (↑‖K.val x‖₊ : ℝ) ≤ ↑(1 : ℝ≥0) ↔ ‖K.val x‖₊ ≤ 1
    exact NNReal.coe_le_coe.symm
  let _ : IsLocalRing V.toSubring := inferInstanceAs (IsLocalRing V)
  let _ : IsLocalRing A := (RingEquiv.subringCongr hAV).symm.isLocalRing
  have hDed : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain ℤ_[ℓ] ℚ_[ℓ] K A
  let _ : IsDedekindDomain A := hDed
  have hinj : Function.Injective (algebraMap ℤ_[ℓ] A) := by
    intro a b hab
    have h := congrArg (fun z : A => (z : K)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] K] at h
    exact IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ] ((algebraMap ℚ_[ℓ] K).injective h)
  have hnf : ¬ IsField A := fun h =>
    IsDiscreteValuationRing.not_isField ℤ_[ℓ] ((Algebra.IsIntegral.isField_iff_isField hinj).mpr h)
  let _ : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE A hnf).out 1 3).mpr hDed
  let _ : Module.Finite ℤ_[ℓ] A := IsIntegralClosure.finite ℤ_[ℓ] ℚ_[ℓ] K A
  let j : K →ₐ[ℤ_[ℓ]] PadicAlgCl ℓ := K.val.restrictScalars ℤ_[ℓ]
  let O := A.map j
  let E := A.equivMapOfInjective j j.injective
  have hζmem : ζ ∈ O := by
    let x : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self _ _⟩
    exact ⟨x, (isIntegral_algHom_iff j j.injective).mp
      ((hζ.isIntegral (NeZero.pos n)).tower_top : IsIntegral ℤ_[ℓ] (j x)), rfl⟩
  refine ⟨O, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E,
    Module.Finite.equiv E.toLinearEquiv, ⟨⟨⟨ζ, hζmem⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := O.val) hζ Subtype.val_injective

/-- A finite coefficient subalgebra lies in the closed p-adic unit ball. -/
theorem padicSubalgebra_norm_le_one (ℓ : ℕ) [Fact ℓ.Prime]
    (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) [Module.Finite ℤ_[ℓ] O] (a : O) :
    ‖(a : PadicAlgCl ℓ)‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[ℓ] (a : PadicAlgCl ℓ) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[ℓ]) a).map O.val
  exact (isIntegral_iff_norm_padicEmbedding_le_one ℓ (AlgHom.id ℚ_[ℓ] (PadicAlgCl ℓ)) _).mp hi

/-- Units of a finite coefficient subalgebra have p-adic norm one. -/
theorem padicSubalgebra_norm_unit (ℓ : ℕ) [Fact ℓ.Prime]
    (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) [Module.Finite ℤ_[ℓ] O] (u : Oˣ) :
    ‖((u : O) : PadicAlgCl ℓ)‖ = 1 := by
  have h := padicSubalgebra_norm_le_one ℓ O (u : O)
  have hi := padicSubalgebra_norm_le_one ℓ O (↑u⁻¹ : O)
  have he : ‖((u : O) : PadicAlgCl ℓ)‖ * ‖((↑u⁻¹ : O) : PadicAlgCl ℓ)‖ = 1 := by
    rw [← norm_mul]
    change ‖O.val ((u : O) * ↑u⁻¹)‖ = 1
    rw [Units.mul_inv, map_one, norm_one]
  exact le_antisymm h (he ▸ (mul_le_of_le_one_right (norm_nonneg _) hi))

/-- Every coefficient subalgebra of the p-adic algebraic closure contains
a faithful copy of the p-adic integers. -/
theorem padicSubalgebra_algebraMap_injective (ℓ : ℕ) [Fact ℓ.Prime]
    (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) : Function.Injective (algebraMap ℤ_[ℓ] O) := by
  intro a b hab
  have h := congrArg (fun x : O => (x : PadicAlgCl ℓ)) hab
  simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] (PadicAlgCl ℓ)] at h
  exact IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ] ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective h)

/-- In a coefficient DVR the length used in local-ring base change is a
positive integer for the extension of the p-adic maximal ideal. -/
theorem exists_padicBaseChangeLength (ℓ : ℕ) [Fact ℓ.Prime] (O : Type*)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[ℓ] O]
    (hinj : Function.Injective (algebraMap ℤ_[ℓ] O)) [IsLocalHom (algebraMap ℤ_[ℓ] O)] :
    ∃ r : ℕ, 0 < r ∧
      Module.length O (O ⧸ (maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O)) = r := by
  let I := (maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O)
  have hproper : I ≠ ⊤ := (map_maximalIdeal_lt_top (algebraMap ℤ_[ℓ] O)).ne
  have hne : I ≠ ⊥ := by
    have hp : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    dsimp only [I]
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      ne_eq, Ideal.span_singleton_eq_bot]
    exact fun h => hp (hinj (h.trans (map_zero _).symm))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at hr
  refine ⟨r, Nat.pos_of_ne_zero fun h => hproper (by simp [hr, h]), ?_⟩
  change Module.length O (O ⧸ I) = r
  rw [hr, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

end Utilities
