module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Utilities.SelmerKernel
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.ZPow

@[expose] public section

open scoped Pointwise Topology

namespace Utilities

noncomputable abbrev padicIntegerImage (ℓ : ℕ) [Fact ℓ.Prime] : Submodule ℤ_[ℓ] ℚ_[ℓ] :=
  LinearMap.range (Algebra.linearMap ℤ_[ℓ] ℚ_[ℓ])

abbrev PadicTateQuotient (ℓ : ℕ) [Fact ℓ.Prime] := ℚ_[ℓ] ⧸ padicIntegerImage ℓ

/-- Every nonzero p-adic integer acts surjectively on the divisible Tate coefficient. -/
theorem padicTateQuotient_smul_surjective {ℓ : ℕ} [Fact ℓ.Prime] (a : ℤ_[ℓ]) (ha : a ≠ 0) :
    Function.Surjective (fun x : PadicTateQuotient ℓ => a • x) := by
  intro x
  obtain ⟨y, rfl⟩ := (padicIntegerImage ℓ).mkQ_surjective x
  let y' : ℚ_[ℓ] := (a : ℚ_[ℓ])⁻¹ * y
  have hy : a • y' = y := by
    change (a : ℚ_[ℓ]) * ((a : ℚ_[ℓ])⁻¹ * y) = y
    rw [← mul_assoc, mul_inv_cancel₀ (PadicInt.coe_ne_zero.mpr ha), one_mul]
  refine ⟨(padicIntegerImage ℓ).mkQ y', ?_⟩
  change a • (padicIntegerImage ℓ).mkQ y' = (padicIntegerImage ℓ).mkQ y
  rw [← map_smul, hy]

/-- The negative cyclotomic power on automorphisms of the coefficient field. -/
noncomputable def padicTateScalarOnAut (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime]
    (i : ℕ) : (K ≃+* K) →* ℤ_[ℓ] :=
  (Units.coeHom ℤ_[ℓ]).comp ((zpowGroupHom (-(i : ℤ))).comp (cyclotomicCharacter K ℓ))

/-- The Tate scalar on the Galois group of a specified common extension. -/
noncomputable def padicTateScalarIn (F L : Type) [Field F] [Field L] [Algebra F L]
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) : Gal(L/F) →* ℤ_[ℓ] :=
  (padicTateScalarOnAut L ℓ i).comp (MulSemiringAction.toRingAut Gal(L/F) L)

noncomputable def padicTateScalar (F : Type) [Field F] (ℓ : ℕ) [Fact ℓ.Prime]
    (i : ℕ) : Field.absoluteGaloisGroup F →* ℤ_[ℓ] :=
  padicTateScalarIn F (AlgebraicClosure F) ℓ i

theorem padicTateScalarIn_continuous (F L : Type) [Field F] [Field L] [Algebra F L]
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) : Continuous (padicTateScalarIn F L ℓ i) :=
  Units.continuous_val.comp
    ((continuous_zpow (-(i : ℤ))).comp (cyclotomicCharacter.continuous ℓ F L))

/-- A multiplicative scalar determines the action on the Tate quotient. -/
noncomputable def padicTateRepOfScalar {G : Type} [Monoid G] (ℓ : ℕ) [Fact ℓ.Prime]
    (a : G →* ℤ_[ℓ]) : Rep.{0} ℤ_[ℓ] G := by
  letI : DistribMulAction G (PadicTateQuotient ℓ) := DistribMulAction.compHom (PadicTateQuotient ℓ) a
  letI : SMulCommClass G ℤ_[ℓ] (PadicTateQuotient ℓ) := ⟨fun σ r m => by
    change a σ • (r • m) = r • (a σ • m)
    rw [← mul_smul, ← mul_smul, mul_comm]⟩
  exact Rep.ofDistribMulAction ℤ_[ℓ] G (PadicTateQuotient ℓ)

/-- The algebraic action on ℚℓ/ℤℓ through the negative cyclotomic twist. -/
noncomputable def padicTateTwistRep (F : Type) [Field F] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    Rep.{0} ℤ_[ℓ] (Field.absoluteGaloisGroup F) :=
  padicTateRepOfScalar ℓ (padicTateScalar F ℓ i)

theorem locallyConstant_padicTateSmul {G : Type} [TopologicalSpace G] (ℓ : ℕ) [Fact ℓ.Prime]
    (r : G → ℤ_[ℓ]) (hr : Continuous r) (a : PadicTateQuotient ℓ) :
    IsLocallyConstant fun g => r g • a := by
  obtain ⟨b, rfl⟩ := (padicIntegerImage ℓ).mkQ_surjective a
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  let f (σ : G) : ℚ_[ℓ] := r σ • b
  have hscalar : Continuous (fun σ => (r σ : ℚ_[ℓ])) := continuous_subtype_val.comp hr
  have hcont : Continuous f := by
    simpa only [f, Algebra.smul_def, PadicInt.algebraMap_apply] using hscalar.mul_const b
  have hopen : IsOpen {σ : G | ‖f σ - f g‖ < 1} :=
    isOpen_lt (hcont.sub continuous_const).norm continuous_const
  have hmem : g ∈ {σ : G | ‖f σ - f g‖ < 1} := by simp
  filter_upwards [hopen.mem_nhds hmem] with σ hσ
  rw [← map_smul, ← map_smul]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero (padicIntegerImage ℓ)).mpr
  have hnorm : ‖f σ - f g‖ < 1 := hσ
  exact ⟨⟨f σ - f g, hnorm.le⟩, rfl⟩

theorem padicTateTwist_discreteOrbit (F : Type) [Field F] (ℓ : ℕ) [Fact ℓ.Prime]
    (i : ℕ) (a : padicTateTwistRep F ℓ i) :
    IsLocallyConstant fun σ : Field.absoluteGaloisGroup F => (padicTateTwistRep F ℓ i).ρ σ a :=
  locallyConstant_padicTateSmul ℓ (padicTateScalar F ℓ i)
    (padicTateScalarIn_continuous F (AlgebraicClosure F) ℓ i) a

/-- The Tate representation on a specified common extension, for comparing
Selmer conditions across a tower on the same closure. -/
noncomputable def padicTateTwistIn (F L : Type) [Field F] [Field L] [Algebra F L]
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) : DiscreteGaloisModule ℤ_[ℓ] Gal(L/F) where
  rep := padicTateRepOfScalar ℓ (padicTateScalarIn F L ℓ i)
  discreteOrbit := locallyConstant_padicTateSmul ℓ _ (padicTateScalarIn_continuous F L ℓ i)

theorem padicTateTwistIn_ρ_apply (F L : Type) [Field F] [Field L] [Algebra F L]
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (g : Gal(L/F)) (a : (padicTateTwistIn F L ℓ i).rep) :
    (padicTateTwistIn F L ℓ i).rep.ρ g a = padicTateScalarIn F L ℓ i g • a :=
  rfl

noncomputable def padicTateTwist (F : Type) [Field F] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    DiscreteGaloisModule ℤ_[ℓ] (Field.absoluteGaloisGroup F) where
  rep := padicTateTwistRep F ℓ i
  discreteOrbit := padicTateTwist_discreteOrbit F ℓ i

theorem padicTateTwist_ρ_apply (F : Type) [Field F] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)
    (σ : Field.absoluteGaloisGroup F) (a : (padicTateTwist F ℓ i).rep) :
    (padicTateTwist F ℓ i).rep.ρ σ a = padicTateScalar F ℓ i σ • a := rfl

end Utilities
