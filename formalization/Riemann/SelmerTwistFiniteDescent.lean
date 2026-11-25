module

public import Riemann.SelmerTwistConductor
public import Utilities.UnramifiedCharacterDescent
public import Mathlib.Algebra.Module.Hom
import Utilities.CyclotomicLayer
import Utilities.PadicTateFiniteRestriction

@[expose] public section

open NumberField Utilities DiscreteGaloisModule groupCohomology
open scoped NumberField Pointwise IsMulCommutative TensorProduct

namespace Riemann

section SharedTwist

variable (F : Type) [Field F] [NumberField F] [IsAbelianGalois ℚ F]
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S]
  (ψ : Gal(F/ℚ) →* Sˣ)

local notation "Ω" => AlgebraicClosure F
local notation "T" => numberFieldSelmerSharedInverseTwist F ℓ i S ψ
local notation "δ" => numberFieldTwistNormalizationElement F
local notation "G" => Gal(Ω/ℚ)
local instance : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω

/-- A Galois element fixing the relevant cyclotomic roots and the host
character acts trivially on coefficients of the specified exponent. -/
theorem sharedTwist_action_eq_self_of_fixes_roots (r : ℕ) (g : G)
    (hψ : ψ (g.restrictNormal F) = 1)
    (hroot : ∀ ζ : Ω, ζ ^ (ℓ ^ r) = 1 → g ζ = ζ)
    (x : (T).rep) (hx : (ℓ : S) ^ r • x = 0) :
    (T).rep.ρ g x = x := by
  have hred : PadicInt.toZModPow r (padicTateScalarIn ℚ Ω ℓ i g) = 1 :=
    padicTateScalarOnAut_toZModPow_eq_one_of_fixes_roots ℓ Ω i r g.toRingEquiv hroot
  rw [numberFieldSelmerSharedInverseTwist_ρ F ℓ i S ψ g, hψ, inv_one, Units.val_one, one_mul,
    LinearMap.smul_apply, one_apply_eq_self]
  let y : S ⊗[ℤ_[ℓ]] PadicTateQuotient ℓ := x
  change (algebraMap ℤ_[ℓ] S (padicTateScalarIn ℚ Ω ℓ i g)) • y = y
  rw [IsScalarTower.algebraMap_smul]
  apply padicInt_smul_eq_self_of_toZModPow_eq_one ℓ hred
  rw [← IsScalarTower.algebraMap_smul S, map_pow, map_natCast]
  exact hx

variable (r : ℕ) (E : IntermediateField ℚ (AlgebraicClosure F))
local notation "L" => numberFieldSelmerSharedTwistArithmeticLayer F ℓ i S ψ r

/-- Over a field killing the finite character and containing the
cyclotomic roots of the exponent layer, restriction is additive. -/
noncomputable def sharedTwistArithmeticLayer_restriction
    (hψ : ∀ σ : Gal(Ω/E), ψ ((σ.restrictScalars ℚ).restrictNormal F) = 1)
    (hroot : ∀ ζ : Ω, ζ ^ (ℓ ^ r) = 1 → ζ ∈ E) :
    L →ₗ[S] (Additive Gal(Ω/E) →+ (T).rep) where
  toFun c :=
    { toFun := fun σ => c.val.val (σ.toMul.restrictScalars ℚ)
      map_zero' := cocycles₁_map_one (⟨c.val.val, c.val.property.1.1.1⟩ : cocycles₁ (T).rep)
      map_add' := fun σ τ => by
        have ha : (ℓ : S) ^ r • c.val.val (τ.toMul.restrictScalars ℚ) = 0 :=
          congrArg (fun f => f.val (τ.toMul.restrictScalars ℚ)) c.property.1
        have hact := sharedTwist_action_eq_self_of_fixes_roots F ℓ i S ψ r
          (σ.toMul.restrictScalars ℚ) (hψ σ.toMul)
          (fun ζ hζ => σ.toMul.commutes (⟨ζ, hroot ζ hζ⟩ : E)) _ ha
        change c.val.val ((AlgEquiv.restrictScalarsHom ℚ) (σ.toMul * τ.toMul)) =
          c.val.val (σ.toMul.restrictScalars ℚ) + c.val.val (τ.toMul.restrictScalars ℚ)
        rw [map_mul, (mem_cocycles₁_iff c.val.val).mp c.val.property.1.1.1,
          AlgEquiv.restrictScalarsHom_apply, AlgEquiv.restrictScalarsHom_apply, hact, add_comm] }
  map_add' _ _ := AddMonoidHom.ext fun _ => rfl
  map_smul' _ _ := AddMonoidHom.ext fun _ => rfl

/-- A nonzero normalized cocycle has a nonzero restriction to the fixing
subgroup of an abelian coefficient field. -/
theorem sharedTwistArithmeticLayer_restriction_injective [IsAbelianGalois ℚ E]
    (hψ : ∀ σ : Gal(Ω/E), ψ ((σ.restrictScalars ℚ).restrictNormal F) = 1)
    (hroot : ∀ ζ : Ω, ζ ^ (ℓ ^ r) = 1 → ζ ∈ E)
    (hodd : ℓ ≠ 2) (hparity : (ψ ((δ).restrictNormal F) : S) = (-1 : S) ^ (i + 1)) :
    Function.Injective (sharedTwistArithmeticLayer_restriction F ℓ i S ψ r E hψ hroot) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  apply Subtype.ext
  let π : Gal(Ω/ℚ) →* Gal(E/ℚ) := AlgEquiv.restrictNormalHom E
  apply normalizedSelmerCocycles_eq_zero_of_vanishes_on_abelianKernel _ _ _ π
    (numberFieldSelmerSharedTwist_normalization_bijective F ℓ i S ψ hodd hparity).injective
  intro g hg
  change g ∈ (AlgEquiv.restrictNormalHom E).ker at hg
  rw [E.restrictNormalHom_ker] at hg
  let σ := E.fixingSubgroupEquiv ⟨g, hg⟩
  exact DFunLike.congr_fun hc (Additive.ofMul σ)

end SharedTwist

section Host

variable (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
  (ℓ : ℕ) [Fact ℓ.Prime] (i r : ℕ) (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))

local notation "F" => selmerHostField target e q d
local notation "Ω" => AlgebraicClosure F
local instance : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
local instance : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω

variable (ψ : Gal((selmerHostField target e q d)/ℚ) →* Oˣ)
local notation "cnd" => DirichletCharacter.conductor
  (selmerDirichletOfCharacter target e q d ℓ O (AlgHom.toRingHom (Subalgebra.val O)) ψ)

/-- The cyclotomic field of order `cnd * ℓ ^ r` kills the host character
and contains all roots needed for the Tate action at precision `r`. -/
theorem exists_sharedTwistArithmeticLayer_coefficientField :
    ∃ E : FiniteGaloisIntermediateField ℚ Ω,
      IsCyclotomicExtension {cnd * ℓ ^ r} ℚ E ∧
      (∀ σ : Gal(Ω/E), ψ ((σ.restrictScalars ℚ).restrictNormal F) = 1) ∧
      (∀ ζ : Ω, ζ ^ (ℓ ^ r) = 1 → ζ ∈ E.toIntermediateField) := by
  let f := selmerHostConductor target e q d
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let N := cnd * ℓ ^ r
  have hN : N ≠ 0 :=
    mul_ne_zero (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ).conductor_ne_zero
      (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  let _ : NeZero N := ⟨hN⟩
  let _ : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.mpr hN⟩
  obtain ⟨ζ, hζ⟩ := (inferInstance : HasEnoughRootsOfUnity Ω N).prim
  let C := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  let _ : IsCyclotomicExtension {N} ℚ C := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let _ : NumberField C := IsCyclotomicExtension.numberField {N} ℚ C
  let _ : IsGalois ℚ C := IsCyclotomicExtension.isGalois {N} ℚ C
  let E : FiniteGaloisIntermediateField ℚ Ω := ⟨C⟩
  have hC {a : ℕ} (ha : a ∣ N) (z : Ω) (hz : z ^ a = 1) : z ∈ C := by
    apply mem_cyclotomicLayer_of_pow_eq_one N C
    obtain ⟨k, hk⟩ := ha
    rw [hk, pow_mul, hz, one_pow]
  refine ⟨E, inferInstanceAs (IsCyclotomicExtension {N} ℚ C), ?_, hC (dvd_mul_left _ _)⟩
  intro σ
  apply selmerHostCharacter_eq_one_of_fixes_conductor_roots target e q d ℓ O ψ
  intro z hz
  exact σ.commutes (⟨z, hC (dvd_mul_right _ _) z hz⟩ : C)

variable (E : IntermediateField ℚ (AlgebraicClosure (selmerHostField target e q d)))
  (hψ : ∀ σ : Gal((AlgebraicClosure (selmerHostField target e q d))/E),
    ψ ((σ.restrictScalars ℚ).restrictNormal (selmerHostField target e q d)) = 1)
  (hroot : ∀ ζ : AlgebraicClosure (selmerHostField target e q d), ζ ^ (ℓ ^ r) = 1 → ζ ∈ E)

local notation "T" => numberFieldSelmerSharedInverseTwist F ℓ i O ψ
local notation "res" => sharedTwistArithmeticLayer_restriction F ℓ i O ψ r E hψ hroot

/-- After restriction to a coefficient field, the character is unramified
everywhere and kills decomposition at primes dividing a conductor or the Tate prime. -/
theorem sharedTwistArithmeticLayer_restriction_eq_zero_of_mem_local
    (c : numberFieldSelmerSharedTwistArithmeticLayer F ℓ i O ψ r)
    (P : Ideal (𝓞 Ω)) [P.IsPrime] (hne : P ≠ ⊥) (σ : Gal(Ω/E))
    (hσ : σ ∈ P.inertia Gal(Ω/E) ∨
      (((cnd * ℓ : ℕ) : 𝓞 Ω) ∈ P ∧ σ ∈ MulAction.stabilizer Gal(Ω/E) P)) :
    res c (Additive.ofMul σ) = 0 := by
  let g := σ.restrictScalars ℚ
  change c.val.val g = 0
  by_cases hP : ((cnd * ℓ : ℕ) : 𝓞 Ω) ∈ P
  · obtain ⟨b, hb, hc⟩ :=
      sharedTwistArithmeticLayer_bounded_at_primitiveConductorPrime target e q d ℓ O i r ψ c P hne hP
    have hg : g ∈ MulAction.stabilizer Gal(Ω/ℚ) P := by
      rcases hσ with hI | ⟨_, hD⟩
      · exact Ideal.inertia_le_stabilizer P (Ideal.mem_inertia.mpr (Ideal.mem_inertia.mp hI))
      · exact MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp hD)
    have hact := sharedTwist_action_eq_self_of_fixes_roots F ℓ i O ψ r g (hψ σ)
      (fun ζ hζ => σ.commutes (⟨ζ, hroot ζ hζ⟩ : E)) b hb
    rw [hc g hg, hact, sub_self]
  · have hI := hσ.resolve_right fun h => hP h.1
    exact sharedTwistCocycle_eq_zero_away_primitiveConductorPrime target e q d ℓ O i ψ c.val P hne hP
      (Ideal.mem_inertia.mpr (Ideal.mem_inertia.mp hI))

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 600000 in
/-- A normalized bounded twist cocycle restricts over a finite Galois
coefficient field to a character of a finite unramified abelian extension.
The extension is Galois over ℚ and split at the bad primes. -/
theorem sharedTwistArithmeticLayer_exists_finiteAbelian_descendant [FiniteDimensional ℚ E]
    [IsGalois ℚ E] (c : numberFieldSelmerSharedTwistArithmeticLayer F ℓ i O ψ r) :
    letI : NumberField E := NumberField.of_module_finite ℚ E
    ∃ B : FiniteGaloisIntermediateField E Ω, IsGalois ℚ B ∧ IsAbelianGalois E B ∧
      ∃ φ : Additive Gal(B/E) →+ (T).rep,
        (∀ σ : Gal(Ω/E), φ (Additive.ofMul (σ.restrictNormal B)) = res c (Additive.ofMul σ)) ∧
        ∀ (Q : Ideal (𝓞 B)) [Q.IsPrime], Q ≠ ⊥ → ∀ τ : Gal(B/E),
          (τ ∈ Q.inertia Gal(B/E) ∨
            (((cnd * ℓ : ℕ) : 𝓞 B) ∈ Q ∧ τ ∈ MulAction.stabilizer Gal(B/E) Q)) → τ = 1 :=
  exists_finiteAbelian_normal_unramified_descendant E (cnd * ℓ) (res c)
    (c.val.property.1.1.2.comp_continuous
      (continuous_subtype_val.comp (fixingSubgroupContinuousMulEquiv E).symm.continuous_toFun))
    (sharedTwistArithmeticLayer_restriction_eq_zero_of_mem_local target e q d ℓ i r O ψ E hψ hroot c)

end Host
end Riemann
