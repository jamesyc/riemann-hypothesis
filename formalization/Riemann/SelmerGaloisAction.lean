module

public import Riemann.SelmerConjugation

@[expose] public section

open Utilities groupCohomology

namespace Riemann

variable (F : Type) [Field F] [NumberField F] [Normal ℚ F]
variable (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)

local notation "L" => AlgebraicClosure F
local notation "G" => (L ≃ₐ[F] L)
local notation "H" => (L ≃ₐ[ℚ] L)
local notation "A" => padicTateTwist F ℓ i
local notation "D" => numberFieldSelmerRestrictions F ℓ
local notation "C" => DiscreteGaloisModule.locallyTrivialCocycles₁ A D
local notation "B" => Submodule.comap (Submodule.subtype C) (coboundaries₁ (DiscreteGaloisModule.rep A))
local notation "χ" => padicTateScalarOnAut L ℓ i

theorem numberFieldSelmerAmbientCoefficient_intertwines (τ : H)
    (g : Field.absoluteGaloisGroup F) (a : (A).rep) :
    let u : Module.End ℤ_[ℓ] (A).rep := χ τ.toRingEquiv • LinearMap.id
    u ((A).rep.ρ (relativeGaloisConj ℚ F L τ.symm g) a) = (A).rep.ρ g (u a) := by
  intro u
  let g' : Field.absoluteGaloisGroup F := relativeGaloisConj ℚ F L τ.symm g
  have hφ : padicTateScalar F ℓ i g' = padicTateScalar F ℓ i g :=
    padicTateScalar_relativeGaloisConj F ℓ i τ.symm g
  change u (padicTateScalar F ℓ i g' • a) = padicTateScalar F ℓ i g • u a
  rw [hφ]
  exact u.map_smul _ _

/-- A lift to the algebraic closure acts on restricted cohomology by inverse
conjugation on its group argument and direct action on the Tate coefficient. -/
noncomputable def numberFieldSelmerAmbientPullback (τ : H) :
    Module.End ℤ_[ℓ] ((A).selmerKernel D) := by
  let φ : Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup F :=
    relativeGaloisConj ℚ F L τ.symm
  let u : Module.End ℤ_[ℓ] (A).rep := χ τ.toRingEquiv • LinearMap.id
  exact (A).pullbackSelmerKernel D φ (relativeGaloisConj_continuous ℚ F L τ.symm) u
    (numberFieldSelmerAmbientCoefficient_intertwines F ℓ i τ)
    (numberFieldSelmerRestrictions_map_conj F ℓ τ.symm)

theorem numberFieldSelmerAmbientPullback_one :
    numberFieldSelmerAmbientPullback F ℓ i (1 : H) = 1 := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective B z
  change (B).mkQ _ = (B).mkQ f
  congr 1
  apply Subtype.ext
  funext g
  change χ (1 : L ≃+* L) • f.val (relativeGaloisConj ℚ F L (1 : H).symm g) = f.val g
  have hgroup : relativeGaloisConj ℚ F L (1 : H).symm g = g :=
    relativeGaloisConj_one ℚ F L (show G from g)
  rw [hgroup, map_one, one_smul]

theorem numberFieldSelmerAmbientPullback_mul (σ τ : H) :
    numberFieldSelmerAmbientPullback F ℓ i (σ * τ) =
      numberFieldSelmerAmbientPullback F ℓ i σ * numberFieldSelmerAmbientPullback F ℓ i τ := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective B z
  simp only [mul_apply_eq_comp]
  change (B).mkQ _ = (B).mkQ _
  congr 1
  apply Subtype.ext
  funext g
  have hgroup : relativeGaloisConj ℚ F L (σ * τ).symm g =
      relativeGaloisConj ℚ F L τ.symm (relativeGaloisConj ℚ F L σ.symm g) := by
    exact relativeGaloisConj_mul ℚ F L τ.symm σ.symm g
  change χ (σ.toRingEquiv * τ.toRingEquiv) • f.val (relativeGaloisConj ℚ F L (σ * τ).symm g) =
    χ σ.toRingEquiv • (χ τ.toRingEquiv •
      f.val (relativeGaloisConj ℚ F L τ.symm (relativeGaloisConj ℚ F L σ.symm g)))
  rw [map_mul, hgroup, mul_smul]

/-- The ambient action makes the Selmer restriction kernel a representation
of the Galois group of the algebraic closure over the rational numbers. -/
noncomputable def numberFieldSelmerAmbientAction :
    H →* Module.End ℤ_[ℓ] ((A).selmerKernel D) where
  toFun := numberFieldSelmerAmbientPullback F ℓ i
  map_one' := numberFieldSelmerAmbientPullback_one F ℓ i
  map_mul' := numberFieldSelmerAmbientPullback_mul F ℓ i

theorem numberFieldSelmerAmbientAction_restrictScalars_eq_one (s : G) :
    numberFieldSelmerAmbientAction F ℓ i (s.restrictScalars ℚ) = 1 := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective B z
  change (B).mkQ _ = (B).mkQ f
  rw [← sub_eq_zero, ← map_sub]
  apply (Submodule.Quotient.mk_eq_zero B).mpr
  let f' : cocycles₁ (A).rep := ⟨f.val, f.property.1.1⟩
  refine ⟨f' s, funext fun g => ?_⟩
  change (A).rep.ρ g (f' s) - f' s =
    (A).rep.ρ s (f' (relativeGaloisConj ℚ F L (s.restrictScalars ℚ).symm g)) - f' g
  exact ((A).inner_pullback_sub_eq_coboundary f' s g).symm

local instance : IsAlgClosure ℚ L := IsAlgClosure.ofAlgebraic ℚ F L

theorem ker_restrictNormalHom_le_selmerAmbientAction :
    (AlgEquiv.restrictNormalHom F : H →* (F ≃ₐ[ℚ] F)).ker ≤
      (numberFieldSelmerAmbientAction F ℓ i).ker := by
  intro τ hτ
  have hτ' : τ.restrictNormal F = 1 := hτ
  let s : G :=
    { __ := τ.toRingEquiv
      commutes' := fun x => by
        change τ (algebraMap F L x) = algebraMap F L x
        rw [← τ.restrictNormal_commutes F, hτ']
        rfl }
  have hs : s.restrictScalars ℚ = τ := by
    apply AlgEquiv.ext
    intro x
    rfl
  change numberFieldSelmerAmbientAction F ℓ i τ = 1
  rw [← hs]
  exact numberFieldSelmerAmbientAction_restrictScalars_eq_one F ℓ i s

/-- The action on the actual Selmer restriction kernel descends canonically
to the Galois group of the number field itself. -/
noncomputable def numberFieldSelmerGaloisAction :
    (F ≃ₐ[ℚ] F) →* Module.End ℤ_[ℓ] ((A).selmerKernel D) :=
  let φ : H →* (F ≃ₐ[ℚ] F) := AlgEquiv.restrictNormalHom F
  let e := (QuotientGroup.quotientKerEquivOfSurjective φ
    (AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := F) L))
  (QuotientGroup.lift φ.ker (numberFieldSelmerAmbientAction F ℓ i)
    (ker_restrictNormalHom_le_selmerAmbientAction F ℓ i)).comp e.symm.toMonoidHom

theorem numberFieldSelmerGaloisAction_restrictNormal (τ : H) :
    numberFieldSelmerGaloisAction F ℓ i (τ.restrictNormal F) =
      numberFieldSelmerAmbientAction F ℓ i τ := by
  let φ : H →* (F ≃ₐ[ℚ] F) := AlgEquiv.restrictNormalHom F
  let e := QuotientGroup.quotientKerEquivOfSurjective φ
    (AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := F) L)
  unfold numberFieldSelmerGaloisAction
  change QuotientGroup.lift φ.ker (numberFieldSelmerAmbientAction F ℓ i)
      (ker_restrictNormalHom_le_selmerAmbientAction F ℓ i) (e.symm (φ τ)) =
    numberFieldSelmerAmbientAction F ℓ i τ
  have he : e (QuotientGroup.mk τ) = φ τ := rfl
  rw [← he, MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]

/-- The previously constructed complex involution is the action of the
corresponding element of the finite field Galois group. -/
theorem numberFieldSelmerGaloisAction_complexConjugation
    (ι : L →ₐ[ℚ] ℂ) :
    numberFieldSelmerGaloisAction F ℓ i (algEquiv_complexConjugation F (ι.domRestrict F)) =
      numberFieldSelmerConjugation F ℓ i ι := by
  let τ := algEquiv_complexConjugation L ι
  have hτ : τ.symm = τ := by
    apply AlgEquiv.ext
    intro x
    apply τ.injective
    exact (τ.apply_symm_apply x).trans ((algEquiv_complexConjugation_involutive L ι x).symm)
  have hrestrict : τ.restrictNormal F = algEquiv_complexConjugation F (ι.domRestrict F) := by
    apply AlgEquiv.ext
    intro x
    apply (ι.domRestrict F).injective
    change (ι.domRestrict F) (τ.restrictNormal F x) =
      (ι.domRestrict F) (algEquiv_complexConjugation F (ι.domRestrict F) x)
    rw [algEquiv_complexConjugation_apply]
    change ι (algebraMap F L (τ.restrictNormal F x)) = star (ι (algebraMap F L x))
    rw [τ.restrictNormal_commutes F]
    exact algEquiv_complexConjugation_apply L ι (algebraMap F L x)
  rw [← hrestrict, numberFieldSelmerGaloisAction_restrictNormal]
  change numberFieldSelmerAmbientPullback F ℓ i τ = _
  unfold numberFieldSelmerAmbientPullback numberFieldSelmerConjugation
  apply DiscreteGaloisModule.pullbackSelmerKernel_congr _ _ _ rfl
  exact congrArg (relativeGaloisConj ℚ F L) hτ

end Riemann
