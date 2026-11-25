module

public import Utilities.KrullCharacterDescent
public import Utilities.InertiaRestriction
import Mathlib.Algebra.Group.Pi.Hom
import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open NumberField
open scoped NumberField Pointwise

namespace Utilities

/-- A character descending from an algebraic Galois extension to a finite
one retains its vanishing on inertia and on decomposition above the chosen prime. -/
theorem descendedCharacter_eq_zero_of_mem_local
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    (ℓ : ℕ) (T : FiniteGaloisIntermediateField K L) {M : Type*} [AddGroup M]
    (ψ : Additive Gal(L/K) →+ M) (φ : Additive Gal(T/K) →+ M)
    (hφ : ∀ σ : Gal(L/K), φ (Additive.ofMul (σ.restrictNormal T)) = ψ (Additive.ofMul σ))
    (hψ : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ → ∀ σ : Gal(L/K),
      (σ ∈ P.inertia Gal(L/K) ∨
        ((ℓ : 𝓞 L) ∈ P ∧ σ ∈ MulAction.stabilizer Gal(L/K) P)) → ψ (Additive.ofMul σ) = 0)
    (Q : Ideal (𝓞 T)) [Q.IsPrime] (hQ : Q ≠ ⊥) (τ : Gal(T/K))
    (hτ : τ ∈ Q.inertia Gal(T/K) ∨
      ((ℓ : 𝓞 T) ∈ Q ∧ τ ∈ MulAction.stabilizer Gal(T/K) Q)) :
    φ (Additive.ofMul τ) = 0 := by
  let _ : NumberField T := NumberField.of_module_finite K T
  let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral Q (S := 𝓞 L)
  let _ : P.IsPrime := hP.isPrime
  let _ : P.LiesOver Q := hPQ
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hQ P
  have hunder := (Ideal.over_def P Q).symm
  obtain ⟨σ, hσ, hστ⟩ : ∃ σ : Gal(L/K),
      (σ ∈ P.inertia Gal(L/K) ∨ ((ℓ : 𝓞 L) ∈ P ∧ σ ∈ MulAction.stabilizer Gal(L/K) P)) ∧
      σ.restrictNormal T = τ := by
    rcases hτ with hI | ⟨hℓ, hD⟩
    · have hmap := numberField_inertia_map_restrictNormal_of_isGalois T P
      rw [hunder] at hmap
      obtain ⟨σ, hσ, hστ⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hI)
      exact ⟨σ, Or.inl hσ, hστ⟩
    · have hmap := numberField_stabilizer_map_restrictNormal_of_isGalois T P
      rw [hunder] at hmap
      obtain ⟨σ, hσ, hστ⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hD)
      have hpℓ : (ℓ : 𝓞 L) ∈ P := by
        rw [← hunder] at hℓ
        change algebraMap (𝓞 T) (𝓞 L) (ℓ : 𝓞 T) ∈ P at hℓ
        simpa only [map_natCast] using hℓ
      exact ⟨σ, Or.inr ⟨hpℓ, hσ⟩, hστ⟩
  rw [← hστ, hφ σ]
  exact hψ P hPne σ hσ

private theorem relativeGaloisConj_mem_local
    {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L) [Normal K E]
    (ℓ : ℕ) (P : Ideal (𝓞 L)) (s : Gal(L/K)) (σ : Gal(L/E))
    (hσ : σ ∈ P.inertia Gal(L/E) ∨ ((ℓ : 𝓞 L) ∈ P ∧ σ ∈ MulAction.stabilizer Gal(L/E) P)) :
    relativeGaloisConj K E L s σ ∈ (s • P : Ideal (𝓞 L)).inertia Gal(L/E) ∨
      ((ℓ : 𝓞 L) ∈ s • P ∧ relativeGaloisConj K E L s σ ∈
        MulAction.stabilizer Gal(L/E) (s • P)) := by
  let τ := relativeGaloisConj K E L s σ
  have hτ : τ.restrictScalars K = s * σ.restrictScalars K * s⁻¹ :=
    relativeGaloisConj_restrictScalars K E L s σ
  rcases hσ with hI | ⟨hℓ, hD⟩
  · left
    have h : σ.restrictScalars K ∈ P.inertia Gal(L/K) :=
      Ideal.mem_inertia.mpr (Ideal.mem_inertia.mp hI)
    have hconj : τ.restrictScalars K ∈ (s • P : Ideal (𝓞 L)).inertia Gal(L/K) := by
      rw [Ideal.inertia_smul, hτ]
      exact Subgroup.mem_map.mpr ⟨_, h, rfl⟩
    exact Ideal.mem_inertia.mpr (Ideal.mem_inertia.mp hconj)
  · right
    refine ⟨?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
    · rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      change (MulSemiringAction.toRingAut Gal(L/K) (𝓞 L) s⁻¹) (ℓ : 𝓞 L) ∈ P
      rwa [map_natCast]
    · have h : σ.restrictScalars K • P = P := MulAction.mem_stabilizer_iff.mp hD
      change τ.restrictScalars K • (s • P) = s • P
      rw [hτ, mul_smul, mul_smul, inv_smul_smul, h]

/-- An unramified character over a finite Galois base descends to a finite
abelian extension that is also Galois over the original base. Its conjugates
preserve the vanishing conditions on the descended extension. -/
theorem exists_finiteAbelian_normal_unramified_descendant
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    (E : IntermediateField K L) [FiniteDimensional K E] [IsGalois K E]
    (ℓ : ℕ) {M : Type*} [AddCommGroup M] (ψ : Additive Gal(L/E) →+ M)
    (hψlc : IsLocallyConstant (fun σ : Gal(L/E) => ψ (Additive.ofMul σ)))
    (hψ : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ → ∀ σ : Gal(L/E),
      (σ ∈ P.inertia Gal(L/E) ∨ ((ℓ : 𝓞 L) ∈ P ∧ σ ∈ MulAction.stabilizer Gal(L/E) P)) →
      ψ (Additive.ofMul σ) = 0) :
    letI : NumberField E := NumberField.of_module_finite K E
    ∃ T : FiniteGaloisIntermediateField E L, IsGalois K T ∧ IsAbelianGalois E T ∧
      ∃ φ : Additive Gal(T/E) →+ M,
        (∀ σ : Gal(L/E), φ (Additive.ofMul (σ.restrictNormal T)) = ψ (Additive.ofMul σ)) ∧
        ∀ (Q : Ideal (𝓞 T)) [Q.IsPrime], Q ≠ ⊥ → ∀ τ : Gal(T/E),
          (τ ∈ Q.inertia Gal(T/E) ∨ ((ℓ : 𝓞 T) ∈ Q ∧ τ ∈ MulAction.stabilizer Gal(T/E) Q)) →
          τ = 1 := by
  let _ : NumberField E := NumberField.of_module_finite K E
  obtain ⟨T, hT, hAb, Φ, hΦinj, hΦ⟩ :=
    exists_finiteAbelian_normal_descendant_of_locallyConstant E ψ hψlc
  let Ψ := relativeGaloisConjugateCharacters E ψ
  have hΨ (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) (σ : Gal(L/E))
      (hσ : σ ∈ P.inertia Gal(L/E) ∨ ((ℓ : 𝓞 L) ∈ P ∧ σ ∈ MulAction.stabilizer Gal(L/E) P)) :
      Ψ (Additive.ofMul σ) = 0 := by
    funext s
    have : (s • P : Ideal (𝓞 L)).IsPrime := (Ideal.IsPrime.smul_iff s).mpr inferInstance
    have hne : (s • P : Ideal (𝓞 L)) ≠ ⊥ := by
      intro h
      apply hP
      simpa only [inv_smul_smul, smul_bot] using congrArg (fun I : Ideal (𝓞 L) => s⁻¹ • I) h
    exact hψ (s • P) hne _ (relativeGaloisConj_mem_local E ℓ P s σ hσ)
  let φ := (Pi.evalAddMonoidHom (fun _ : Gal(L/K) => M) 1).comp Φ
  refine ⟨T, hT, hAb, φ, fun σ => ?_, fun Q _ hQ τ hτ => ?_⟩
  · change Φ (Additive.ofMul (σ.restrictNormal T)) 1 = ψ (Additive.ofMul σ)
    simpa only [relativeGaloisConj_one] using hΦ σ 1
  · have hzero := descendedCharacter_eq_zero_of_mem_local ℓ T Ψ Φ (fun σ => funext (hΦ σ)) hΨ Q hQ τ hτ
    exact congrArg Additive.toMul (hΦinj (hzero.trans (map_zero Φ).symm))

end Utilities
