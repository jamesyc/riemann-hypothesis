module

public import Riemann.SelmerUnramifiedRestriction
public import Utilities.UnramifiedCharacterDescent

@[expose] public section

open Utilities NumberField
open scoped NumberField Pointwise

namespace Riemann

variable (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)

local notation "Ω" => AlgebraicClosure F
local notation "A" => padicTateTwist F ℓ i
local notation "D" => numberFieldSelmerRestrictions F ℓ

/-- At a finite Galois intermediate field containing the required roots,
the Tate Selmer class descends to a finite abelian extension that is also
Galois over `ℚ`, with trivial finite inertia and decomposition above `ℓ`. -/
theorem exists_finiteAbelian_unramified_tateSelmerRestriction (x : (A).selmerKernel D) :
    ∃ (r : ℕ) (c : (A).locallyTrivialCocycles₁ D), (Submodule.Quotient.mk c : (A).selmerKernel D) = x ∧
      (ℓ : ℤ_[ℓ]) ^ r • c = 0 ∧
      ∀ (E : IntermediateField F Ω) [FiniteDimensional F E] [IsGalois ℚ E], (∀ ζ : Ω, ζ ^ (ℓ ^ r) = 1 → ζ ∈ E) →
        ∃ T : FiniteGaloisIntermediateField E Ω, IsGalois ℚ T ∧ IsAbelianGalois E T ∧
          ∃ φ : Additive Gal(T/E) →+ (A).rep,
          (∀ σ : Gal(Ω/E), φ (Additive.ofMul (σ.restrictNormal T)) = c.val (σ.restrictScalars F)) ∧
          ∀ (Q : Ideal (𝓞 T)) [Q.IsPrime], Q ≠ ⊥ → ∀ τ : Gal(T/E),
            (τ ∈ Q.inertia Gal(T/E) ∨ ((ℓ : 𝓞 T) ∈ Q ∧ τ ∈ MulAction.stabilizer Gal(T/E) Q)) →
            τ = 1 := by
  obtain ⟨r, c, hcx, hc, hRestr⟩ := exists_unramified_tateSelmerRestriction_on_fixingSubgroup F ℓ i x
  refine ⟨r, c, hcx, hc, ?_⟩
  intro E _ _ hE
  let _ : NumberField E := NumberField.of_module_finite F E
  obtain ⟨ψ, hψeq, hψlc, hψ⟩ := hRestr E hE
  let ψE := ψ.comp E.fixingSubgroupEquiv.symm.toMonoidHom.toAdditive
  have hψE : ∀ (P : Ideal (𝓞 Ω)) [P.IsPrime], P ≠ ⊥ → ∀ σ : Gal(Ω/E),
      (σ ∈ P.inertia Gal(Ω/E) ∨ ((ℓ : 𝓞 Ω) ∈ P ∧ σ ∈ MulAction.stabilizer Gal(Ω/E) P)) →
      ψE (Additive.ofMul σ) = 0 := by
    intro P _ hP σ hσ
    apply hψ P hP (E.fixingSubgroupEquiv.symm σ)
    rcases hσ with hσ | ⟨hℓ, hD⟩
    · exact Or.inl (Ideal.mem_inertia.mpr (Ideal.mem_inertia.mp hσ))
    · exact Or.inr ⟨hℓ, MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp hD)⟩
  have hψElc : IsLocallyConstant (fun σ : Gal(Ω/E) => ψE (Additive.ofMul σ)) :=
    hψlc.comp_continuous (fixingSubgroupContinuousMulEquiv E).symm.continuous_toFun
  let _ : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω
  let E₀ := E.restrictScalars ℚ
  let _ : FiniteDimensional ℚ E₀ := FiniteDimensional.trans ℚ F E
  let _ : IsGalois ℚ E₀ := inferInstanceAs (IsGalois ℚ E)
  obtain ⟨T, hT, hAb, φ, hφ, hlocal⟩ :=
    exists_finiteAbelian_normal_unramified_descendant E₀ ℓ ψE hψElc hψE
  exact ⟨T, hT, hAb, φ, fun σ => (hφ σ).trans (hψeq _), hlocal⟩

end Riemann
