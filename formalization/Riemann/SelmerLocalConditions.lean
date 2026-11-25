module

public import Riemann.SelmerCohomology
public import Utilities.SelmerDecomposition

@[expose] public section

open Utilities
open scoped NumberField Pointwise

namespace Riemann

/-- For the actual restriction conditions, a cocycle is already locally
trivial on inertia at the chosen prolongation. The local criterion then
adds its decomposition subgroup, as in Lemma 17.18. -/
theorem numberFieldSelmer_coboundary_on_decomposition
    (F : Type) [Field F] [NumberField F] (ℓ : ℕ)
    {k : Type} [CommRing k]
    (A : DiscreteGaloisModule k (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
    (v : NumberField.FinitePlace F) (P : Ideal (𝓞 (AlgebraicClosure F)))
    (hp : P.IsPrime)
    (hover : P.comap (NumberField.RingOfIntegers.mapRingHom (algebraMap F (AlgebraicClosure F))) =
      v.maximalIdeal.asIdeal)
    {f : (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) → A.rep}
    (hf : f ∈ A.locallyTrivialCocycles₁ (numberFieldSelmerRestrictions F ℓ))
    (hlocal :
      (∀ a : A.rep, (∀ d ∈ P.inertia (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F), A.rep.ρ d a = a) → a = 0) ∨
      let D := MulAction.stabilizer (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) P
      let I := P.inertia D
      (∀ d ∈ P.inertia (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F), ∀ a : A.rep, A.rep.ρ d a = a) ∧
      ∃ φ : D,
        Dense (Subgroup.zpowers (QuotientGroup.mk' I φ) : Set (D ⧸ I)) ∧
        Function.Surjective (fun a : A.rep => A.rep.ρ φ.val a - a)) :
    ∃ a : A.rep, ∀ d ∈ MulAction.stabilizer (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) P,
      f d = A.rep.ρ d a - a := by
  have hmem : P.inertia (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ∈ numberFieldSelmerRestrictions F ℓ :=
    ⟨v, P, hp, hover, Or.inl rfl⟩
  have hI := hf.2 _ hmem
  rcases hlocal with hfixed | ⟨hact, φ, hdense, hFrob⟩
  · exact A.exists_coboundary_on_stabilizer_of_inertia_no_fixed P hf.1 hfixed hI
  · exact A.exists_coboundary_on_stabilizer_of_unramified P hf.1 hact hI φ hdense hFrob

end Riemann
