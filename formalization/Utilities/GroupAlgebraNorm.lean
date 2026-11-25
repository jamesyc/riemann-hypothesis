module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.RingTheory.Norm.Basic
import Utilities.FiniteAlgebraAnnihilator

@[expose] public section

open scoped BigOperators

namespace Utilities

variable (G : Type*) [CommGroup G]

/-- Simultaneous evaluation at the complex characters of a finite abelian group. -/
noncomputable def groupAlgebraCharacterEval :
    MonoidAlgebra ℂ G →ₐ[ℂ] (AddChar (Additive G) ℂ → ℂ) :=
  AlgHom.pi fun χ => MonoidAlgebra.lift ℂ ℂ G (AddChar.toMonoidHomEquiv χ)

@[simp]
theorem groupAlgebraCharacterEval_apply (z : MonoidAlgebra ℂ G) (χ : AddChar (Additive G) ℂ) :
    groupAlgebraCharacterEval G z χ = MonoidAlgebra.lift ℂ ℂ G (AddChar.toMonoidHomEquiv χ) z := rfl

/-- The characters form a basis of the functions on the group. Hence the
pairing with a group-algebra element detects each of its coefficients. -/
theorem groupAlgebraCharacterEval_injective [Fintype G] :
    Function.Injective (groupAlgebraCharacterEval G) := by
  classical
  let L (z : MonoidAlgebra ℂ G) : (Additive G → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∑ g : G, z.coeff g * f (Additive.ofMul g)
      map_add' := by intro f g; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a f
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have heval (z : MonoidAlgebra ℂ G) (χ : AddChar (Additive G) ℂ) :
      groupAlgebraCharacterEval G z χ = L z (AddChar.complexBasis (Additive G) χ) := by
    let η : G →* ℂ := AddChar.toMonoidHomEquiv χ
    change MonoidAlgebra.lift ℂ ℂ G η z = _
    have hη (g : G) : η g = χ (Additive.ofMul g) := rfl
    rw [MonoidAlgebra.lift_apply', Finsupp.sum_fintype]
    · simp only [Algebra.algebraMap_self, RingHom.id_apply, hη,
        AddChar.complexBasis_apply, L, LinearMap.coe_mk, AddHom.coe_mk]
    · simp
  intro z w h
  have hL : L z = L w := by
    apply (AddChar.complexBasis (Additive G)).ext
    intro χ
    rw [← heval, ← heval, h]
  ext g
  let f (x : Additive G) : ℂ := if x = Additive.ofMul g then 1 else 0
  have hf (v : MonoidAlgebra ℂ G) : L v f = v.coeff g := by
    change (∑ t : G, v.coeff t * f (Additive.ofMul t)) = v.coeff g
    rw [Finset.sum_eq_single g]
    · simp [f]
    · intro t ht htne
      simp [f, show Additive.ofMul t ≠ Additive.ofMul g from fun he => htne (Additive.ofMul.injective he)]
    · simp
  have hfg := congrArg (fun l : (Additive G → ℂ) →ₗ[ℂ] ℂ => l f) hL
  simpa only [hf] using hfg

/-- Fourier evaluation is an algebra isomorphism for the complex group algebra. -/
noncomputable def groupAlgebraCharacterEquiv [Fintype G] :
    MonoidAlgebra ℂ G ≃ₐ[ℂ] (AddChar (Additive G) ℂ → ℂ) := by
  let e := groupAlgebraCharacterEval G
  have he : Function.Injective e := groupAlgebraCharacterEval_injective G
  have hdim : Module.finrank ℂ (MonoidAlgebra ℂ G) =
      Module.finrank ℂ (AddChar (Additive G) ℂ → ℂ) := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ),
      Module.finrank_fintype_fun_eq_card, AddChar.card_eq]
    exact Fintype.card_congr Additive.ofMul
  exact AlgEquiv.ofBijective e ⟨he,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := e.toLinearMap)).mp he⟩

private theorem norm_pi_eq_prod {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    Algebra.norm ℂ x = ∏ i, x i := by
  classical
  rw [Algebra.norm_eq_matrix_det (Pi.basisFun ℂ ι)]
  have h : Algebra.leftMulMatrix (Pi.basisFun ℂ ι) x = Matrix.diagonal x := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Algebra.leftMulMatrix_apply]
    · simp [Algebra.leftMulMatrix_apply, h]
  rw [h, Matrix.det_diagonal]

/-- The norm of a complex group-algebra element is the product of its
character values. -/
theorem norm_groupAlgebra_eq_prod_characterEval [Fintype G] (z : MonoidAlgebra ℂ G) :
    Algebra.norm ℂ z = ∏ χ : AddChar (Additive G) ℂ, groupAlgebraCharacterEval G z χ := by
  have h := norm_pi_eq_prod (groupAlgebraCharacterEval G z)
  exact (Algebra.norm_eq_of_algEquiv (groupAlgebraCharacterEquiv G) z).symm.trans h

/-- Complex character evaluation commutes with extending integer coefficients. -/
theorem lift_complex_map_int (χ : G →* ℂ) (z : MonoidAlgebra ℤ G) :
    MonoidAlgebra.lift ℂ ℂ G χ (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ) z) =
      MonoidAlgebra.lift ℤ ℂ G χ z := by
  let f := (MonoidAlgebra.lift ℂ ℂ G χ).toRingHom.comp (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ))
  let g := (MonoidAlgebra.lift ℤ ℂ G χ).toRingHom
  have h : f = g := by
    apply MonoidAlgebra.ringHom_ext
    · intro x
      simp [f, g, Algebra.smul_def]
    · intro x
      simp [f, g]
  exact congrArg (fun t : MonoidAlgebra ℤ G →+* ℂ => t z) h

/-- Nonzero character values make the integral group-algebra norm nonzero,
and their common absolute bound gives the logarithmic determinant bound. -/
theorem intNorm_groupAlgebra_ne_zero_log_le [Fintype G] (z : MonoidAlgebra ℤ G)
    (B : ℝ)
    (h : ∀ χ : AddChar (Additive G) ℂ,
      let y := groupAlgebraCharacterEval G (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ) z) χ
      y ≠ 0 ∧ ‖y‖ ≤ B) :
    Algebra.norm ℤ z ≠ 0 ∧
      Real.log ((Algebra.norm ℤ z).natAbs : ℝ) ≤ (Fintype.card G : ℝ) * Real.log B := by
  let zC := MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ) z
  let value := groupAlgebraCharacterEval G zC
  have hnorm : (Algebra.norm ℤ z : ℂ) = ∏ χ, value χ := by
    rw [show (Algebra.norm ℤ z : ℂ) = Algebra.norm ℂ zC from
      map_norm_groupAlgebra (Int.castRingHom ℂ) z, norm_groupAlgebra_eq_prod_characterEval]
  have hne : Algebra.norm ℤ z ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at hnorm
    exact (Finset.prod_ne_zero_iff.mpr fun χ _ => (h χ).1) hnorm.symm
  have habs : ((Algebra.norm ℤ z).natAbs : ℝ) ≤ B ^ Fintype.card G := calc
    _ = ‖(Algebra.norm ℤ z : ℂ)‖ := by
      rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    _ = ∏ χ, ‖value χ‖ := by rw [hnorm, norm_prod]
    _ ≤ ∏ _χ : AddChar (Additive G) ℂ, B :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun χ _ => (h χ).2)
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, AddChar.card_eq, ← Fintype.card_congr Additive.ofMul]
  refine ⟨hne, ?_⟩
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (Int.natAbs_pos.mpr hne)) habs
  rwa [Real.log_pow] at hlog

end Utilities
