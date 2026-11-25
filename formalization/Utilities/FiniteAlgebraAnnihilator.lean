module

import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.Algebra.Polynomial.Inductions

@[expose] public section

open Polynomial

namespace Utilities

/-- An element of a finite free commutative algebra divides its norm viewed
in the algebra. Apply Cayley–Hamilton to multiplication by its negative so
that the constant coefficient is the norm without a sign. -/
theorem dvd_algebraMap_norm_of_finiteFree (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B] (z : B) :
    z ∣ algebraMap A B (Algebra.norm A z) := by
  let p := (Algebra.lmul A B (-z)).charpoly
  have hp : p.coeff 0 = Algebra.norm A z := by
    change (Algebra.lmul A B (-z)).charpoly.coeff 0 = Algebra.norm A z
    rw [coeff_zero_eq_eval_zero, LinearMap.eval_charpoly,
      map_zero (algebraMap A (Module.End A B)), zero_sub,
      map_neg (Algebra.lmul A B), neg_neg, Algebra.norm_apply]
  have ha : aeval (-z) p = 0 := Algebra.aeval_self_charpoly_lmul (-z)
  have h := congrArg (aeval (-z)) (X_mul_divX_add p)
  rw [map_add, map_mul, aeval_X, aeval_C, hp, ha] at h
  refine ⟨aeval (-z) p.divX, sub_eq_zero.mp ?_⟩
  rw [sub_eq_add_neg, add_comm, ← neg_mul]
  exact h

/-- If an algebra element annihilates a vector, its norm annihilates the
vector as a scalar. -/
theorem norm_smul_eq_zero_of_algebraAction {A B M : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    [AddCommGroup M] [Module A M] (ρ : B →ₐ[A] Module.End A M) (z : B) (x : M)
    (hz : ρ z x = 0) : Algebra.norm A z • x = 0 := by
  obtain ⟨w, hw⟩ := dvd_algebraMap_norm_of_finiteFree A B z
  have h := congrArg (fun b : B => ρ b x) hw
  rw [AlgHom.commutes, Module.algebraMap_end_apply, mul_comm z w, map_mul,
    mul_apply_eq_comp, hz, map_zero] at h
  exact h

/-- Keep the selected parity of a group algebra element and act by a
nonzero scalar on the complementary parity, without dividing by two. -/
noncomputable def groupAlgebraParityCompletion {A G : Type*} [CommRing A] [CommGroup G]
    (c : G) (ε : A) (z : MonoidAlgebra A G) : MonoidAlgebra A G :=
  (1 + MonoidAlgebra.single c ε) * z + (1 - MonoidAlgebra.single c ε)

/-- The completed element still kills any vector of the selected parity
that the original element kills. -/
theorem groupAlgebraParityCompletion_annihilates {A G M : Type*}
    [CommRing A] [CommGroup G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (c : G) (ε : A) (hε : ε * ε = 1)
    (z : MonoidAlgebra A G) (x : M) (hx : ρ c x = ε • x) (hz : ρ.asAlgebraHom z x = 0) :
    ρ.asAlgebraHom (groupAlgebraParityCompletion c ε z) x = 0 := by
  unfold groupAlgebraParityCompletion
  simp only [map_add, map_mul, map_sub, map_one, Representation.asAlgebraHom_single,
    LinearMap.add_apply, LinearMap.sub_apply, mul_apply_eq_comp, one_apply_eq_self,
    LinearMap.smul_apply, hz, map_zero, zero_add, hx, smul_smul, hε, one_smul, sub_self]

/-- The norm of the parity-completed element is a scalar annihilator. -/
theorem norm_parityCompletion_smul_eq_zero {A G M : Type*}
    [CommRing A] [CommGroup G] [Finite G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (c : G) (ε : A) (hε : ε * ε = 1)
    (z : MonoidAlgebra A G) (x : M) (hx : ρ c x = ε • x) (hz : ρ.asAlgebraHom z x = 0) :
    Algebra.norm A (groupAlgebraParityCompletion c ε z) • x = 0 := by
  let _ := Fintype.ofFinite G
  let _ : Module.Free A (MonoidAlgebra A G) := Module.Free.of_basis (MonoidAlgebra.basis G A)
  let _ : Module.Finite A (MonoidAlgebra A G) := Module.Finite.of_basis (MonoidAlgebra.basis G A)
  exact norm_smul_eq_zero_of_algebraAction ρ.asAlgebraHom _ x
    (groupAlgebraParityCompletion_annihilates ρ c ε hε z x hx hz)

/-- Character evaluation displays the completed element as the selected
value scaled by two and the value two on the opposite parity. -/
theorem lift_groupAlgebraParityCompletion {A B G : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [CommGroup G]
    (χ : G →* B) (c : G) (ε : A) (z : MonoidAlgebra A G) :
    MonoidAlgebra.lift A B G χ (groupAlgebraParityCompletion c ε z) =
      (1 + algebraMap A B ε * χ c) * MonoidAlgebra.lift A B G χ z + (1 - algebraMap A B ε * χ c) := by
  simp only [groupAlgebraParityCompletion, map_add, map_mul, map_sub, map_one,
    MonoidAlgebra.lift_single, Algebra.smul_def]

/-- Evaluation of a completed element on either parity. -/
theorem lift_groupAlgebraParityCompletion_eq_ite {A B G : Type*}
    [CommRing A] [Field B] [Algebra A B] [CommGroup G] [DecidableEq B]
    (χ : G →* B) (c : G) (hc : c * c = 1) (ε : A) (hε : ε * ε = 1)
    (z : MonoidAlgebra A G) :
    MonoidAlgebra.lift A B G χ (groupAlgebraParityCompletion c ε z) =
      if χ c = algebraMap A B ε then 2 * MonoidAlgebra.lift A B G χ z else 2 := by
  have hεB : algebraMap A B ε * algebraMap A B ε = 1 := by rw [← map_mul, hε, map_one]
  have hcB : χ c * χ c = 1 := by rw [← map_mul, hc, map_one]
  rw [lift_groupAlgebraParityCompletion]
  split_ifs with hχ
  · rw [hχ, hεB, sub_self, add_zero, one_add_one_eq_two]
  · have hprod : (χ c - algebraMap A B ε) * (χ c + algebraMap A B ε) = 0 := by
      rw [sub_mul, mul_add, mul_add, hcB, hεB]
      ring
    have hneg : χ c = -(algebraMap A B ε) :=
      eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hχ))
    rw [hneg, mul_neg, hεB, add_neg_cancel, zero_mul, zero_add, sub_neg_eq_add, one_add_one_eq_two]

/-- Over a field of characteristic different from two, completion gives
nonzero values on all characters if the original values on the selected
parity are nonzero. -/
theorem lift_groupAlgebraParityCompletion_ne_zero {A B G : Type*}
    [CommRing A] [Field B] [Algebra A B] [CommGroup G] [NeZero (2 : B)]
    (χ : G →* B) (c : G) (hc : c * c = 1) (ε : A) (hε : ε * ε = 1)
    (z : MonoidAlgebra A G)
    (hz : χ c = algebraMap A B ε → MonoidAlgebra.lift A B G χ z ≠ 0) :
    MonoidAlgebra.lift A B G χ (groupAlgebraParityCompletion c ε z) ≠ 0 := by
  classical
  rw [lift_groupAlgebraParityCompletion_eq_ite χ c hc ε hε]
  split_ifs with hχ
  · exact mul_ne_zero (NeZero.ne _) (hz hχ)
  · exact NeZero.ne _

/-- Parity completion commutes with changing the coefficient ring. -/
theorem mapRingHom_groupAlgebraParityCompletion {A B G : Type*} [CommRing A] [CommRing B]
    [CommGroup G] (f : A →+* B) (c : G) (ε : A) (z : MonoidAlgebra A G) :
    MonoidAlgebra.mapRingHom G f (groupAlgebraParityCompletion c ε z) =
      groupAlgebraParityCompletion c (f ε) (MonoidAlgebra.mapRingHom G f z) := by
  simp only [groupAlgebraParityCompletion, map_mul, map_add, map_sub, map_one, MonoidAlgebra.mapRingHom_single]

/-- Coefficient base change commutes with the group-algebra norm. -/
theorem map_norm_groupAlgebra {A B G : Type*} [CommRing A] [CommRing B]
    [CommGroup G] [Fintype G] (f : A →+* B) (z : MonoidAlgebra A G) :
    f (Algebra.norm A z) = Algebra.norm B (MonoidAlgebra.mapRingHom G f z) := by
  classical
  rw [Algebra.norm_eq_matrix_det (MonoidAlgebra.basis G A),
    Algebra.norm_eq_matrix_det (MonoidAlgebra.basis G B), RingHom.map_det]
  congr 1
  ext i j
  change f (Algebra.leftMulMatrix (MonoidAlgebra.basis G A) z i j) =
    Algebra.leftMulMatrix (MonoidAlgebra.basis G B) (MonoidAlgebra.mapRingHom G f z) i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    MonoidAlgebra.basis_apply, MonoidAlgebra.basis_apply]
  change f ((z * MonoidAlgebra.single j 1).coeff i) =
    (MonoidAlgebra.mapRingHom G f z * MonoidAlgebra.single j 1).coeff i
  rw [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_mul_single_apply,
    mul_one, mul_one, MonoidAlgebra.coeff_mapRingHom]

/-- If an integral group-algebra element kills a vector after base change,
its integral norm kills the same vector. -/
theorem intNorm_smul_eq_zero_of_groupAlgebraAction {A G M : Type*}
    [CommRing A] [CommGroup G] [Fintype G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (z : MonoidAlgebra ℤ G) (x : M)
    (hz : ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (Int.castRingHom A) z) x = 0) :
    (Algebra.norm ℤ z : A) • x = 0 := by
  change (Int.castRingHom A) (Algebra.norm ℤ z) • x = 0
  rw [map_norm_groupAlgebra]
  let _ := Module.Free.of_basis (MonoidAlgebra.basis G A)
  let _ := Module.Finite.of_basis (MonoidAlgebra.basis G A)
  exact norm_smul_eq_zero_of_algebraAction ρ.asAlgebraHom _ x hz

/-- The integer norm of a completion kills the selected parity when the
original element kills it after coefficient base change. -/
theorem intNorm_parityCompletion_smul_eq_zero {A G M : Type*}
    [CommRing A] [CommGroup G] [Fintype G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (c : G) (ε : ℤ) (hε : (ε : A) * (ε : A) = 1)
    (z : MonoidAlgebra ℤ G) (x : M) (hx : ρ c x = (ε : A) • x)
    (hz : ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (Int.castRingHom A) z) x = 0) :
    (Algebra.norm ℤ (groupAlgebraParityCompletion c ε z) : A) • x = 0 := by
  apply intNorm_smul_eq_zero_of_groupAlgebraAction ρ _ x
  rw [mapRingHom_groupAlgebraParityCompletion]
  exact groupAlgebraParityCompletion_annihilates ρ c (ε : A) hε _ x hx hz

end Utilities
