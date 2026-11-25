module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

@[expose] public section

open scoped Matrix InnerProductSpace
open Module

namespace Utilities

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_orthonormalBasis_extending_fin [FiniteDimensional ℂ H] {d n : ℕ} (hd : d ≤ n)
    (hn : finrank ℂ H = n) {rows : Fin d → H} (ho : Orthonormal ℂ rows) :
    ∃ basis : OrthonormalBasis (Fin n) ℂ H, ∀ i, basis (Fin.castLE hd i) = rows i := by
  let s : Set (Fin n) := {i | i.val < d}
  let rowOn (i : Fin n) : H := if hi : i.val < d then rows ⟨i.val, hi⟩ else 0
  let idx (i : s) : Fin d := ⟨i.val.val, i.prop⟩
  have hi : Function.Injective idx := by
    intro i j h
    exact Subtype.ext (Fin.ext (congrArg (fun i : Fin d => i.val) h))
  have hsub : Orthonormal ℂ (s.domRestrict rowOn) := by
    have h := ho.comp idx hi
    convert h using 1
    ext i
    exact dite_eq_left i.prop
  obtain ⟨basis, hb⟩ := hsub.exists_orthonormalBasis_extension_of_card_eq
    (by simpa using hn)
  refine ⟨basis, fun i => (hb _ i.isLt).trans ?_⟩
  simp [rowOn, i.isLt]

/-- Extend the image of an orthonormal basis under a conjugate-linear isometry. -/
theorem exists_conjugateIsometry_rowBasis [FiniteDimensional ℂ H]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] {d n : ℕ}
    (hd : d ≤ n) (hn : finrank ℂ H = n)
    (bY : OrthonormalBasis (Fin d) ℂ Y) (s : Y →ₛₗ[starRingEnd ℂ] H)
    (hs : ∀ y z : Y, ⟪s y, s z⟫_ℂ = ⟪z, y⟫_ℂ) :
    ∃ bH : OrthonormalBasis (Fin n) ℂ H, ∀ i, bH (Fin.castLE hd i) = s (bY i) := by
  apply exists_orthonormalBasis_extending_fin hd hn
  rw [orthonormal_iff_ite]
  intro i j
  rw [hs, (orthonormal_iff_ite.mp bY.orthonormal)]
  simp [eq_comm]

/-- Express a bilinear pairing realized by an inner product as a row
compression of the two linear maps that enter that inner product. -/
theorem bilinearPairing_matrices_of_rowBasis
    {Y V C : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C]
    {d n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hd : d ≤ n) (bH : OrthonormalBasis (Fin n) ℂ H)
    (bY : OrthonormalBasis (Fin d) ℂ Y) (bV : OrthonormalBasis ι ℂ V)
    (bC : OrthonormalBasis κ ℂ C) (s : Y →ₛₗ[starRingEnd ℂ] H)
    (hbH : ∀ i, bH (Fin.castLE hd i) = s (bY i))
    (J : V →ₗᵢ[ℂ] C) (P : C →ₗ[ℂ] H) (B : V →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    {a : ℂ} (ha : a ≠ 0)
    (hperiod : ∀ (z : V) (y : Y), B z y = a * ⟪s y, P (J z)⟫_ℂ) :
    let PM := P.toMatrix bC.toBasis bH.toBasis
    let JM := J.toLinearMap.toMatrix bV.toBasis bC.toBasis
    JMᴴ * JM = 1 ∧
    ∀ i j, (PM * JM) (Fin.castLE hd i) j = a⁻¹ * B (bV j) (bY i) := by
  constructor
  · have hg := Matrix.gram_eq_conjTranspose_mul bC (fun j => J (bV j))
    have hj : Orthonormal ℂ (fun j => J (bV j)) := bV.orthonormal.comp_linearIsometry J
    rw [Matrix.gram_eq_one_iff_orthonormal.mpr hj] at hg
    have hJM : J.toLinearMap.toMatrix bV.toBasis bC.toBasis =
        Matrix.of (fun i j => bC.repr (J (bV j)) i) := by
      ext i j
      simp [LinearMap.toMatrix_apply]
    rw [hJM]
    exact hg.symm
  · intro i j
    rw [← LinearMap.toMatrix_comp, LinearMap.toMatrix_apply]
    change bH.repr (P (J (bV j))) (Fin.castLE hd i) = _
    rw [OrthonormalBasis.repr_apply_apply, hbH, hperiod,
      ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-- The matrix of a scaled adjoint composition in orthonormal coordinates. -/
theorem toMatrix_smul_adjoint_comp [FiniteDimensional ℂ H]
    {C C' : Type*} [NormedAddCommGroup C] [InnerProductSpace ℂ C] [FiniteDimensional ℂ C]
    [NormedAddCommGroup C'] [InnerProductSpace ℂ C'] [FiniteDimensional ℂ C']
    {n : ℕ} {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (bH : OrthonormalBasis (Fin n) ℂ H)
    (bC : OrthonormalBasis κ ℂ C) (bC' : OrthonormalBasis κ' ℂ C')
    (P : C →ₗ[ℂ] H) (P' : C' →ₗ[ℂ] H) (c : ℂ) :
    (c • (P.adjoint.comp P')).toMatrix bC'.toBasis bC.toBasis =
      c • ((P.toMatrix bC.toBasis bH.toBasis)ᴴ * P'.toMatrix bC'.toBasis bH.toBasis) := by
  rw [map_smul, LinearMap.toMatrix_comp bC'.toBasis bH.toBasis bC.toBasis,
    LinearMap.toMatrix_adjoint]

end Utilities
