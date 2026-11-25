module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Utilities.OrthonormalCompression
public import Utilities.LatticeIntegrality

@[expose] public section

open IsDedekindDomain Module TensorProduct Utilities
open scoped TensorProduct InnerProductSpace Matrix

namespace Riemann

variable {K V Y : Type*} [Field K] [Algebra K ℂ]
  [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module K Y]

/-- Scalar extension of the field-valued bilinear period pairing at a complex
embedding. The algebra structure on `ℂ` specifies the embedding. -/
noncomputable def besselPeriodAt (B : V →ₗ[K] Y →ₗ[K] K) :
    (ℂ ⊗[K] V) →ₗ[ℂ] (ℂ ⊗[K] Y) →ₗ[ℂ] ℂ :=
  let ψ : ℂ →ₗ[ℂ] Module.Dual K Y →ₗ[K] Module.Dual ℂ (ℂ ⊗[K] Y) :=
    { toFun a := a • Module.Dual.baseChange ℂ
      map_add' a b := add_smul a b _
      map_smul' a b := mul_smul a b _ }
  (AlgebraTensorModule.lift ψ).comp (B.baseChange ℂ)

@[simp] theorem besselPeriodAt_tmul (B : V →ₗ[K] Y →ₗ[K] K)
    (z : V) (y : Y) (a b : ℂ) :
    besselPeriodAt B (a ⊗ₜ[K] z) (b ⊗ₜ[K] y) =
      a * b * algebraMap K ℂ (B z y) := by
  simp [besselPeriodAt, Algebra.smul_def, mul_comm, mul_assoc]

/-- The matrix of the specialized pairing is the entrywise embedding of the
field matrix in the scalar extensions of its original bases. -/
theorem besselPeriodAt_toMatrix_baseChange
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : V →ₗ[K] Y →ₗ[K] K) (v : Basis ι K V) (y : Basis κ K Y) :
    (besselPeriodAt B).toMatrix (v.baseChange ℂ) (y.baseChange ℂ).dualBasis =
      (B.toMatrix v y.dualBasis).map (algebraMap K ℂ) := by
  ext i j
  simp [LinearMap.toMatrix_apply]

/-- For arbitrary complex bases of the two scalar extensions, the pairing
matrix is obtained by invertible row and column changes from the embedded
field matrix. -/
theorem besselPeriodAt_toMatrix_changeBasis
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : V →ₗ[K] Y →ₗ[K] K) (v : Basis ι K V) (y : Basis κ K Y)
    (v' : Basis ι ℂ (ℂ ⊗[K] V)) (y' : Basis κ ℂ (ℂ ⊗[K] Y)) :
    let L := y'.dualBasis.toMatrix (y.baseChange ℂ).dualBasis
    let R := (v.baseChange ℂ).toMatrix v'
    IsUnit L ∧ IsUnit R ∧
      (besselPeriodAt B).toMatrix v' y'.dualBasis =
        L * (B.toMatrix v y.dualBasis).map (algebraMap K ℂ) * R := by
  dsimp only
  let : Invertible (y'.dualBasis.toMatrix (y.baseChange ℂ).dualBasis) :=
    y'.dualBasis.invertibleToMatrix (y.baseChange ℂ).dualBasis
  let : Invertible ((v.baseChange ℂ).toMatrix v') := (v.baseChange ℂ).invertibleToMatrix v'
  refine ⟨isUnit_of_invertible _, isUnit_of_invertible _, ?_⟩
  rw [← besselPeriodAt_toMatrix_baseChange, ← LinearMap.toMatrix_id_eq_basis_toMatrix,
    ← LinearMap.toMatrix_id_eq_basis_toMatrix,
    ← LinearMap.toMatrix_comp (v.baseChange ℂ) (y.baseChange ℂ).dualBasis y'.dualBasis,
    ← LinearMap.toMatrix_comp v' (v.baseChange ℂ) y'.dualBasis]
  simp

/-- Lemma 13.14 in the matrices over the original coefficient field, given
the complex Bessel realization at the chosen embedding. -/
theorem besselPeriodAt_compression
    {H C Vv Yv : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C]
    [NormedAddCommGroup Vv] [InnerProductSpace ℂ Vv]
    [NormedAddCommGroup Yv] [InnerProductSpace ℂ Yv]
    {d n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hd : d ≤ n) (bH : OrthonormalBasis (Fin n) ℂ H)
    (v : Basis ι K V) (y : Basis (Fin d) K Y)
    (vIso : (ℂ ⊗[K] V) ≃ₗ[ℂ] Vv) (yIso : (ℂ ⊗[K] Y) ≃ₗ[ℂ] Yv)
    (bY : OrthonormalBasis (Fin d) ℂ Yv)
    (bV : OrthonormalBasis ι ℂ Vv) (bC : OrthonormalBasis κ ℂ C)
    (row : Yv →ₛₗ[starRingEnd ℂ] H)
    (hbH : ∀ i, bH (Fin.castLE hd i) = row (bY i))
    (J : Vv →ₗᵢ[ℂ] C) (P : C →ₗ[ℂ] H) (B : V →ₗ[K] Y →ₗ[K] K)
    {a : ℂ} (ha : a ≠ 0)
    (hperiod : ∀ z y, besselPeriodAt B (vIso.symm z) (yIso.symm y) = a * ⟪row y, P (J z)⟫_ℂ) :
    let PM := P.toMatrix bC.toBasis bH.toBasis
    let JM := J.toLinearMap.toMatrix bV.toBasis bC.toBasis
    let A := (B.toMatrix v y.dualBasis).map (algebraMap K ℂ)
    ∃ (L : Matrix (Fin d) (Fin d) ℂ) (R : Matrix ι ι ℂ),
      IsUnit L ∧ IsUnit R ∧ JMᴴ * JM = 1 ∧
      (PM * JM).submatrix (Fin.castLE hd) id = a⁻¹ • (L * A * R) := by
  let Bv := (besselPeriodAt B).compl₁₂ vIso.symm.toLinearMap yIso.symm.toLinearMap
  obtain ⟨hJ, hrow⟩ :=
    bilinearPairing_matrices_of_rowBasis hd bH bY bV bC row hbH J P Bv ha hperiod
  obtain ⟨hL, hR, hB⟩ :=
    besselPeriodAt_toMatrix_changeBasis B v y (bV.toBasis.map vIso.symm) (bY.toBasis.map yIso.symm)
  refine ⟨_, _, hL, hR, hJ, ?_⟩
  rw [← hB]
  ext i j
  simpa [Bv, LinearMap.toMatrix_apply] using hrow i j

/-- At a complex embedding the integral restriction from local divisibility
realizes the same period pairing. This is the compatibility between the
integrality of the period map and the Bessel identity used in Theorem 13.15. -/
theorem exists_integralBesselPeriod_of_local_divisibility
    {R H C : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
    [Module R V] [IsScalarTower R K V] [Module R Y] [IsScalarTower R K Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C]
    (N : Submodule R V) (M : Submodule R Y) (B : V →ₗ[K] Y →ₗ[K] K)
    (N₀ : HeightOneSpectrum R → Set V) (π : HeightOneSpectrum R → K)
    (k : HeightOneSpectrum R → ℕ) (hπ : ∀ v, π v ≠ 0)
    (hval : ∀ (v : HeightOneSpectrum R) (z : V), z ∈ N₀ v → ∀ y : M,
      v.valuation K (B z y) ≤ v.valuation K (π v) ^ k v)
    (hrescale : ∀ (v : HeightOneSpectrum R) (z : N), ∃ z₀ ∈ N₀ v,
      (z : V) = (π v ^ k v)⁻¹ • z₀)
    (row : (ℂ ⊗[K] Y) →ₛₗ[starRingEnd ℂ] H)
    (J : (ℂ ⊗[K] V) →ₗ[ℂ] C) (P : C →ₗ[ℂ] H) (a : ℂ)
    (hperiod : ∀ z y, besselPeriodAt B z y = a * ⟪row y, P (J z)⟫_ℂ) :
    ∃ B₀ : N →ₗ[R] Module.Dual R M, ∀ (z : N) (y : M),
      algebraMap R K (B₀ z y) = B z y ∧
      algebraMap K ℂ (algebraMap R K (B₀ z y)) =
        a * ⟪row (1 ⊗ₜ[K] (y : Y)), P (J (1 ⊗ₜ[K] (z : V)))⟫_ℂ := by
  obtain ⟨B₀, hB₀⟩ :=
    Utilities.exists_integralDualMap_of_local_divisibility N M B N₀ π k hπ hval hrescale
  refine ⟨B₀, fun z y => ⟨hB₀ z y, ?_⟩⟩
  simpa only [besselPeriodAt_tmul, one_mul, hB₀] using
    hperiod (1 ⊗ₜ[K] (z : V)) (1 ⊗ₜ[K] (y : Y))

end Riemann
