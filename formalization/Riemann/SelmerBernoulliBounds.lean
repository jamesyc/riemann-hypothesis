module

public import Riemann.SelmerMinusBounds
public import Utilities.GeneralizedBernoulliValuation

@[expose] public section

open Utilities
open scoped BigOperators

namespace Riemann

/-- The cyclotomic Galois group at the conductor restricts to the host. -/
noncomputable def selmerHostConductorGalMap (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) :
    (ZMod (selmerHostConductor target e q d))ˣ →*
      (selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d) := by
  let f := selmerHostConductor target e q d
  let E := selmerHostField target e q d
  let K := CyclotomicField f ℚ
  let j := selmerHostConductorEmbedding target e q d
  let _ : Algebra E K := j.toRingHom.toAlgebra
  let _ : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let _ : NeZero (f : ℚ) := ⟨by exact_mod_cast NeZero.ne f⟩
  let _ : IsCyclotomicExtension {f} ℚ K := CyclotomicField.isCyclotomicExtension f ℚ
  exact (AlgEquiv.restrictNormalHom E).comp
    (IsCyclotomicExtension.Rat.galEquivZMod f K).symm.toMonoidHom

theorem selmerHostConductorGalMap_surjective (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) : Function.Surjective (selmerHostConductorGalMap target e q d) := by
  unfold selmerHostConductorGalMap
  let f := selmerHostConductor target e q d
  let E := selmerHostField target e q d
  let K := CyclotomicField f ℚ
  let j := selmerHostConductorEmbedding target e q d
  let _ : Algebra E K := j.toRingHom.toAlgebra
  let _ : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let _ : NeZero (f : ℚ) := ⟨by exact_mod_cast NeZero.ne f⟩
  let _ : IsCyclotomicExtension {f} ℚ K := CyclotomicField.isCyclotomicExtension f ℚ
  let _ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {f} ℚ K
  exact (AlgEquiv.restrictNormalHom_surjective _).comp (MulEquiv.surjective _)

theorem selmerHostConductorGalMap_ker_index (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) :
    (selmerHostConductorGalMap target e q d).ker.index =
      Module.finrank ℚ (selmerHostField target e q d) := by
  let _ := selmerHostField_isAbelianGalois target e q d
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (selmerHostConductorGalMap target e q d)
    (selmerHostConductorGalMap_surjective target e q d)).toEquiv).trans
      (IsGalois.card_aut_eq_finrank ℚ (selmerHostField target e q d))

theorem selmerHostConductorGalMap_neg_one_eq_conjugation (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ι : selmerHostField target e q d →ₐ[ℚ] ℂ) :
    letI := selmerHostField_isAbelianGalois target e q d
    selmerHostConductorGalMap target e q d (-1) =
      algEquiv_complexConjugation (selmerHostField target e q d) ι := by
  let f := selmerHostConductor target e q d
  let E := selmerHostField target e q d
  let K := CyclotomicField f ℚ
  let j := selmerHostConductorEmbedding target e q d
  let _ : Algebra E K := j.toRingHom.toAlgebra
  let _ : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let _ : NeZero (f : ℚ) := ⟨by exact_mod_cast NeZero.ne f⟩
  let _ : IsCyclotomicExtension {f} ℚ K := CyclotomicField.isCyclotomicExtension f ℚ
  let _ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {f} ℚ K
  let _ : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {f} ℚ K
  let _ : FiniteDimensional E K := FiniteDimensional.right ℚ E K
  obtain ⟨ιK, hιK⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := ℚ) (L := E) (M := ℂ) (E := K) ι
  let σ := algEquiv_complexConjugation K ιK
  have hneg := cyclotomicGalEquivZMod_eq_neg_one_of_embedding_conj f K ιK σ
    (algEquiv_complexConjugation_apply K ιK)
  change ((IsCyclotomicExtension.Rat.galEquivZMod f K).symm (-1)).restrictNormal E =
    algEquiv_complexConjugation E ι
  rw [← hneg, MulEquiv.symm_apply_apply]
  have hι (x : E) : ιK (algebraMap E K x) = ι x := DFunLike.congr_fun hιK x
  apply AlgEquiv.ext
  intro x
  apply ι.injective
  calc
    ι (σ.restrictNormal E x) = ιK (algebraMap E K (σ.restrictNormal E x)) := (hι _).symm
    _ = ιK (σ (algebraMap E K x)) := congrArg ιK (σ.restrictNormal_commutes E x)
    _ = ι (algEquiv_complexConjugation E ι x) := by
      rw [algEquiv_complexConjugation_apply, hι, algEquiv_complexConjugation_apply]

/-- The character kernels for the minus eigenspace at twist `i`. -/
noncomputable def selmerMinusBernoulliKernels (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (i : ℕ) :
    Set (Subgroup (ZMod (selmerHostConductor target e q d))ˣ) :=
  {H | (selmerHostConductorGalMap target e q d).ker ≤ H ∧
    ((-1 : (ZMod (selmerHostConductor target e q d))ˣ) ∈ H ↔ Even (i + 1))}

/-- The arithmetic comparison behind the prime-to-degree minus estimate.
At each odd prime, compare the actual Selmer length with the normalized
Bernoulli factors of a subset of the parity-appropriate host characters. -/
def HasSelmerBernoulliValuationComparison : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i ≥ 1,
      let E := selmerHostField target e q d
      let f := selmerHostConductor target e q d
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ¬ ℓ ∣ Module.finrank ℚ E →
        let lengths := numberFieldSelmerSignLengths false E
        lengths ℓ i ≠ ⊤ ∧
        ∃ T : Finset (DirichletCharacter (PadicAlgCl ℓ) f),
          (∀ χ ∈ T, χ ∈ dirichletCharactersWithKernelIn (PadicAlgCl ℓ)
            (selmerMinusBernoulliKernels target e q d i)) ∧
          Real.log (ℓ : ℝ) * (((lengths ℓ i).untopD 0 : ℕ) : ℝ) ≤
            ∑ χ ∈ T, -Real.log ‖(generalizedBernoulliDenominator f (i + 1) : PadicAlgCl ℓ) *
              primitiveBernoulliValue (i + 1) χ‖

/-- The common integer Bernoulli product converts the local arithmetic
comparisons into the global prime-to-degree sum bound. -/
theorem selmerBernoulliMinusEstimates_of_valuationComparison
    (h : HasSelmerBernoulliValuationComparison) : HasSelmerBernoulliMinusEstimates := by
  intro target hprimitive e q d he hpair i hi
  let E := selmerHostField target e q d
  let f := selmerHostConductor target e q d
  let P := selmerMinusBernoulliKernels target e q d i
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  have hi' : 2 ≤ i + 1 := by omega
  obtain ⟨w, hw, hlocal⟩ := exists_weighted_padic_bernoulli_bounds hi' P
    (fun _ hH => hH.2)
  have hcard := (ncard_dirichletCharactersWithKernelIn_le_index P
    (selmerHostConductorGalMap target e q d).ker (fun _ hH => hH.1)).trans_eq
    (selmerHostConductorGalMap_ker_index target e q d)
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast selmerHostConductor_pos target e q d
  have hfact : (1 : ℝ) ≤ (i + 1).factorial := by exact_mod_cast Nat.factorial_pos (i + 1)
  have hheight : 0 ≤ Real.log (generalizedBernoulliHeightBound f (i + 1)) := by
    apply Real.log_nonneg
    unfold generalizedBernoulliHeightBound
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hf)) hfact
  have hcomp := h target hprimitive e q d he hpair i hi
  refine ⟨fun ℓ hℓ hodd hdiv => ?_, fun S hS => ?_⟩
  · let : Fact ℓ.Prime := ⟨hℓ⟩
    exact (hcomp ℓ hodd hdiv).1
  · calc
      _ ≤ ∑ ℓ ∈ S, (w ℓ : ℝ) * Real.log ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        obtain ⟨hprime, hodd, hdiv⟩ := hS ℓ hℓ
        let : Fact ℓ.Prime := ⟨hprime⟩
        obtain ⟨T, hT, hTbound⟩ := (hcomp ℓ hodd hdiv).2
        exact hTbound.trans (hlocal ℓ T hT)
      _ ≤ _ := (hw S (fun ℓ hℓ => (hS ℓ hℓ).1)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hheight)

end Riemann
