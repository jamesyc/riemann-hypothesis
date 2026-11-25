module

public import Riemann.SelmerStickelbergerCongruence
public import Utilities.ArtinIdeal
import Riemann.SelmerArtinRestriction
import Riemann.SelmerFiniteDescent
import Riemann.SelmerKummerRestriction
import Utilities.CyclotomicLayer
import Utilities.CyclotomicRestriction
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

@[expose] public section

open Utilities NumberField IsCyclotomicExtension
open scoped IsMulCommutative

namespace Riemann

/-- At any multiple of the conductor, cyclotomic restriction to the host
is the conductor map on the reduced residue. -/
theorem exists_selmerHostCyclotomicLayer (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (M : ℕ) [NeZero M] (h : selmerHostConductor target e q d ∣ M) :
    let F := selmerHostField target e q d
    letI := selmerHostField_isAbelianGalois target e q d
    ∃ E : IntermediateField F (AlgebraicClosure F), ∃ _ : IsCyclotomicExtension {M} ℚ E,
      letI : NumberField E := IsCyclotomicExtension.numberField {M} ℚ E
      letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {M} ℚ E
      ∀ s : Gal(E/ℚ), s.restrictNormal F =
        selmerHostConductorGalMap target e q d (ZMod.unitsMap h (Rat.galEquivZMod M E s)) := by
  let F := selmerHostField target e q d
  let f := selmerHostConductor target e q d
  let K := CyclotomicField f ℚ
  let j := selmerHostConductorEmbedding target e q d
  let _ : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let _ : IsCyclotomicExtension {f} ℚ K := CyclotomicField.isCyclotomicExtension f ℚ
  let _ : NumberField K := IsCyclotomicExtension.numberField {f} ℚ K
  let _ : Algebra F K := j.toRingHom.toAlgebra
  let _ : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  exact exists_cyclotomicLayer_restrictNormal F K f M h

set_option maxHeartbeats 500000 in
/-- Principal-ideal reciprocity supplies the finite-level restriction
vanishing required for the exceptional-prime Selmer estimate. -/
theorem selmerTwistedWeightOneRestrictionVanishing_of_principalReciprocity
    (h : HasTotallyComplexUnramifiedPrincipalReciprocity) :
    HasSelmerTwistedWeightOneRestrictionVanishing := by
  intro target _ e q d _ _ i _
  dsimp only
  intro ℓ _ hodd _ x m₀
  let F := selmerHostField target e q d
  let Ω := AlgebraicClosure F
  let _ : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  let _ : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω
  let f := selmerHostConductor target e q d
  let N := f * ℓ
  have hf : 0 < f := selmerHostConductor_pos target e q d
  have hp : ℓ.Prime := Fact.out
  let _ : NeZero N := ⟨mul_ne_zero hf.ne' hp.ne_zero⟩
  obtain ⟨r, c, hcx, hc, hdescent⟩ :=
    exists_finiteAbelian_unramified_tateSelmerRestriction F ℓ i x.val
  let m := max m₀ r
  refine ⟨m, le_max_left _ _, ?_⟩
  let M := N * ℓ ^ m
  let _ : NeZero M := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hp.ne_zero)⟩
  have hN : N ∣ M := dvd_mul_right _ _
  have hfN : f ∣ N := dvd_mul_right _ _
  have hfM : f ∣ M := hfN.trans hN
  have hr : ℓ ^ r ∣ M := (pow_dvd_pow ℓ (le_max_right m₀ r)).trans (dvd_mul_left _ _)
  obtain ⟨E, hcyclo, hres⟩ := exists_selmerHostCyclotomicLayer target e q d M hfM
  let _ : IsCyclotomicExtension {M} ℚ E := hcyclo
  let _ : NumberField E := IsCyclotomicExtension.numberField {M} ℚ E
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {M} ℚ E
  let _ : FiniteDimensional F E := FiniteDimensional.right ℚ F E
  have hE (ζ : Ω) (hζ : ζ ^ (ℓ ^ r) = 1) : ζ ∈ E :=
    mem_cyclotomicLayer_of_pow_eq_one M E (by
      obtain ⟨k, hk⟩ := hr
      rw [hk, pow_mul, hζ, one_pow])
  obtain ⟨T, hT, hAb, φ, hφ, hlocal⟩ := hdescent E hE
  let _ : NumberField T := NumberField.of_module_finite E T
  let _ : IsGalois ℚ T := hT
  let _ : IsAbelianGalois E T := hAb
  have hI (P : Ideal (𝓞 T)) [P.IsPrime] (hP : P ≠ ⊥) (t : Gal(T/E))
      (ht : t ∈ P.inertia Gal(T/E)) : t = 1 :=
    hlocal P hP t (Or.inl ht)
  have hℓM : ℓ ≤ M := (Nat.le_mul_of_pos_left ℓ hf).trans
    (Nat.le_of_dvd (NeZero.pos M) hN)
  have hM : 2 < M := (show 2 < ℓ by have := hp.two_le; omega).trans_le hℓM
  let _ : IsTotallyComplex E := Rat.isTotallyComplex E hM
  choose lift hlift using fun b : (ZMod M)ˣ =>
    AlgEquiv.restrictNormalHom_surjective Ω ((Rat.galEquivZMod M E).symm b)
  let π := (selmerStickelbergerGalMap target e q d ℓ).comp (ZMod.unitsMap hN)
  have hπ (b : (ZMod M)ˣ) : (π b)⁻¹ = (lift b).restrictNormal F := by
    let s : Gal(E/ℚ) := (lift b).restrictNormal E
    have hb : Rat.galEquivZMod M E s = b :=
      (congrArg (Rat.galEquivZMod M E) (hlift b)).trans (MulEquiv.apply_symm_apply _ _)
    calc
      (π b)⁻¹ = selmerHostConductorGalMap target e q d (ZMod.unitsMap hfN (ZMod.unitsMap hN b)) :=
        inv_selmerStickelbergerGalMap_apply target e q d ℓ (ZMod.unitsMap hN b)
      _ = selmerHostConductorGalMap target e q d (ZMod.unitsMap hfM b) :=
        congrArg (selmerHostConductorGalMap target e q d)
          (DFunLike.congr_fun (ZMod.unitsMap_comp hfN hN) b)
      _ = s.restrictNormal F := by rw [hres s, hb]
      _ = (lift b).restrictNormal F :=
        (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F E (lift b)).symm
  let a := 2 * N + 1
  have haN : a.Coprime N := by simp [a]
  have ha : a.Coprime M := haN.mul_right ((haN.coprime_dvd_right (dvd_mul_left ℓ f)).pow_right m)
  intro σ hfix
  have hσ : (show Gal(Ω/F) from σ.val) ∈ E.fixingSubgroup :=
    mem_fixingSubgroup_of_fixes_cyclotomicLayer M E _ (fun ζ hζ =>
      algEquiv_fixes_root_mul_prime_pow (NeZero.ne N) hp _ hfix
        (fun r _ hz => fixes_primePowRoots_of_mem_ker_padicCyclotomicUnitsMap F ℓ σ.property r hz) m hζ)
  let g := E.fixingSubgroupEquiv ⟨σ.val, hσ⟩
  have hprincip := h E T hI
  have hz := padicTateSelmerRestriction_twistedWeightOne_eq_zero_of_artin F ℓ i
    M E T r hr c hc φ hφ π lift hlift hπ a ha σ g rfl hprincip hI
  rw [hcx] at hz
  exact hz

/-- The two arithmetic inputs still needed for Theorem 17.12(II). -/
theorem numberField_selmer_minus_estimate_of_comparison_principalReciprocity
    (hBernoulli : HasSelmerBernoulliValuationComparison)
    (hReciprocity : HasTotallyComplexUnramifiedPrincipalReciprocity) : HasSelmerMinusEstimate :=
  numberField_selmer_minus_estimate_of_comparison_exponent hBernoulli
    (selmerStickelbergerExponentEstimate_of_higherStickelberger
      (selmerHigherStickelbergerAnnihilation_of_twistedWeightOneRestriction
        (selmerTwistedWeightOneRestrictionVanishing_of_principalReciprocity hReciprocity)))

end Riemann
