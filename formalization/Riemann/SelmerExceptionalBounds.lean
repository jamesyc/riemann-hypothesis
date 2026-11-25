module

public import Riemann.SelmerBernoulliBounds
public import Utilities.ModuleLengthBounds
public import Utilities.SelmerKernelRestrictions
public import Utilities.SelmerKernelTorsion
import Mathlib.Analysis.Complex.ExponentialBounds
import Utilities.PadicAnnihilator

@[expose] public section

open Utilities
open scoped NumberField

namespace Riemann

/-- The parity-adjusted eigenvalue of complex conjugation. -/
def selmerSignScalar {R : Type*} [Ring R] (positive : Bool) (i : ℕ) : R :=
  if positive then (-1 : R) ^ i else -((-1 : R) ^ i)

@[simp]
theorem map_selmerSignScalar {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (positive : Bool) (i : ℕ) :
    f (selmerSignScalar positive i) = selmerSignScalar positive i := by
  cases positive <;> simp [selmerSignScalar]

/-- The actual parity-adjusted eigenspace, before taking its length. -/
noncomputable abbrev numberFieldSelmerSignPart (positive : Bool) (F : Type) [Field F] [NumberField F]
    [Normal ℚ F] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :=
  letI : IsAlgClosure ℚ (AlgebraicClosure F) := IsAlgClosure.ofAlgebraic ℚ F _
  (numberFieldSelmerConjugation F ℓ i IsAlgClosed.lift).eigenspace (selmerSignScalar positive i)

noncomputable abbrev numberFieldSelmerMinusPart (F : Type) [Field F] [NumberField F]
    [Normal ℚ F] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :=
  numberFieldSelmerSignPart false F ℓ i

theorem numberFieldSelmerSignLengths_eq_moduleLength (positive : Bool) (F : Type)
    [Field F] [NumberField F] [hF : Normal ℚ F] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    numberFieldSelmerSignLengths positive F ℓ i =
      Module.length ℤ_[ℓ] (numberFieldSelmerSignPart positive F ℓ i) := by
  rw [numberFieldSelmerSignLengths, dite_eq_left hF]
  rw [numberFieldSelmerSignLength, dite_eq_left (Fact.out : ℓ.Prime)]
  change primaryCardLength ℓ (numberFieldSelmerSignPart positive F ℓ i) = _
  exact primaryCardLength_eq_moduleLength ℓ (numberFieldSelmerSignPart positive F ℓ i)

theorem numberFieldSelmerSignLengths_false_eq_moduleLength (F : Type)
    [Field F] [NumberField F] [Normal ℚ F] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    numberFieldSelmerSignLengths false F ℓ i =
      Module.length ℤ_[ℓ] (numberFieldSelmerMinusPart F ℓ i) :=
  numberFieldSelmerSignLengths_eq_moduleLength false F ℓ i

theorem numberFieldRelaxedSelmer_torsionLength_le_residualCocycles (F : Type)
    [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    let A := padicTateTwist F ℓ i
    let G := numberFieldRelaxedSelmerRestrictions F ℓ
    Module.length ℤ_[ℓ] (Submodule.torsionBy ℤ_[ℓ] (A.selmerKernel G) (ℓ : ℤ_[ℓ])) ≤
      Module.length ℤ_[ℓ]
        (Submodule.torsionBy ℤ_[ℓ] (A.locallyTrivialCocycles₁ G) (ℓ : ℤ_[ℓ])) := by
  exact (padicTateTwist F ℓ i).module_length_torsionBy_selmerKernel_le _ _
    (padicTateQuotient_smul_surjective (ℓ : ℤ_[ℓ]) (by
      exact_mod_cast (Fact.out : ℓ.Prime).ne_zero))

/-- The Stickelberger annihilation estimate needed at the exceptional primes. -/
def HasSelmerStickelbergerExponentEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
      ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i : ℕ, 1 ≤ i →
        let E := selmerHostField target e q d
        let n := Module.finrank ℚ E
        let f := selmerHostConductor target e q d
        letI := selmerHostField_isAbelianGalois target e q d
        ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ℓ ∣ n →
          ∃ r : ℕ, (r : ℝ) * Real.log ℓ ≤ C * n * ((i : ℝ) + 1) * Real.log ((i : ℝ) * ℓ * f) ∧
            ∀ a : numberFieldSelmerMinusPart E ℓ i, (ℓ : ℤ_[ℓ]) ^ r • a = 0

/-- An integer annihilator of bounded size on the actual odd minus part
is sufficient for the Stickelberger exponent estimate. -/
def HasSelmerIntegerAnnihilatorEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
      ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i : ℕ, 1 ≤ i →
        let E := selmerHostField target e q d
        let n := Module.finrank ℚ E
        let f := selmerHostConductor target e q d
        letI := selmerHostField_isAbelianGalois target e q d
        ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ℓ ∣ n →
          ∃ X : ℤ, X ≠ 0 ∧ Real.log (X.natAbs : ℝ) ≤ C * n * ((i : ℝ) + 1) * Real.log ((i : ℝ) * ℓ * f) ∧
            ∀ a : numberFieldSelmerMinusPart E ℓ i, (X : ℤ_[ℓ]) • a = 0

theorem selmerStickelbergerExponentEstimate_of_integerAnnihilator
    (h : HasSelmerIntegerAnnihilatorEstimate) : HasSelmerStickelbergerExponentEstimate := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun target hprimitive e q d he hpair i hi ℓ hℓ hodd hdvd => ?_⟩
  obtain ⟨X, hX, hlog, hkill⟩ := h target hprimitive e q d he hpair i hi ℓ hodd hdvd
  let E := selmerHostField target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let M := ↥(numberFieldSelmerMinusPart E ℓ i)
  obtain ⟨r, hr, hrkill⟩ := exists_padic_prime_pow_smul_eq_zero_of_intCast ℓ (M := M) X hX hkill
  exact ⟨r, hr.trans hlog, hrkill⟩

/-- Bound the first torsion layer of the relaxed global restriction kernel. -/
def HasSelmerRelaxedTorsionRankEstimate : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i : ℕ, 1 ≤ i →
      let E := selmerHostField target e q d
      let n := Module.finrank ℚ E
      let f := selmerHostConductor target e q d
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ℓ ∣ n →
        let V := numberFieldRelaxedSelmerKernel E ℓ i
        ∃ g : ℕ, Module.length ℤ_[ℓ] (Submodule.torsionBy ℤ_[ℓ] V (ℓ : ℤ_[ℓ])) ≤ g ∧
          (g : ℝ) ≤ 8 * ℓ * n * Real.log ((ℓ : ℝ) * f)

/-- Convert the Kummer estimate `ℓ^(2m) h` and the logarithmic class-number
bound into the rank estimate, where `m` is the degree after adjoining `μℓ`. -/
theorem exists_padic_torsionRank_of_cardBound (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Type*) [AddCommGroup M] [Module ℤ_[ℓ] M] [Finite M] {m n f h : ℕ}
    (hf : 0 < f) (hh : 0 < h) (hm : m ≤ ℓ * n)
    (hcard : Nat.card M ≤ ℓ ^ (2 * m) * h)
    (hlogh : Real.log (h : ℝ) ≤ 3 * m * Real.log ((ℓ : ℝ) * f)) :
    ∃ g : ℕ, Module.length ℤ_[ℓ] M ≤ g ∧
      (g : ℝ) ≤ 8 * ℓ * n * Real.log ((ℓ : ℝ) * f) := by
  have hfinite := (padicModule_isFiniteLength_iff_finite ℓ M).mpr inferInstance
  let g := (Module.length ℤ_[ℓ] M).toNat
  have hg : Module.length ℤ_[ℓ] M = g :=
    (ENat.natCast_toNat (Module.length_ne_top_iff.mpr hfinite)).symm
  refine ⟨g, hg.le, ?_⟩
  have hcardR : (ℓ : ℝ) ^ g ≤ (ℓ : ℝ) ^ (2 * m) * h := by
    exact_mod_cast (card_eq_padic_prime_pow_of_isFiniteLength ℓ M hfinite).symm.trans_le hcard
  have hL := Real.log_le_log (by have := (Fact.out : ℓ.Prime).pos; positivity) hcardR
  rw [Real.log_mul (by have := (Fact.out : ℓ.Prime).pos; positivity)
    (by exact_mod_cast hh.ne'), Real.log_pow, Real.log_pow] at hL
  push_cast at hL
  have hℓ : (2 : ℝ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).two_le
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hℓ₀ : (0 : ℝ) < ℓ := (by norm_num : (0 : ℝ) < 2).trans_le hℓ
  have hlogℓ : Real.log (ℓ : ℝ) ≤ Real.log ((ℓ : ℝ) * f) :=
    Real.log_le_log hℓ₀ (le_mul_of_one_le_right hℓ₀.le hfR)
  have hlog₀ : 0 ≤ Real.log ((ℓ : ℝ) * f) :=
    (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans hℓ)).trans hlogℓ
  have hlog2 : (5 : ℝ) / 8 ≤ Real.log (ℓ : ℝ) :=
    (by linarith [Real.log_two_gt_d9] : (5 : ℝ) / 8 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hℓ)
  have hmR : (m : ℝ) ≤ ℓ * n := by exact_mod_cast hm
  have hchain : (5 : ℝ) / 8 * g ≤ 5 * (ℓ : ℝ) * n * Real.log ((ℓ : ℝ) * f) := calc
    _ ≤ (g : ℝ) * Real.log ℓ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlog2 (Nat.cast_nonneg g)
    _ ≤ 2 * m * Real.log ℓ + Real.log (h : ℝ) := hL
    _ ≤ 5 * m * Real.log ((ℓ : ℝ) * f) := by
      have hh' := mul_le_mul_of_nonneg_left hlogℓ (show (0 : ℝ) ≤ 2 * m by positivity)
      linarith only [hh', hlogh]
    _ ≤ _ := by
      rw [mul_assoc (5 : ℝ) (ℓ : ℝ) (n : ℝ)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmR (by norm_num)) hlog₀
  linarith only [hchain]

/-- An annihilating power and a bound on the first torsion layer yield the
exact exceptional-prime bound in Theorem 17.12(II). -/
theorem selmerStickelbergerMinusEstimates_of_exponent_rank
    (hExp : HasSelmerStickelbergerExponentEstimate) (hRank : HasSelmerRelaxedTorsionRankEstimate) :
    HasSelmerStickelbergerMinusEstimates := by
  obtain ⟨C, hC, hExp⟩ := hExp
  refine ⟨8 * C, by positivity, fun target hprimitive e q d he hpair i hi ℓ hℓ hodd hdiv => ?_⟩
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let E := selmerHostField target e q d
  let n := Module.finrank ℚ E
  let f := selmerHostConductor target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : IsAlgClosure ℚ (AlgebraicClosure E) := IsAlgClosure.ofAlgebraic ℚ E _
  let A := padicTateTwist E ℓ i
  let M := numberFieldSelmerMinusPart E ℓ i
  let V := numberFieldRelaxedSelmerKernel E ℓ i
  let j : M →ₗ[ℤ_[ℓ]] V :=
    (A.selmerKernel_of_subset (numberFieldRelaxedSelmerRestrictions_subset E ℓ)).comp
      ((numberFieldSelmerConjugation E ℓ i IsAlgClosed.lift).eigenspace _).subtype
  have hj : Function.Injective j :=
    (A.selmerKernel_of_subset_injective (numberFieldRelaxedSelmerRestrictions_subset E ℓ)).comp
      (Submodule.subtype_injective _)
  let Q := LinearEquiv.ofInjective j hj
  obtain ⟨r, hr, hkill⟩ := hExp target hprimitive e q d he hpair i hi ℓ hodd hdiv
  obtain ⟨g, hg, hgR⟩ := hRank target hprimitive e q d he hpair i hi ℓ hodd hdiv
  have hjkill : ∀ x ∈ j.range, (ℓ : ℤ_[ℓ]) ^ r • x = 0 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_smul, hkill a, map_zero]
  have hlen : Module.length ℤ_[ℓ] M ≤ ((r * g : ℕ) : ℕ∞) := by
    rw [Q.length_eq]
    calc
      _ ≤ (r : ℕ∞) * Module.length ℤ_[ℓ] (Submodule.torsionBy ℤ_[ℓ] V (ℓ : ℤ_[ℓ])) :=
        module_length_le_torsionBy_pow j.range (ℓ : ℤ_[ℓ]) r hjkill
      _ ≤ _ := by
        rw [Nat.cast_mul]
        gcongr
  have hlogℓ₀ : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg (by exact_mod_cast hℓ.one_le)
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast selmerHostConductor_pos target e q d
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.one_le
  have hfℓ : 1 ≤ (ℓ : ℝ) * f := one_le_mul_of_one_le_of_one_le hℓR hfR
  have hlog : Real.log ((ℓ : ℝ) * f) ≤ Real.log ((i : ℝ) * ℓ * f) :=
    Real.log_le_log (zero_lt_one.trans_le hfℓ) (by
      rw [mul_assoc]
      exact le_mul_of_one_le_left (zero_le_one.trans hfℓ) hiR)
  have hlog₀ : 0 ≤ Real.log ((i : ℝ) * ℓ * f) := (Real.log_nonneg hfℓ).trans hlog
  have hgR' : (g : ℝ) ≤ 8 * ℓ * n * Real.log ((i : ℝ) * ℓ * f) :=
    hgR.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
  change numberFieldSelmerSignLengths false E ℓ i ≠ ⊤ ∧ _
  rw [numberFieldSelmerSignLengths_false_eq_moduleLength E ℓ i]
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hlen, ?_⟩
  have hlenNat : (Module.length ℤ_[ℓ] M).toNat ≤ r * g := ENat.toNat_le_of_le_natCast hlen
  have hlenReal : ((Module.length ℤ_[ℓ] M).toNat : ℝ) ≤ (r : ℝ) * g := by exact_mod_cast hlenNat
  calc
    _ ≤ Real.log ℓ * ((r : ℝ) * g) := mul_le_mul_of_nonneg_left hlenReal hlogℓ₀
    _ = ((r : ℝ) * Real.log ℓ) * g := by ring
    _ ≤ (C * n * ((i : ℝ) + 1) * Real.log ((i : ℝ) * ℓ * f)) *
        (8 * ℓ * n * Real.log ((i : ℝ) * ℓ * f)) :=
      mul_le_mul hr hgR' (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- Theorem 17.12(II) follows from the prime-to-degree Bernoulli comparison
and the two arithmetic inputs at primes dividing the host degree. -/
theorem numberField_selmer_minus_estimate_of_comparison_exponent_rank
    (hBernoulli : HasSelmerBernoulliValuationComparison)
    (hExp : HasSelmerStickelbergerExponentEstimate)
    (hRank : HasSelmerRelaxedTorsionRankEstimate) : HasSelmerMinusEstimate :=
  numberField_selmer_minus_estimate_of_prime_estimates
    (selmerBernoulliMinusEstimates_of_valuationComparison hBernoulli)
    (selmerStickelbergerMinusEstimates_of_exponent_rank hExp hRank)

end Riemann
