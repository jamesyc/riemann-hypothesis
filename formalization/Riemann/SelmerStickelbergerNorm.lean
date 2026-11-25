module

public import Mathlib.Algebra.Group.IsCommutative
public import Riemann.SelmerExceptionalBounds
public import Riemann.SelmerGaloisAction
public import Utilities.GroupAlgebraNorm
public import Utilities.HigherStickelbergerNorm
public import Utilities.HigherStickelbergerPadic
import Utilities.FiniteAlgebraAnnihilator
import Utilities.PadicAnnihilator

@[expose] public section

open Utilities
open scoped IsMulCommutative

namespace Riemann

/-- The norm of an integral group-algebra annihilator supplies an integer
annihilator on the actual minus part, bounded by its complex character values. -/
theorem numberFieldSelmerMinusPart_intNorm_bound (E : Type) [Field E] [NumberField E]
    [IsAbelianGalois ℚ E] [Fintype (E ≃ₐ[ℚ] E)] (ℓ i : ℕ) [Fact ℓ.Prime]
    (z : MonoidAlgebra ℤ (E ≃ₐ[ℚ] E)) (B : ℝ)
    (hvalue : ∀ χ : AddChar (Additive (E ≃ₐ[ℚ] E)) ℂ,
      let y := groupAlgebraCharacterEval (E ≃ₐ[ℚ] E)
        (MonoidAlgebra.mapRingHom (E ≃ₐ[ℚ] E) (Int.castRingHom ℂ) z) χ
      y ≠ 0 ∧ ‖y‖ ≤ B)
    (hkill : ∀ x : numberFieldSelmerMinusPart E ℓ i,
      Representation.asAlgebraHom (numberFieldSelmerGaloisAction E ℓ i)
        (MonoidAlgebra.mapRingHom (E ≃ₐ[ℚ] E) (Int.castRingHom ℤ_[ℓ]) z) x.val = 0) :
    ∃ X : ℤ, X ≠ 0 ∧ Real.log (X.natAbs : ℝ) ≤ Module.finrank ℚ E * Real.log B ∧
      ∀ x : numberFieldSelmerMinusPart E ℓ i, (X : ℤ_[ℓ]) • x = 0 := by
  obtain ⟨hX, hlog⟩ := intNorm_groupAlgebra_ne_zero_log_le (E ≃ₐ[ℚ] E) z B hvalue
  have hdegree : Fintype.card (E ≃ₐ[ℚ] E) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  rw [hdegree] at hlog
  refine ⟨Algebra.norm ℤ z, hX, hlog, fun x => Subtype.ext ?_⟩
  exact intNorm_smul_eq_zero_of_groupAlgebraAction (numberFieldSelmerGaloisAction E ℓ i) z x.val (hkill x)

/-- At the Stickelberger level `f * ℓ`, pass the inverse cyclotomic
map to the constructors, whose terms are indexed by the inverse of its value. -/
noncomputable def selmerStickelbergerGalMap (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ℓ : ℕ) :
    (ZMod (selmerHostConductor target e q d * ℓ))ˣ →*
      (selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d) := by
  let _ := selmerHostField_isAbelianGalois target e q d
  exact ((selmerHostConductorGalMap target e q d).comp (ZMod.unitsMap (dvd_mul_right _ _)))⁻¹

/-- A term indexed by the inverse of the Stickelberger map acts by the
usual cyclotomic automorphism on the host. -/
theorem inv_selmerStickelbergerGalMap_apply (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ℓ : ℕ) (b : (ZMod (selmerHostConductor target e q d * ℓ))ˣ) :
    (selmerStickelbergerGalMap target e q d ℓ b)⁻¹ =
      selmerHostConductorGalMap target e q d (ZMod.unitsMap (dvd_mul_right _ _) b) := by
  let _ := selmerHostField_isAbelianGalois target e q d
  simp only [selmerStickelbergerGalMap, MonoidHom.inv_apply, inv_inv, MonoidHom.comp_apply]

/-- The integral smoothing at `2 * f * ℓ + 1` of the higher element
at Bernoulli index `i + 1`. -/
noncomputable def selmerIntegralHigherStickelberger (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ℓ i : ℕ) [Fact ℓ.Prime] :
    MonoidAlgebra ℤ (selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d) := by
  let f := selmerHostConductor target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : NeZero (f * ℓ) := ⟨mul_ne_zero (selmerHostConductor_pos target e q d).ne'
    (Fact.out : ℓ.Prime).ne_zero⟩
  exact integralHigherStickelberger (N := f * ℓ) (selmerStickelbergerGalMap target e q d ℓ)
    (i + 1) (2 * (f * ℓ) + 1) (by simp)

/-- The p-adic integral smoothing at the host's Stickelberger level. -/
noncomputable def selmerPadicHigherStickelberger (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ℓ i : ℕ) [Fact ℓ.Prime] (hodd : ℓ ≠ 2) :
    MonoidAlgebra ℤ_[ℓ] (selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d) := by
  let f := selmerHostConductor target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : NeZero (f * ℓ) := ⟨mul_ne_zero (selmerHostConductor_pos target e q d).ne'
    (Fact.out : ℓ.Prime).ne_zero⟩
  exact padicHigherStickelberger ℓ (selmerStickelbergerGalMap target e q d ℓ)
    (Nat.succ_ne_zero i) hodd (dvd_mul_left _ _)

/-- The remaining arithmetic annihilation after the cyclotomic restriction
factor `φ(f * ℓ)` on the Selmer minus part. -/
def HasSelmerHigherStickelbergerAnnihilation : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i : ℕ, 1 ≤ i →
      let E := selmerHostField target e q d
      letI := selmerHostField_isAbelianGalois target e q d
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ℓ ∣ Module.finrank ℚ E →
        ∀ x : numberFieldSelmerMinusPart E ℓ i,
          Representation.asAlgebraHom (numberFieldSelmerGaloisAction E ℓ i)
            (MonoidAlgebra.mapRingHom (E ≃ₐ[ℚ] E) (Int.castRingHom ℤ_[ℓ])
              (selmerIntegralHigherStickelberger target e q d ℓ i))
            ((selmerHostConductor target e q d * ℓ).totient • x).val = 0

/-- Annihilation by the explicit p-adic model supplies the arithmetic
input for the denominator-cleared element. -/
theorem selmerHigherStickelbergerAnnihilation_of_padicLift
    (h : ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
      ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i : ℕ, 1 ≤ i →
        let E := selmerHostField target e q d
        letI := selmerHostField_isAbelianGalois target e q d
        ∀ (ℓ : ℕ) [Fact ℓ.Prime] (hodd : ℓ ≠ 2), ℓ ∣ Module.finrank ℚ E →
          ∀ x : numberFieldSelmerMinusPart E ℓ i,
            Representation.asAlgebraHom (numberFieldSelmerGaloisAction E ℓ i)
              (selmerPadicHigherStickelberger target e q d ℓ i hodd)
              ((selmerHostConductor target e q d * ℓ).totient • x).val = 0) :
    HasSelmerHigherStickelbergerAnnihilation := by
  intro target hp e q d he hpair i hi
  dsimp only
  intro ℓ _ hodd hdiv x
  let E := selmerHostField target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let N := selmerHostConductor target e q d * ℓ
  let _ : NeZero N := ⟨mul_ne_zero (selmerHostConductor_pos target e q d).ne'
    (Fact.out : ℓ.Prime).ne_zero⟩
  let π := selmerStickelbergerGalMap target e q d ℓ
  have hk := Nat.succ_ne_zero i
  have hℓN : ℓ ∣ N := dvd_mul_left _ _
  exact integralHigherStickelberger_annihilation_of_padicLift (N := N) ℓ π (k := i + 1)
    (a := 2 * N + 1) hk (by simp) (selmerPadicHigherStickelberger target e q d ℓ i hodd)
    (map_padicHigherStickelberger_eq_rational ℓ π hk hodd hℓN)
    (numberFieldSelmerGaloisAction E ℓ i) (N.totient • x).val
    (h target hp e q d he hpair i hi ℓ hodd hdiv x)

private theorem log_stickelberger_level_le {i ℓ f : ℕ}
    (hi : 1 ≤ i) (hℓ : 2 ≤ ℓ) (hf : 0 < f) :
    Real.log (((i + 1 : ℕ) : ℝ) * ((f * ℓ : ℕ) : ℝ)) ≤
      2 * Real.log ((i : ℝ) * ℓ * f) := by
  let t : ℝ := (i : ℝ) * ℓ * f
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have ht : 2 ≤ t := by
    dsimp only [t]
    calc
      (2 : ℝ) = 1 * 2 * 1 := by ring
      _ ≤ _ := by gcongr
  have hmul : (((i + 1 : ℕ) : ℝ) * ((f * ℓ : ℕ) : ℝ)) ≤ 2 * t := by
    push_cast
    calc
      _ ≤ (2 * (i : ℝ)) * ((f : ℝ) * ℓ) := by gcongr; linarith
      _ = _ := by dsimp only [t]; ring
  calc
    _ ≤ Real.log (2 * t) := Real.log_le_log (by positivity) hmul
    _ = Real.log 2 + Real.log t := Real.log_mul (by norm_num) (by linarith)
    _ ≤ 2 * Real.log t := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht]

/-- Complete the integral element on the parity of the Selmer minus part. -/
noncomputable def selmerCompletedHigherStickelberger (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ℓ i : ℕ) [Fact ℓ.Prime] :
    MonoidAlgebra ℤ (selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d) := by
  let _ := selmerHostField_isAbelianGalois target e q d
  exact groupAlgebraParityCompletion (selmerStickelbergerGalMap target e q d ℓ (-1))
    ((-1 : ℤ) ^ (i + 1)) (selmerIntegralHigherStickelberger target e q d ℓ i)

/-- The completed element has a nonzero integer norm with the required
logarithmic budget at the host. -/
theorem selmerCompletedHigherStickelberger_norm_bound (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ℓ i : ℕ) [Fact ℓ.Prime] (hi : 1 ≤ i) :
    letI := selmerHostField_isAbelianGalois target e q d
    let z := selmerCompletedHigherStickelberger target e q d ℓ i
    Algebra.norm ℤ z ≠ 0 ∧ Real.log ((Algebra.norm ℤ z).natAbs : ℝ) ≤
      16 * Module.finrank ℚ (selmerHostField target e q d) * ((i : ℝ) + 1) *
        Real.log ((i : ℝ) * ℓ * selmerHostConductor target e q d) := by
  dsimp only
  let E := selmerHostField target e q d
  let f := selmerHostConductor target e q d
  let N := f * ℓ
  let k := i + 1
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : Fintype (E ≃ₐ[ℚ] E) := Fintype.ofFinite _
  have hf : 0 < f := selmerHostConductor_pos target e q d
  have hℓ : ℓ.Prime := Fact.out
  have hN : 2 ≤ N := hℓ.two_le.trans (Nat.le_mul_of_pos_left _ hf)
  have hk : 2 ≤ k := Nat.succ_le_succ hi
  let _ : NeZero N := ⟨by omega⟩
  let z := selmerCompletedHigherStickelberger target e q d ℓ i
  have hsize : Algebra.norm ℤ z ≠ 0 ∧
      Real.log ((Algebra.norm ℤ z).natAbs : ℝ) ≤
        (Fintype.card (E ≃ₐ[ℚ] E) : ℝ) * (8 * (k : ℝ) * Real.log ((k : ℝ) * N)) :=
    intNorm_parityHigherStickelberger_bound (selmerStickelbergerGalMap target e q d ℓ)
      hN hk (by simp)
  have hdegree : Fintype.card (E ≃ₐ[ℚ] E) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  refine ⟨hsize.1, ?_⟩
  calc
    _ ≤ (Module.finrank ℚ E : ℝ) * (8 * (k : ℝ) * Real.log ((k : ℝ) * N)) := by
      simpa only [hdegree] using hsize.2
    _ ≤ (Module.finrank ℚ E : ℝ) * (8 * (k : ℝ) * (2 * Real.log ((i : ℝ) * ℓ * f))) := by
      gcongr
      exact log_stickelberger_level_le hi hℓ.two_le hf
    _ = _ := by dsimp only [k]; push_cast; ring

/-- The norm of the completion annihilates the minus part whenever the
integral element itself annihilates it. -/
theorem selmerCompletedHigherStickelberger_norm_annihilates (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ℓ i : ℕ) [Fact ℓ.Prime] :
    let E := selmerHostField target e q d
    letI := selmerHostField_isAbelianGalois target e q d
    ∀ x : numberFieldSelmerMinusPart E ℓ i,
      Representation.asAlgebraHom (numberFieldSelmerGaloisAction E ℓ i)
        (MonoidAlgebra.mapRingHom (E ≃ₐ[ℚ] E) (Int.castRingHom ℤ_[ℓ])
          (selmerIntegralHigherStickelberger target e q d ℓ i)) x.val = 0 →
      (Algebra.norm ℤ (selmerCompletedHigherStickelberger target e q d ℓ i) : ℤ_[ℓ]) • x = 0 := by
  dsimp only
  intro x h
  let E := selmerHostField target e q d
  let f := selmerHostConductor target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : Fintype (E ≃ₐ[ℚ] E) := Fintype.ofFinite _
  let ρ := numberFieldSelmerGaloisAction E ℓ i
  let c := selmerStickelbergerGalMap target e q d ℓ (-1)
  let ε := (-1 : ℤ) ^ (i + 1)
  let s := selmerIntegralHigherStickelberger target e q d ℓ i
  let _ : IsAlgClosure ℚ (AlgebraicClosure E) := IsAlgClosure.ofAlgebraic ℚ E _
  let ι : AlgebraicClosure E →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hneg : ZMod.unitsMap (dvd_mul_right f ℓ) (-1 : (ZMod (f * ℓ))ˣ) = -1 := by
    apply Units.ext
    rw [ZMod.unitsMap_val]
    simp
  have hc : ρ c = numberFieldSelmerConjugation E ℓ i ι := by
    have hinv : c⁻¹ = selmerHostConductorGalMap target e q d (-1) :=
      (inv_selmerStickelbergerGalMap_apply target e q d ℓ (-1)).trans
        (congrArg (selmerHostConductorGalMap target e q d) hneg)
    have hc' : c = selmerHostConductorGalMap target e q d (-1) := by
      simpa only [inv_inv, ← map_inv, inv_neg, inv_one] using congrArg Inv.inv hinv
    rw [hc', selmerHostConductorGalMap_neg_one_eq_conjugation target e q d (ι.domRestrict E)]
    exact numberFieldSelmerGaloisAction_complexConjugation E ℓ i ι
  have hε : (ε : ℤ_[ℓ]) * (ε : ℤ_[ℓ]) = 1 := by
    dsimp only [ε]
    push_cast
    rw [← mul_pow]
    norm_num
  have hx : ρ c x.val = (ε : ℤ_[ℓ]) • x.val := by
    rw [hc]
    have hsign : (ε : ℤ_[ℓ]) = -((-1 : ℤ_[ℓ]) ^ i) := by
      dsimp only [ε]
      push_cast
      rw [pow_succ]
      ring
    rw [hsign]
    exact Module.End.mem_eigenspace_iff.mp x.property
  have hs : Representation.asAlgebraHom ρ
      (MonoidAlgebra.mapRingHom (E ≃ₐ[ℚ] E) (Int.castRingHom ℤ_[ℓ]) s) x.val = 0 := h
  apply Subtype.ext
  change (Algebra.norm ℤ (groupAlgebraParityCompletion c ε s) : ℤ_[ℓ]) • x.val = 0
  exact intNorm_parityCompletion_smul_eq_zero ρ c ε hε s x.val hx hs

/-- The logarithmic budget and parity reduction turn the explicit integral
element into the required bounded integer annihilator. -/
theorem selmerIntegerAnnihilatorEstimate_of_higherStickelberger
    (h : HasSelmerHigherStickelbergerAnnihilation) : HasSelmerIntegerAnnihilatorEstimate := by
  refine ⟨17, by norm_num, fun target hp e q d he hpair i hi ℓ _ hodd hdiv => ?_⟩
  let _ := selmerHostField_isAbelianGalois target e q d
  let E := selmerHostField target e q d
  let f := selmerHostConductor target e q d
  let N := f * ℓ
  let t : ℝ := (i : ℝ) * ℓ * f
  let X := Algebra.norm ℤ (selmerCompletedHigherStickelberger target e q d ℓ i)
  obtain ⟨hsize, hlog⟩ := selmerCompletedHigherStickelberger_norm_bound target e q d ℓ i hi
  have hf : 0 < f := selmerHostConductor_pos target e q d
  have hℓ : ℓ.Prime := Fact.out
  have hN : 0 < N := Nat.mul_pos hf hℓ.pos
  have htot := Nat.totient_pos.mpr hN
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hNt : (N : ℝ) ≤ t := by
    dsimp only [N, t]
    push_cast
    rw [mul_comm (f : ℝ) ℓ, mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hiR
  have hlogT := Real.log_le_log (Nat.cast_pos.mpr htot)
    ((Nat.cast_le.mpr (Nat.totient_le N)).trans hNt)
  have ht : 1 ≤ t := (show 1 ≤ (N : ℝ) by exact_mod_cast hN).trans hNt
  have hdeg : (1 : ℝ) ≤ Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hfactor : 1 ≤ (Module.finrank ℚ E : ℝ) * ((i : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le hdeg (by linarith)
  refine ⟨X * (N.totient : ℤ), mul_ne_zero hsize (by exact_mod_cast htot.ne'), ?_, ?_⟩
  · rw [Int.natAbs_mul, Int.natAbs_natCast, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    have hlog' : Real.log (X.natAbs : ℝ) ≤ (16 : ℝ) * Module.finrank ℚ E * ((i : ℝ) + 1) * Real.log t := hlog
    nlinarith only [hlog', hlogT, mul_le_mul_of_nonneg_right hfactor (Real.log_nonneg ht)]
  · intro x
    let y := N.totient • x
    have hkill := selmerCompletedHigherStickelberger_norm_annihilates target e q d ℓ i y
      (h target hp e q d he hpair i hi ℓ hodd hdiv x)
    exact padicInt_intCast_mul_nat_smul_eq_zero X N.totient x hkill

/-- The explicit higher Stickelberger annihilation implies the exceptional
prime exponent bound. -/
theorem selmerStickelbergerExponentEstimate_of_higherStickelberger
    (h : HasSelmerHigherStickelbergerAnnihilation) : HasSelmerStickelbergerExponentEstimate :=
  selmerStickelbergerExponentEstimate_of_integerAnnihilator
    (selmerIntegerAnnihilatorEstimate_of_higherStickelberger h)

end Riemann
