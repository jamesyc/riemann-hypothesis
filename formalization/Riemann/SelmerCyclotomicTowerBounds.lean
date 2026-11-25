module

public import Riemann.SelmerIntegralCohomology
public import Riemann.SelmerLengthAssembly
public import Riemann.SelmerTowerCokernel
public import Utilities.FiniteScaleWindows
public import Utilities.PadicTwistExceptions
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Utilities.ExponentialGrowth

@[expose] public section

open Filter Asymptotics Utilities

namespace Riemann

/-- The bound on a layer when a twist stays away from the finitely many
p-adic roots controlling the tower. -/
def SelmerCyclotomicTowerRootBound (F : Type) [Field F] [NumberField F]
    (ℓ R c : ℕ) (hℓ : ℓ.Prime) : Prop :=
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  ∃ (E : Type) (_ : NormedField E) (_ : NormedAlgebra ℚ_[ℓ] E) (_ : IsUltrametricDist E)
      (n : ℕ) (roots : Fin n → E),
    n ≤ R ∧ ∀ i : ℕ, 1 ≤ i → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [Algebra F L],
      IsPrimePowerCyclotomicLayer ℓ m F L →
      ∀ B : ℕ, (∀ a, (ℓ : ℝ) ^ (-(B : ℤ)) ≤ ‖roots a - (i : E)‖) →
        numberFieldSelmerLengths L ℓ i ≤
          ((n * (max m (selmerCyclotomicReferenceDepth ℓ R) + c + B) : ℕ) : WithTop ℕ)

/-- A uniform upper bound for the root exponent can replace its value on
an individual base field. -/
theorem SelmerCyclotomicTowerRootBound.mono
    {F : Type} [Field F] [NumberField F] {ℓ R c c' : ℕ} {hℓ : ℓ.Prime}
    (hroot : SelmerCyclotomicTowerRootBound F ℓ R c hℓ) (hc : c ≤ c') :
    SelmerCyclotomicTowerRootBound F ℓ R c' hℓ := by
  let _ : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨E, _, _, _, n, roots, hn, hbound⟩ := hroot
  refine ⟨E, inferInstance, inferInstance, inferInstance, n, roots, hn,
    fun i hi m L _ _ _ hL B hfar => (hbound i hi m L hL B hfar).trans ?_⟩
  exact WithTop.coe_le_coe.mpr (Nat.mul_le_mul_left _ (by omega))

/-- The bound for every twist obtained from torsion at the reference layer
and a loss linear in the excess depth. -/
def SelmerCyclotomicTowerReferenceBound (F : Type) [Field F] [NumberField F]
    (ℓ R : ℕ) (K : ℝ) : Prop :=
  ∀ (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra F L₀],
    IsPrimePowerCyclotomicLayer ℓ (selmerCyclotomicReferenceDepth ℓ R) F L₀ →
    ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [Algebra F L],
      IsPrimePowerCyclotomicLayer ℓ m F L → ∀ i : ℕ, 1 ≤ i →
        let a := numberFieldSelmerLengths L ℓ i
        a ≠ ⊤ ∧ ((a.untopD 0 : ℕ) : ℝ) ≤ (R : ℝ) * (m - selmerCyclotomicReferenceDepth ℓ R : ℕ) +
          2 * selmerIntegralTorsionBudget L₀ i K

/-- Both cyclotomic towers use the same integral torsion estimate at their
reference layer. Only the depth comparison depends on the tower. -/
theorem selmerCyclotomicTowerReferenceBound_of_depthBound
    {F : Type} [Field F] [NumberField F] {ℓ R : ℕ} [Fact ℓ.Prime] {K : ℝ}
    (hroots : HasSmallPrimeTorsionRoots F ℓ) (hdepth : SelmerCyclotomicTowerDepthBound F ℓ R)
    (hbudget : SelmerIntegralTorsionBound K) :
    SelmerCyclotomicTowerReferenceBound F ℓ R K := by
  intro L₀ _ _ _ hL₀ m L _ _ _ hL i hi
  have hroots₀ : HasSmallPrimeTorsionRoots L₀ ℓ := hroots.map
  have hcomplex := hroots₀.isTotallyComplex (Fact.out : ℓ.Prime)
  obtain ⟨hfinite, hlog⟩ := hbudget L₀ ℓ hcomplex hroots₀ i hi
  obtain ⟨hs₀, hlen₀⟩ := selmerLength_le_of_integralTateH2_torsionBudget L₀ ℓ i _
    (selmerLength_le_integralTateH2_length L₀ ℓ hcomplex i hi) hfinite hlog
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hs₀
  let loss := R * (m - selmerCyclotomicReferenceDepth ℓ R)
  have hle : numberFieldSelmerLengths L ℓ i ≤ ((n + loss : ℕ) : WithTop ℕ) := calc
    _ ≤ numberFieldSelmerLengths L₀ ℓ i + (loss : WithTop ℕ) := hdepth L₀ hL₀ m L hL i hi
    _ = (n : WithTop ℕ) + (loss : WithTop ℕ) := congrArg (· + (loss : WithTop ℕ)) hn.symm
    _ = _ := (WithTop.coe_add n loss).symm
  refine ⟨ne_top_of_le_ne_top WithTop.coe_ne_top hle, ?_⟩
  rw [← hn] at hlen₀
  change (n : ℝ) ≤ _ at hlen₀
  have hcast : (((numberFieldSelmerLengths L ℓ i).untopD 0 : ℕ) : ℝ) ≤ (n : ℝ) + loss := by
    exact_mod_cast WithTop.untopD_le (a := 0) hle
  have hloss : (loss : ℝ) = (R : ℝ) * (m - selmerCyclotomicReferenceDepth ℓ R : ℕ) :=
    Nat.cast_mul _ _
  linarith only [hcast, hlen₀, hloss]

/-- The arithmetic length estimates on and off the exceptional twists. -/
structure SelmerCyclotomicTowerProfile (F : Type) [Field F] [NumberField F]
    (ℓ R c : ℕ) (K : ℝ) : Prop where
  outside : ∀ Z : ℕ, ∃ exc : Finset ℕ, exc.card ≤ R ∧
    ∀ i ∈ Finset.Icc 1 Z, i ∉ exc →
      ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [Algebra F L],
        IsPrimePowerCyclotomicLayer ℓ m F L →
        numberFieldSelmerLengths L ℓ i ≤
          ((R * (max m (selmerCyclotomicReferenceDepth ℓ R) + c + Nat.log ℓ Z) : ℕ) : WithTop ℕ)
  reference : SelmerCyclotomicTowerReferenceBound F ℓ R K

/-- The root-distance estimate supplies the bounded exception sets at every
cutoff. Both the dyadic and odd bounds use this construction. -/
theorem selmerCyclotomicTowerProfile_of_rootBound
    {F : Type} [Field F] [NumberField F] {ℓ R c : ℕ} {K : ℝ} (hℓ : ℓ.Prime)
    (hroot : SelmerCyclotomicTowerRootBound F ℓ R c hℓ)
    (href : SelmerCyclotomicTowerReferenceBound F ℓ R K) :
    SelmerCyclotomicTowerProfile F ℓ R c K := by
  let _ : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨E, _, _, _, n, roots, hn, hbound⟩ := hroot
  refine ⟨fun Z => ?_, href⟩
  obtain ⟨exc, hexc, hfar⟩ := exists_padic_twist_exceptions (p := ℓ) roots Z
  refine ⟨exc, hexc.trans (by simpa using hn), fun i hi hnot m L _ _ _ hL => ?_⟩
  exact (hbound i (Finset.mem_Icc.mp hi).1 m L hL (Nat.log ℓ Z) (hfar i hi hnot)).trans
    (WithTop.coe_le_coe.mpr (Nat.mul_le_mul_right _ hn))

/-- The pointwise budget before summing over the twist interval. The
additive one allows the dyadic comparison with the host. -/
noncomputable def selmerCyclotomicPointBudget (C ε x : ℝ) : ℝ :=
  C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * ε / 4)) + 1

theorem selmerCyclotomicPointBudget_nonneg {C ε x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) :
    0 ≤ selmerCyclotomicPointBudget C ε x := by
  unfold selmerCyclotomicPointBudget
  have := Real.log_nonneg hx
  positivity

/-- The twist count and the pointwise budget fit in the small-prime allowance. -/
theorem eventually_rpow_mul_selmerCyclotomicPointBudget_le {C ε : ℝ}
    (T : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      x ^ T * selmerCyclotomicPointBudget C ε x ≤ Real.exp (x ^ (4 * ε / 5)) := by
  have hβ : 0 < 4 * ε / 5 := by positivity
  have hgap : 0 < 4 * ε / 5 - 3 * ε / 4 := by linarith
  have hsmall := (((isLittleO_log_rpow_atTop hβ).const_mul_left (T + C)).add
    (isLittleO_const_rpow_atTop (C + Real.log 3) hβ)).bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall,
      (tendsto_rpow_atTop hgap).eventually_ge_atTop (2 * C)] with x hx hlog hpow
  have hx₀ := zero_lt_one.trans_le hx
  have hlog' : (T + C) * Real.log x + (C + Real.log 3) ≤ x ^ (4 * ε / 5) / 2 := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _), Real.norm_eq_abs] at hlog
    exact (le_abs_self _).trans (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hlog)
  have hpow' : C * x ^ (3 * ε / 4) ≤ x ^ (4 * ε / 5) / 2 := by
    have h := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hx₀.le (3 * ε / 4))
    rw [← Real.rpow_add hx₀, sub_add_cancel] at h
    linarith
  let a := C * (1 + Real.log x)
  let b := C * x ^ (3 * ε / 4)
  have ha : 0 ≤ a := mul_nonneg hC (by linarith [Real.log_nonneg hx])
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsum : selmerCyclotomicPointBudget C ε x ≤ 3 * Real.exp (a + b) := by
    change a + 2 * Real.exp b + 1 ≤ _
    have h₁ := (Real.add_one_le_exp a).trans (Real.exp_le_exp.mpr (show a ≤ a + b by linarith))
    have h₂ := Real.exp_le_exp.mpr (show b ≤ a + b by linarith)
    linarith
  calc
    _ ≤ x ^ T * (3 * Real.exp (a + b)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = Real.exp (T * Real.log x + Real.log 3 + (a + b)) := by
      rw [Real.rpow_def_of_pos hx₀, Real.exp_add (T * Real.log x + Real.log 3) (a + b),
        Real.exp_add (T * Real.log x) (Real.log 3), Real.exp_log (by norm_num : (0 : ℝ) < 3),
        mul_comm T (Real.log x), mul_assoc]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [a, b]; linarith only [hlog', hpow'])

/-- The logarithm of the upper twist cutoff grows at most logarithmically
in each scale inside the window. -/
private theorem natLog_floor_rpow_le {ℓ : ℕ} {X x J T : ℝ}
    (hℓ : 2 ≤ ℓ) (hJ : 0 < J) (hT : 0 ≤ T) (hX : 1 ≤ X) (hx : X ^ (1 / J) ≤ x) :
    (Nat.log ℓ ⌊X ^ T⌋₊ : ℝ) ≤ 2 * T * J * Real.log x := by
  have hX₀ := zero_lt_one.trans_le hX
  have hx₁ : 1 ≤ x := (Real.one_le_rpow hX (by positivity)).trans hx
  have hlogx := Real.log_nonneg hx₁
  have hlogX : Real.log X ≤ J * Real.log x := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hX₀ (1 / J)) hx
    rwa [Real.log_rpow hX₀, one_div_mul_eq_div, div_le_iff₀ hJ, mul_comm] at h
  let Z : ℕ := ⌊X ^ T⌋₊
  have hZ : 1 ≤ Z := Nat.le_floor (by simpa using Real.one_le_rpow hX hT)
  have hpower : (ℓ : ℝ) ^ Nat.log ℓ Z ≤ X ^ T :=
    (by exact_mod_cast Nat.pow_log_le_self ℓ (by omega : Z ≠ 0) :
      (ℓ : ℝ) ^ Nat.log ℓ Z ≤ (Z : ℝ)).trans (Nat.floor_le (by positivity))
  have hℓ₀ : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hlog := Real.log_le_log (pow_pos hℓ₀ _) hpower
  rw [Real.log_pow, Real.log_rpow hX₀] at hlog
  have hl : (1 / 2 : ℝ) ≤ Real.log ℓ := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hℓ : (2 : ℝ) ≤ ℓ)
    linarith [Real.log_two_gt_d9]
  have hl' := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (Nat.log ℓ Z))
  nlinarith only [hlog, hl', mul_le_mul_of_nonneg_left hlogX hT]

/-- The scale-dependent pointwise estimate common to the dyadic and odd
branches. The same finite set is used for every target layer. -/
theorem selmerCyclotomicTower_pointwiseOnScales
    {ℓ R c N : ℕ} {K D a T J ε : ℝ} (hℓ : ℓ.Prime) (hK : 1 ≤ K)
    (hD : 0 ≤ D) (ha : 0 ≤ a) (hT : 0 ≤ T) (hJ : 0 < J) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F L₀ : Type) [Field F] [NumberField F]
      [Field L₀] [NumberField L₀] [Algebra F L₀],
      SelmerCyclotomicTowerProfile F ℓ R c K →
      IsPrimePowerCyclotomicLayer ℓ (selmerCyclotomicReferenceDepth ℓ R) F L₀ →
      Module.finrank ℚ L₀ ≤ N →
      ∀ X ≥ 1, ∃ exc : Finset ℕ, exc.card ≤ R ∧
        ∀ x ∈ Set.Icc (X ^ (1 / J)) X, 1 ≤ x →
          GoodFiniteScale (ε / (2 * K)) T exc x →
          Real.log (2 * ((NumberField.discr L₀).natAbs : ℝ)) ≤ D * x ^ (ε / 4) →
          ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [Algebra F L],
            IsPrimePowerCyclotomicLayer ℓ m F L → (m : ℝ) ≤ a * (1 + Real.log x) →
            ∀ i : ℕ, 1 ≤ i → (i : ℝ) ≤ x ^ T →
              let u := numberFieldSelmerLengths L ℓ i
              u ≠ ⊤ ∧ ((u.untopD 0 : ℕ) : ℝ) + 1 ≤ selmerCyclotomicPointBudget C ε x := by
  let j := selmerCyclotomicReferenceDepth ℓ R
  let A := (R : ℝ) * (a + j + c + 2 * T * J)
  let B := (2 * (N : ℝ)) ^ K * D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro F L₀ _ _ _ _ _ hprofile hL₀ hdegree X hX
  let Z : ℕ := ⌊X ^ T⌋₊
  obtain ⟨exc, hcard, hout⟩ := hprofile.outside Z
  refine ⟨exc, hcard, ?_⟩
  intro x hx hx₁ hgood hdisc m L _ _ _ hL hm i hi hix
  have hx₀ := zero_lt_one.trans_le hx₁
  have hlog := Real.log_nonneg hx₁
  have hscale : (i : ℝ) ≤ X ^ T := hix.trans (Real.rpow_le_rpow hx₀.le hx.2 hT)
  have hbase : (R : ℝ) * ((m : ℝ) + j + c + Nat.log ℓ Z) ≤ A * (1 + Real.log x) := by
    have hZ := natLog_floor_rpow_le hℓ.two_le hJ hT hX hx.1
    dsimp only [A]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    nlinarith only [hm, hZ, mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hlog,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) c) hlog, mul_nonneg (show 0 ≤ 2 * T * J by positivity) hlog,
      show 0 ≤ 2 * T * J by positivity]
  have hbudgetExp : 2 * Real.exp (B * x ^ (3 * ε / 4)) ≤
      2 * Real.exp ((A + B) * x ^ (3 * ε / 4)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) (by norm_num)
  have hbudgetLin : A * (1 + Real.log x) ≤ (A + B) * (1 + Real.log x) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  by_cases hmem : i ∈ exc
  · obtain ⟨hfin, hbound⟩ := hprofile.reference L₀ hL₀ m L hL i hi
    unfold selmerIntegralTorsionBudget at hbound
    have hlow := hgood i hmem hix
    have he : (i : ℝ) ^ K ≤ x ^ (ε / 2) := by
      have h := Real.rpow_le_rpow (Nat.cast_nonneg i) hlow (by linarith : 0 ≤ K)
      rwa [← Real.rpow_mul hx₀.le, show ε / (2 * K) * K = ε / 2 by
        have : K ≠ 0 := by linarith
        field_simp] at h
    have hd : (2 * (Module.finrank ℚ L₀ : ℝ)) ^ K ≤ (2 * (N : ℝ)) ^ K :=
      Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hdegree) (by norm_num)) (by linarith)
    have hpow : (2 * (i : ℝ) * (Module.finrank ℚ L₀ : ℝ)) ^ K ≤
        (2 * (N : ℝ)) ^ K * x ^ (ε / 2) := by
      rw [show 2 * (i : ℝ) * (Module.finrank ℚ L₀ : ℝ) =
        (2 * (Module.finrank ℚ L₀ : ℝ)) * i by ring, Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
      exact mul_le_mul hd he (by positivity) (by positivity)
    have harg : (2 * (i : ℝ) * (Module.finrank ℚ L₀ : ℝ)) ^ K *
        Real.log (2 * ((NumberField.discr L₀).natAbs : ℝ)) ≤ B * x ^ (3 * ε / 4) := by
      have h := mul_le_mul hpow hdisc
        (Real.log_nonneg (by
          have hpos := Int.natAbs_pos.mpr (NumberField.discr_ne_zero L₀)
          have : (1 : ℝ) ≤ ((NumberField.discr L₀).natAbs : ℝ) := by exact_mod_cast hpos
          linarith)) (by positivity)
      refine h.trans_eq ?_
      rw [show (3 * ε / 4) = ε / 2 + ε / 4 by ring, Real.rpow_add hx₀]
      dsimp [B]
      ring
    have hdepth : ((m - j : ℕ) : ℝ) ≤ (m : ℝ) + j + c + Nat.log ℓ Z := by
      have h : ((m - j : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m j
      linarith [Nat.cast_nonneg (α := ℝ) j, Nat.cast_nonneg (α := ℝ) c,
        Nat.cast_nonneg (α := ℝ) (Nat.log ℓ Z)]
    have hloss := (mul_le_mul_of_nonneg_left hdepth (Nat.cast_nonneg (α := ℝ) R)).trans hbase
    have hexp := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num : (0 : ℝ) ≤ 2)
    refine ⟨hfin, ?_⟩
    dsimp only [selmerCyclotomicPointBudget]
    linarith only [hbound, hloss, hexp, hbudgetExp, hbudgetLin]
  · have hle := hout i (Finset.mem_Icc.mpr ⟨hi, Nat.le_floor hscale⟩) hmem m L hL
    have hfin := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    have hnat := WithTop.untopD_le (a := 0) hle
    have hlen : (((numberFieldSelmerLengths L ℓ i).untopD 0 : ℕ) : ℝ) ≤
        (R : ℝ) * ((m : ℝ) + j + c + Nat.log ℓ Z) := by
      have hs : max m j ≤ m + j := max_le (by omega) (by omega)
      exact_mod_cast hnat.trans (Nat.mul_le_mul_left R (by omega))
    refine ⟨hfin, ?_⟩
    dsimp only [selmerCyclotomicPointBudget]
    linarith only [hlen, hbase, hbudgetLin, Real.exp_nonneg ((A + B) * x ^ (3 * ε / 4))]

end Riemann
