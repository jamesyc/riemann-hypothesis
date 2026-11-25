module

public import Riemann.SelmerConjugation
public import Riemann.SelmerConductorSizes
import Mathlib.NumberTheory.MulChar.Duality

@[expose] public section

open Filter Utilities

namespace Riemann

/-- The sign length is used on normal fields, in particular on every window host. -/
noncomputable def numberFieldSelmerSignLengths (positive : Bool) : NumberFieldSelmerLengths := by
  classical
  intro F _ _
  exact if h : Normal ℚ F then
    letI : Normal ℚ F := h
    letI : IsAlgClosure ℚ (AlgebraicClosure F) := IsAlgClosure.ofAlgebraic ℚ F _
    numberFieldSelmerSignLength F positive IsAlgClosed.lift
  else fun _ _ => ⊤

theorem numberFieldSelmerLengths_eq_signLengths_add (F : Type) [Field F] [NumberField F]
    [hF : Normal ℚ F] {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (i : ℕ) :
    numberFieldSelmerLengths F ℓ i =
      numberFieldSelmerSignLengths true F ℓ i + numberFieldSelmerSignLengths false F ℓ i := by
  let : IsAlgClosure ℚ (AlgebraicClosure F) := IsAlgClosure.ofAlgebraic ℚ F _
  simpa only [numberFieldSelmerSignLengths, dite_eq_left hF] using
    numberFieldSelmerLengths_eq_sign_add F IsAlgClosed.lift hℓ hodd i

/-- The prime and coprimality assumptions common to the arithmetic estimates. -/
structure SelmerEstimatePrimePair (target : BundledDirichletCharacter) (q d : ℕ+) : Prop where
  q_prime : (q : ℕ).Prime
  q_residue : (q : ℕ) % 8 = 3
  d_prime : (d : ℕ).Prime
  d_residue : (d : ℕ) % 16 = 7
  coprime : ((q : ℕ) * (d : ℕ)).Coprime target.modulus

/-- Theorem 17.12(I) for the specified plus eigenspaces and the prime two. -/
def HasSelmerPlusTwoWindowEstimates : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∀ e t : ℝ → ℕ,
      (∀ x ≥ 2, 2 ≤ e x ∧ (2 : ℝ) ^ e x ≤ x ^ (4 : ℕ) ∧
        2 ≤ t x ∧ (t x : ℝ) ≤ x ^ (401 : ℕ)) →
      ∃ J C P X₁ : ℝ, 0 < J ∧ 0 < C ∧ 0 < P ∧ 0 < X₁ ∧
        ∀ X ≥ X₁, ∀ q d : ℕ+, SelmerEstimatePrimePair target q d →
          max P (2 * X ^ (401 : ℕ) + 1) < (q : ℕ) →
          max P (2 * X ^ (401 : ℕ) + 1) < (d : ℕ) →
          Real.log ((q : ℕ) * (d : ℕ) : ℝ) ≤ X ^ (ε / (4 * J)) →
          ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ≤ X ^ (1 / 2 : ℝ) ∧
            ∀ x ∈ Set.Icc Y (Y ^ (2 : ℕ)),
              let E := selmerHostField target (e x) q d
              let f := selmerHostConductor target (e x) q d
              TwoSelmerLengthBound (numberFieldSelmerLengths E) (t x) (Real.exp (x ^ (4 * ε / 5))) ∧
              OddSelmerLengthBound (numberFieldSelmerSignLengths true E) (t x)
                (((f : ℝ) * t x) ^ C + C * Real.exp (x ^ (4 * ε / 5)))

/-- Theorem 17.12(II) for the specified minus eigenspaces. -/
def HasSelmerMinusEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
      ∀ (e t : ℕ) (q d : ℕ+), 2 ≤ e → 2 ≤ t → SelmerEstimatePrimePair target q d →
        let E := selmerHostField target e q d
        let f := selmerHostConductor target e q d
        OddSelmerLengthBound (numberFieldSelmerSignLengths false E) t
          (selmerMinusBudget C (Module.finrank ℚ E) t f (orderOf target.character))

private theorem selmer_cutoff_admitted {ε : ℝ} (hε : 0 < ε) (hεmax : ε < 1 / 52)
    (e : ℝ → ℕ) (he : ∀ x ≥ 1, x ^ (2 + 8 * ε) ≤ (2 : ℝ) ^ e x ∧
      (2 : ℝ) ^ e x ≤ 2 * x ^ (2 + 8 * ε)) :
    ∀ x ≥ 2, 2 ≤ e x ∧ (2 : ℝ) ^ e x ≤ x ^ (4 : ℕ) ∧
      2 ≤ Nat.floor (x ^ (401 : ℕ)) ∧
      (Nat.floor (x ^ (401 : ℕ)) : ℝ) ≤ x ^ (401 : ℕ) := by
  intro x hx
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hx
  have hx₀ := zero_le_one.trans hx1
  obtain ⟨hlo, hhi⟩ := he x hx1
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ e x := by
    calc
      _ ≤ x ^ (2 : ℕ) := by nlinarith
      _ ≤ x ^ (2 + 8 * ε) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; positivity)
      _ ≤ _ := hlo
  refine ⟨?_, ?_, Nat.le_floor ?_, Nat.floor_le (pow_nonneg hx₀ _)⟩
  · by_contra hn
    have hmono : (2 : ℝ) ^ e x ≤ 2 ^ (1 : ℕ) :=
      pow_right_mono₀ (by norm_num) (show e x ≤ 1 by omega)
    norm_num at hmono
    linarith
  · calc
      _ ≤ 2 * x ^ (2 + 8 * ε) := hhi
      _ ≤ x * x ^ (2 + 8 * ε) := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx₀ _)
      _ = x ^ (1 + (2 + 8 * ε)) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hx1) 1 (2 + 8 * ε), Real.rpow_one]
      _ ≤ x ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith)
  · norm_cast
    exact hx.trans (le_self_pow₀ hx1 (by decide : (401 : ℕ) ≠ 0))

private theorem selmer_estimate_prime_pair {target : BundledDirichletCharacter}
    {ε base : ℝ} {q d : ℕ+} (hp : SelmerWindowPair ε base q d)
    (hq : (target.modulus : ℕ) < q) (hd : (target.modulus : ℕ) < d) :
    SelmerEstimatePrimePair target q d := by
  refine ⟨hp.q_prime, hp.q_residue, hp.d_prime, hp.d_residue, Nat.Coprime.mul_left ?_ ?_⟩
  · exact hp.q_prime.coprime_iff_not_dvd.mpr (fun h => (Nat.le_of_dvd target.modulus.pos h).not_gt hq)
  · exact hp.d_prime.coprime_iff_not_dvd.mpr (fun h => (Nat.le_of_dvd target.modulus.pos h).not_gt hd)

/-- Theorem 17.12. The exact arithmetic estimates imply Hypothesis 17.11. -/
theorem numberField_selmer_window_bound_of_estimates
    (hplus : HasSelmerPlusTwoWindowEstimates) (hminus : HasSelmerMinusEstimate) :
    HasSelmerWindowBound numberFieldSelmerLengths := by
  apply hasSelmerWindowBound_of_part_estimates
    (plus := numberFieldSelmerSignLengths true) (minus := numberFieldSelmerSignLengths false)
  intro target hprimitive ε hε hεmax e he
  let t (x : ℝ) := Nat.floor (x ^ (401 : ℕ))
  have ht := selmer_cutoff_admitted hε hεmax e he
  obtain ⟨JI, C, P, X₁, hJI, hC, hP, hX₁, hw⟩ :=
    hplus target hprimitive ε hε hεmax e t ht
  obtain ⟨Cm, hCm, hbminus⟩ := hminus
  let o := orderOf target.character
  let J : ℝ := max JI 1
  have hJ : 1 ≤ J := le_max_right _ _
  have hJIJ : JI ≤ J := le_max_left _ _
  have hJpos := zero_lt_one.trans_le hJ
  let K : ℝ := max 3 (max P (target.modulus : ℕ))
  have hK : 0 < K := (by norm_num : (0 : ℝ) < 3).trans_le (le_max_left _ _)
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp
    (eventually_selmerWindowPair_gt_rpow hε K hK (401 * J))
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp (eventually_selmerWindowPair_log_mul_le hε)
  obtain ⟨A₃, hA₃⟩ := exists_selmerHost_log_conductor_mul_cutoff_le target hε hεmax
  let A : ℝ := max 2 (max A₁ (max A₂ A₃))
  let X₀ : ℝ := max 1 (max X₁ (A ^ J))
  refine ⟨J, X₀, C, 3 + 4 * Cm * (o : ℝ) ^ (3 : ℕ), hJ, le_max_left _ _, hC.le,
    by positivity, fun X hX q d hpair => ?_⟩
  let base : ℝ := X ^ (1 / J)
  have hX1 : 1 ≤ X := (le_max_left _ _ : 1 ≤ X₀).trans hX
  have hXpos := zero_lt_one.trans_le hX1
  have hApos : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  have hbase : A ≤ base := by
    have hAX : A ^ J ≤ X := (le_max_right X₁ _).trans ((le_max_right 1 _).trans hX)
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hApos J) hAX (one_div_nonneg.mpr hJpos.le)
    rw [one_div, Real.rpow_rpow_inv hApos hJpos.ne'] at h
    simpa only [base, one_div] using h
  have hbasePow : base ^ (401 * J) = X ^ (401 : ℕ) := by
    have hmul : 1 / J * (401 * J) = (401 : ℝ) := by field_simp
    change (X ^ (1 / J)) ^ (401 * J) = X ^ (401 : ℕ)
    rw [← Real.rpow_mul hXpos.le, hmul, ← Real.rpow_natCast]
    norm_num
  have hA₁base : A₁ ≤ base := ((le_max_left A₁ _).trans (le_max_right 2 _)).trans hbase
  obtain ⟨hqbig, hdbig⟩ := hA₁ base hA₁base q d hpair
  rw [hbasePow] at hqbig hdbig
  have hXpow : 1 ≤ X ^ (401 : ℕ) := one_le_pow₀ hX1
  have hN : (target.modulus : ℝ) ≤ K := (le_max_right P _).trans (le_max_right 3 _)
  have hP' : P ≤ K := (le_max_left _ _).trans (le_max_right 3 _)
  have hKpow : K ≤ K * X ^ (401 : ℕ) := le_mul_of_one_le_right hK.le hXpow
  have hcutoff : 2 * X ^ (401 : ℕ) + 1 ≤ K * X ^ (401 : ℕ) := by
    have h3 : (3 : ℝ) * X ^ (401 : ℕ) ≤ K * X ^ (401 : ℕ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hXpow)
    linarith only [h3, hXpow]
  have hpr : SelmerEstimatePrimePair target q d := selmer_estimate_prime_pair hpair
    (by exact_mod_cast (hN.trans hKpow).trans_lt hqbig)
    (by exact_mod_cast (hN.trans hKpow).trans_lt hdbig)
  have hA₂base : A₂ ≤ base :=
    (((le_max_left A₂ A₃).trans (le_max_right A₁ _)).trans (le_max_right 2 _)).trans hbase
  have hexp : ε / (4 * J) ≤ ε / (4 * JI) :=
    div_le_div_of_nonneg_left hε.le (by positivity) (by gcongr)
  have hlog : Real.log ((q : ℕ) * (d : ℕ) : ℝ) ≤ X ^ (ε / (4 * JI)) := by
    calc
      _ ≤ base ^ (ε / 4) := hA₂ base hA₂base q d hpair
      _ = X ^ (ε / (4 * J)) := by
        change (X ^ (1 / J)) ^ (ε / 4) = _
        rw [← Real.rpow_mul hXpos.le]
        congr 1
        field_simp
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX1 hexp
  have hX₁X : X₁ ≤ X := ((le_max_left X₁ _).trans (le_max_right 1 _)).trans hX
  have hcut := max_le (hP'.trans hKpow) hcutoff
  obtain ⟨Y, hY, hYmax, hparts⟩ :=
    hw X hX₁X q d hpr (hcut.trans_lt hqbig) (hcut.trans_lt hdbig) hlog
  have hbaseY : base ≤ Y :=
    (Real.rpow_le_rpow_of_exponent_le hX1 (one_div_le_one_div_of_le hJI hJIJ)).trans hY
  refine ⟨Y, hbaseY, hYmax, fun x hx => ?_⟩
  have hbaseX := hbaseY.trans hx.1
  have hx2 := hpair.base_ge_two.trans hbaseX
  have hadmitted := ht x hx2
  have htpos : 0 < t x := (by decide : (0 : ℕ) < 2).trans_le hadmitted.2.2.1
  let f := selmerHostConductor target (e x) q d
  have hf : 0 < f := selmerHostConductor_pos target (e x) q d
  have hA₃base : A₃ ≤ base :=
    (((le_max_right A₂ A₃).trans (le_max_right A₁ _)).trans (le_max_right 2 _)).trans hbase
  have hlogft : Real.log ((f : ℝ) * t x) ≤ 2 * x ^ (ε / 4) :=
    hA₃ base hA₃base q d hpair x hbaseX _ _ htpos hadmitted.2.2.2
      (he x ((by norm_num : (1 : ℝ) ≤ 2).trans hx2)).2
  have hpoly := selmerConductorCutoff_rpow_le hf htpos hC.le hlogft
  have hpoly3 : ((f : ℝ) * t x) ^ (3 : ℕ) ≤ Real.exp (6 * x ^ (ε / 4)) := by
    have h := selmerConductorCutoff_rpow_le hf htpos
      (C := ((3 : ℕ) : ℝ)) (by positivity) hlogft
    rw [Real.rpow_natCast, show (2 : ℝ) * ((3 : ℕ) : ℝ) = 6 by norm_num] at h
    exact h
  have hn := selmerHostDegree_le_conductor target (e x) q d
  have hβ := (selmerMinusBudget_le Cm hCm _ _ _ o hn htpos hf).trans
    (mul_le_mul_of_nonneg_left hpoly3 (by positivity))
  obtain ⟨htwo, hpplus⟩ := hparts x hx
  have hpminus := hbminus target hprimitive (e x) (t x) q d hadmitted.1 hadmitted.2.2.1 hpr
  refine ⟨htwo, ⟨hpplus.1, fun primes hprimes =>
      (hpplus.2 primes hprimes).trans (add_le_add hpoly le_rfl)⟩,
    ⟨hpminus.1, fun primes hprimes => (hpminus.2 primes hprimes).trans hβ⟩, ?_⟩
  let _ := selmerHostField_isAbelianGalois target (e x) q d
  exact fun ℓ hℓ hodd i _ => numberFieldSelmerLengths_eq_signLengths_add _ hℓ hodd i

end Riemann
