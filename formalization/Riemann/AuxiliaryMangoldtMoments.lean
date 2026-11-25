module

public import Riemann.AuxiliaryPrimeMoments
public import Riemann.AuxiliarySmoothedFamily
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

open MeasureTheory Utilities
open scoped BigOperators Classical

namespace Riemann

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "K" => (Real.log 4 + 4)

/-- Chebyshev's estimate and Abel summation bound the total reciprocal
von Mangoldt mass with one logarithm. -/
theorem auxiliary_vonMangoldt_sum_div_le {Z : ℕ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Finset.Icc 1 Z, Λ n / (n : ℝ)) ≤ K * (1 + Real.log Z) := by
  have hZ₁ : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hZ₀ : (0 : ℝ) < Z := by positivity
  let f (u : ℝ) := u⁻¹
  have hd (u : ℝ) (hu : u ∈ Set.Icc (1 : ℝ) Z) : DifferentiableAt ℝ f u :=
    differentiableAt_id.inv (by change u ≠ 0; linarith [hu.1])
  have hdi : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) Z) := by
    rw [show f = fun u : ℝ => u⁻¹ from rfl, deriv_inv']
    exact (continuousOn_id.pow 2 |>.inv₀ (fun u hu => pow_ne_zero _ (by change u ≠ 0; linarith [hu.1])) |>.neg).integrableOn_Icc
  have hab := sum_mul_eq_sub_integral_mul₀' (f := f) (fun n => Λ n) (ArithmeticFunction.map_zero (f := Λ)) Z hd hdi
  have hs : (∑ n ∈ Finset.Icc 1 Z, Λ n / (n : ℝ)) =
      ∑ n ∈ Finset.Icc 0 Z, f n * Λ n := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ArithmeticFunction.map_zero, mul_zero, zero_add,
      ← Finset.Icc_add_one_left_eq_Ioc]
    exact Finset.sum_congr rfl fun n _ => by simp [f, div_eq_mul_inv, mul_comm]
  have hsum : (∑ n ∈ Finset.Icc 0 Z, Λ n) = Chebyshev.psi Z := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rw [hs, hab, hsum]
  have hi : IntegrableOn (fun u => deriv f u * Chebyshev.psi u) (Set.Ioc (1 : ℝ) Z) := by
    simp only [Chebyshev.psi_eq_sum_Icc]
    exact (integrableOn_mul_sum_Icc (c := fun n => Λ n) zero_le_one hdi).mono_set Set.Ioc_subset_Icc_self
  have hi' : IntegrableOn (fun u : ℝ => -(K * u⁻¹)) (Set.Ioc (1 : ℝ) Z) :=
    ((continuousOn_id.inv₀ (fun u (hu : u ∈ Set.Icc (1 : ℝ) Z) => by change u ≠ 0; linarith [hu.1]))
      |>.const_mul K |>.neg |>.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hI : -(K * Real.log Z) ≤
      ∫ u in Set.Ioc (1 : ℝ) Z, deriv f u * ∑ n ∈ Finset.Icc 0 ⌊u⌋₊, Λ n := by
    have hh := setIntegral_mono_on hi' hi measurableSet_Ioc (f := fun u => -(K * u⁻¹))
      (g := fun u => deriv f u * Chebyshev.psi u) (fun u hu => by
        have hu₀ : 0 < u := by linarith [hu.1]
        have H := mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self hu₀.le)
          (show 0 ≤ (u ^ 2)⁻¹ by positivity)
        rw [show f = fun u : ℝ => u⁻¹ from rfl, deriv_inv]
        rw [show (u ^ 2)⁻¹ * (K * u) = K * u⁻¹ by field_simp] at H
        linarith)
    rw [← intervalIntegral.integral_of_le hZ₁, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one hZ₀, div_one] at hh
    simpa only [Chebyshev.psi_eq_sum_Icc] using hh
  have hψ : f Z * Chebyshev.psi Z ≤ K := by
    change (Z : ℝ)⁻¹ * Chebyshev.psi Z ≤ K
    have hp := mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self hZ₀.le)
      (inv_nonneg.mpr hZ₀.le)
    calc
      _ ≤ (Z : ℝ)⁻¹ * (K * Z) := hp
      _ = _ := by rw [mul_left_comm, inv_mul_cancel₀ hZ₀.ne', mul_one]
  linarith

/-- A single coefficient weight covers the smoothed sum and, below its
left cutoff, the partial sum. -/
noncomputable def auxiliaryMangoldtWeight (y : ℝ) (n : ℕ) : ℝ :=
  Λ n * min 1 (y / n)

theorem auxiliaryMangoldtWeight_nonneg {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    0 ≤ auxiliaryMangoldtWeight y n := by
  unfold auxiliaryMangoldtWeight
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))

/-- The total mass bound is uniform in the cutoff and the twist. -/
theorem auxiliaryMangoldtWeight_sum_le {Z : ℕ} (hZ : 1 ≤ Z) {y : ℝ} (hy : 0 ≤ y) :
    (∑ n ∈ Finset.Icc 1 Z, auxiliaryMangoldtWeight y n) ≤ K * y * (1 + Real.log Z) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Z, y * (Λ n / (n : ℝ)) := by
      refine Finset.sum_le_sum fun n _ => ?_
      unfold auxiliaryMangoldtWeight
      calc
        _ ≤ Λ n * (y / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) ArithmeticFunction.vonMangoldt_nonneg
        _ = _ := by ring
    _ = y * ∑ n ∈ Finset.Icc 1 Z, Λ n / (n : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ y * (K * (1 + Real.log Z)) :=
      mul_le_mul_of_nonneg_left (auxiliary_vonMangoldt_sum_div_le hZ) hy
    _ = _ := by ring

/-- The exceptional squarefree parts in §5.3, restricted to the range
needed for the mean square. -/
noncomputable def auxiliaryExceptionalParts (z : ℝ) (sStar Z : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Z ^ (2 : ℕ))).filter fun s =>
    Squarefree s ∧
      let large := (s.primeFactors.filter fun p : ℕ => z < (p : ℝ)).prod id
      large = 1 ∨ large = sStar

/-- The diagonal and exceptional coefficient masses in Lemma 5.5.
The weight itself has no Dirichlet or Legendre factor. -/
theorem exists_auxiliaryExceptionalMangoldtMass :
    ∃ D ≥ (0 : ℝ), ∀ (Z sStar : ℕ) (z y : ℝ),
      3 ≤ y → y ≤ Z → 2 ≤ z → z * Real.log y ≤ Real.sqrt y → 0 < sStar →
      (∀ p ∈ sStar.primeFactors, z < (p : ℝ)) →
      (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        if IsExceptionalLegendreProduct (auxiliaryExceptionalParts z sStar Z) n m then
          auxiliaryMangoldtWeight y n * auxiliaryMangoldtWeight y m else 0) ≤
          D * y * Real.log (2 * y) := by
  sorry

/-- The progression-specific inputs for the common Legendre mean square.
The coefficient identity says that removing the varying quadratic twist
leaves a fixed bounded coefficient family throughout the truncation range. -/
structure AuxiliaryLegendreMomentInput {ι : Type*} (pool : Finset ℕ)
    (χ : ℕ → ι → BundledDirichletCharacter) (Z : ℕ) (X z : ℝ) where
  error : ℝ
  exception : ℕ
  baseCoefficient : ι → ℕ → ℂ
  error_nonneg : 0 ≤ error
  error_small : error * (2 * X) * (1 + Real.log Z) ^ (2 : ℕ) ≤ 1
  exception_pos : 0 < exception
  exception_support : ∀ p ∈ exception.primeFactors, z < (p : ℝ)
  prime_range : ∀ q ∈ pool, q.Prime ∧ Z < q
  correlation : ∀ s : ℕ, Squarefree s → 1 < s → s ≤ Z ^ (2 : ℕ) →
    s ∉ auxiliaryExceptionalParts z exception Z →
    ‖∑ q ∈ pool, auxiliaryLegendre q s‖ ≤ error * pool.card
  base_norm : ∀ i n, ‖baseCoefficient i n‖ ≤ 1
  coefficients : ∀ q ∈ pool, ∀ i n, n ∈ Finset.Icc 1 Z →
    auxiliarySmoothedCoefficients (χ q i) n =
      (Λ n : ℂ) * baseCoefficient i n * auxiliaryLegendre q n

private theorem auxiliaryLegendre_weighted_meanSquare {ι : Type*} {pool : Finset ℕ}
    {χ : ℕ → ι → BundledDirichletCharacter} {Z W : ℕ} {X z D y : ℝ}
    (h : AuxiliaryLegendreMomentInput pool χ Z X z)
    (hW : W ≤ Z) (hy : 3 ≤ y) (hyX : y ≤ 2 * X) (hyZ : y ≤ (Z : ℝ))
    (hmass : (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
      if IsExceptionalLegendreProduct (auxiliaryExceptionalParts z h.exception Z) n m then
        auxiliaryMangoldtWeight y n * auxiliaryMangoldtWeight y m else 0) ≤
      D * y * Real.log (2 * y)) (i : ι) :
    (∑ q ∈ pool, ‖∑ n ∈ Finset.Icc 1 W,
      ((auxiliaryMangoldtWeight y n : ℝ) : ℂ) * h.baseCoefficient i n * auxiliaryLegendre q n‖ ^
        (2 : ℕ)) ≤ (D + 2 * K ^ (2 : ℕ)) * pool.card * y * Real.log (2 * y) := by
  let bad := auxiliaryExceptionalParts z h.exception Z
  let c (n : ℕ) := ((auxiliaryMangoldtWeight y n : ℝ) : ℂ) * h.baseCoefficient i n
  have hy₀ : 0 ≤ y := by linarith
  have hZ : 1 ≤ Z := by exact_mod_cast (show (1 : ℝ) ≤ Z by linarith)
  have hWZ : Finset.Icc 1 W ⊆ Finset.Icc 1 Z := Finset.Icc_subset_Icc_right hW
  have hn (n : ℕ) : ‖c n‖ ≤ auxiliaryMangoldtWeight y n := by
    dsimp only [c]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (auxiliaryMangoldtWeight_nonneg hy₀ n)]
    exact mul_le_of_le_one_right (auxiliaryMangoldtWeight_nonneg hy₀ n) (h.base_norm i n)
  have hE :
      (∑ n ∈ Finset.Icc 1 W, ∑ m ∈ Finset.Icc 1 W,
        if IsExceptionalLegendreProduct bad n m then ‖c n‖ * ‖c m‖ else 0) ≤
        D * y * Real.log (2 * y) := by
    refine le_trans ?_ hmass
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 W, ∑ m ∈ Finset.Icc 1 W,
          if IsExceptionalLegendreProduct bad n m then
            auxiliaryMangoldtWeight y n * auxiliaryMangoldtWeight y m else 0 := by
        refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_
        split_ifs
        · exact mul_le_mul (hn n) (hn m) (norm_nonneg _) (auxiliaryMangoldtWeight_nonneg hy₀ n)
        · rfl
      _ ≤ _ := by
        refine (Finset.sum_le_sum fun n _ => Finset.sum_le_sum_of_subset_of_nonneg hWZ ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg hWZ ?_)
        · intro m _ _
          split_ifs <;> positivity [auxiliaryMangoldtWeight_nonneg hy₀ n, auxiliaryMangoldtWeight_nonneg hy₀ m]
        · intro n _ _
          refine Finset.sum_nonneg fun m _ => ?_
          split_ifs <;> positivity [auxiliaryMangoldtWeight_nonneg hy₀ n, auxiliaryMangoldtWeight_nonneg hy₀ m]
  have hL₁ : (∑ n ∈ Finset.Icc 1 W, ‖c n‖) ≤ K * y * (1 + Real.log Z) := by
    refine (Finset.sum_le_sum fun n _ => hn n).trans ?_
    exact (Finset.sum_le_sum_of_subset_of_nonneg hWZ
      (fun n _ _ => auxiliaryMangoldtWeight_nonneg hy₀ n)).trans (auxiliaryMangoldtWeight_sum_le hZ hy₀)
  have hη : h.error * y * (1 + Real.log Z) ^ (2 : ℕ) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyX h.error_nonneg) (by positivity)).trans h.error_small
  have hnoise : h.error * (K * y * (1 + Real.log Z)) ^ (2 : ℕ) ≤ K ^ (2 : ℕ) * y := by
    calc
      _ = (K ^ (2 : ℕ) * y) * (h.error * y * (1 + Real.log Z) ^ (2 : ℕ)) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hη
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * y) := by
    have hInv : (2 * y)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    linarith [Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 2 * y)]
  have hnoise' : K ^ (2 : ℕ) * y ≤ (2 * K ^ (2 : ℕ)) * y * Real.log (2 * y) := by
    nlinarith only [mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 2 * K ^ (2 : ℕ) * y by positivity)]
  have hmoment := auxiliaryLegendre_meanSquare_le_of_masses pool bad h.error_nonneg
    (fun q hq => ⟨(h.prime_range q hq).1, hW.trans_lt (h.prime_range q hq).2⟩)
    (fun s hs hs₁ hsW hbad => h.correlation s hs hs₁
      (hsW.trans (Nat.pow_le_pow_left hW _)) hbad) c hE hL₁
  refine hmoment.trans ?_
  calc
    _ ≤ (pool.card : ℝ) * (D * y * Real.log (2 * y) + (2 * K ^ (2 : ℕ)) * y * Real.log (2 * y)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (hnoise.trans hnoise')) (by positivity)
    _ = _ := by ring

private theorem sum_Icc_zero_eq_one {f : ℕ → ℂ} {W : ℕ} (hf : f 0 = 0) :
    ∑ n ∈ Finset.Icc 0 W, f n = ∑ n ∈ Finset.Icc 1 W, f n := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hf, zero_add, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

/-- Both moments follow from one weighted Legendre estimate. The partial
sum is the same weight restricted to the integers below its argument. -/
theorem auxiliarySmoothedMoments_of_legendreInput {ι : Type*} {pool : Finset ℕ}
    {χ : ℕ → ι → BundledDirichletCharacter} {Z : ℕ} {Y X z D : ℝ}
    (h : AuxiliaryLegendreMomentInput pool χ Z X z)
    (hY : 3 ≤ Y) (hX : 0 ≤ X) (hZ : 2 * X ≤ Z)
    (hmass : ∀ y ∈ Set.Icc Y (2 * X),
      (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        if IsExceptionalLegendreProduct (auxiliaryExceptionalParts z h.exception Z) n m then
          auxiliaryMangoldtWeight y n * auxiliaryMangoldtWeight y m else 0) ≤
          D * y * Real.log (2 * y)) :
    AuxiliarySmoothedMomentBounds pool χ Z Y X (D + 2 * K ^ (2 : ℕ)) := by
  intro i
  constructor
  · intro y hy
    have hyX : y ≤ 2 * X := hy.2.trans (by linarith)
    have hm := auxiliaryLegendre_weighted_meanSquare h le_rfl (hY.trans hy.1) hyX (hyX.trans hZ)
      (hmass y ⟨hy.1, hyX⟩) i
    refine le_trans (le_of_eq ?_) hm
    refine Finset.sum_congr rfl fun q hq => ?_
    have he : truncatedAuxiliarySmoothedSum (auxiliarySmoothedCoefficients (χ q i)) Z y =
        ∑ n ∈ Finset.Icc 1 Z, ((auxiliaryMangoldtWeight y n : ℝ) : ℂ) *
          h.baseCoefficient i n * auxiliaryLegendre q n := by
      unfold truncatedAuxiliarySmoothedSum
      rw [sum_Icc_zero_eq_one (by simp [auxiliarySmoothedCoefficients, ArithmeticFunction.map_zero])]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [h.coefficients q hq i n hn, auxiliaryMangoldtWeight, Complex.ofReal_mul]
      ring
    rw [he]
  · intro u hu
    have hW : Nat.floor u ≤ Z := Nat.floor_le_of_le (hu.2.trans hZ)
    have hm := auxiliaryLegendre_weighted_meanSquare h hW (hY.trans hu.1) hu.2 (hu.2.trans hZ)
      (hmass u hu) i
    refine le_trans (le_of_eq ?_) hm
    refine Finset.sum_congr rfl fun q hq => ?_
    have he : auxiliaryPartialSum (auxiliarySmoothedCoefficients (χ q i)) u =
        ∑ n ∈ Finset.Icc 1 (Nat.floor u), ((auxiliaryMangoldtWeight u n : ℝ) : ℂ) *
          h.baseCoefficient i n * auxiliaryLegendre q n := by
      unfold auxiliaryPartialSum
      rw [sum_Icc_zero_eq_one (by simp [auxiliarySmoothedCoefficients, ArithmeticFunction.map_zero])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn₀ : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnu : (n : ℝ) ≤ u := (Nat.le_floor_iff (by linarith [hY.trans hu.1] : 0 ≤ u)).mp (Finset.mem_Icc.mp hn).2
      rw [h.coefficients q hq i n (Finset.Icc_subset_Icc_right hW hn), auxiliaryMangoldtWeight,
        min_eq_left ((one_le_div hn₀).mpr hnu), mul_one]
    rw [he]

end Riemann
