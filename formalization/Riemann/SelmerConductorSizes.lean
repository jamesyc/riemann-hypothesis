module

public import Riemann.SelmerLengthAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Utilities.ExponentialGrowth

@[expose] public section

open Filter Asymptotics Utilities
open scoped BigOperators Classical

namespace Riemann

theorem exists_selmerHostCyclotomicEmbedding (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (selmerHostField target e q d →ₐ[ℚ] CyclotomicField m ℚ) :=
  ⟨selmerHostModulus target e q d, selmerHostModulus_pos target e q d,
    ⟨(selmerHostField target e q d).val⟩⟩

/-- The conductor of the abelian host is the least positive cyclotomic modulus
whose cyclotomic field admits an embedding of the host. -/
noncomputable def selmerHostConductor (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) : ℕ :=
  Nat.find (exists_selmerHostCyclotomicEmbedding target e q d)

theorem selmerHostConductor_pos (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+) :
    0 < selmerHostConductor target e q d :=
  (Nat.find_spec (exists_selmerHostCyclotomicEmbedding target e q d)).1

/-- An embedding of the host into the cyclotomic field at its conductor. -/
noncomputable def selmerHostConductorEmbedding (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) :
    selmerHostField target e q d →ₐ[ℚ] CyclotomicField (selmerHostConductor target e q d) ℚ := by
  classical
  exact Classical.choice (Nat.find_spec (exists_selmerHostCyclotomicEmbedding target e q d)).2

theorem selmerHostConductor_le_modulus (target : BundledDirichletCharacter) (e : ℕ)
    (q d : ℕ+) : selmerHostConductor target e q d ≤ selmerHostModulus target e q d :=
  Nat.find_min' _ ⟨selmerHostModulus_pos target e q d, ⟨(selmerHostField target e q d).val⟩⟩

theorem selmerHostDegree_le_conductor (target : BundledDirichletCharacter) (e : ℕ)
    (q d : ℕ+) : Module.finrank ℚ (selmerHostField target e q d) ≤ selmerHostConductor target e q d := by
  let f := selmerHostConductor target e q d
  let j := selmerHostConductorEmbedding target e q d
  let : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let : IsCyclotomicExtension {f} ℚ (CyclotomicField f ℚ) :=
    CyclotomicField.isCyclotomicExtension f ℚ
  calc
    _ ≤ Module.finrank ℚ (CyclotomicField f ℚ) :=
      j.toLinearMap.finrank_le_finrank_of_injective j.injective
    _ = f.totient := IsCyclotomicExtension.Rat.finrank f (CyclotomicField f ℚ)
    _ ≤ f := Nat.totient_le _

/-- The logarithmic conductor-times-cutoff estimate in Theorem 17.12 is uniform
over the auxiliary pair and every point to the right of its base. -/
theorem exists_selmerHost_log_conductor_mul_cutoff_le (target : BundledDirichletCharacter)
    {ε : ℝ} (hε : 0 < ε) (hεmax : ε < 1 / 52) :
    ∃ A : ℝ, ∀ base ≥ A, ∀ q d : ℕ+, SelmerWindowPair ε base q d →
      ∀ x ≥ base, ∀ e t : ℕ, 0 < t → (t : ℝ) ≤ x ^ (401 : ℕ) →
        (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * ε) →
        Real.log ((selmerHostConductor target e q d : ℝ) * t) ≤ 2 * x ^ (ε / 4) := by
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp (eventually_selmerWindowPair_log_mul_le hε)
  let N : ℝ := target.modulus
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast target.modulus.pos
  have hgap : 0 < ε / 4 := by positivity
  have hconst := isLittleO_const_rpow_atTop (Real.log 2 + Real.log 4 + Real.log N) hgap
  have hlog := (isLittleO_log_rpow_atTop hgap).const_mul_left (404 : ℝ)
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp ((hconst.add hlog).bound (by norm_num : (0 : ℝ) < 1))
  refine ⟨max A₁ A₂, fun base hbase q d hp x hx e t ht htupper he => ?_⟩
  have hbase1 : 1 ≤ base := (by norm_num : (1 : ℝ) ≤ 2).trans hp.base_ge_two
  have hx1 := hbase1.trans hx
  have hxpos := zero_lt_one.trans_le hx1
  have hqd := (hA₁ base ((le_max_left _ _).trans hbase) q d hp).trans
    (Real.rpow_le_rpow (zero_le_one.trans hbase1) hx hgap.le)
  have hsmall := hA₂ x (((le_max_right _ _).trans hbase).trans hx)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _), one_mul, Real.norm_eq_abs] at hsmall
  have hsmall' := (le_abs_self (Real.log 2 + Real.log 4 + Real.log N + 404 * Real.log x)).trans hsmall
  have heupper : (2 : ℝ) ^ e ≤ 2 * x ^ (3 : ℕ) := he.trans (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith))
  have helog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ e) heupper
  rw [Real.log_pow, Real.log_mul (by norm_num) (pow_ne_zero _ hxpos.ne'), Real.log_pow] at helog
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have htlog := Real.log_le_log htpos htupper
  rw [Real.log_pow] at htlog
  have hfpos : (0 : ℝ) < selmerHostConductor target e q d := by
    exact_mod_cast selmerHostConductor_pos target e q d
  have hqpos : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  have hdpos : (0 : ℝ) < (d : ℕ) := by exact_mod_cast d.pos
  have hfbound : (selmerHostConductor target e q d : ℝ) ≤
      (2 : ℝ) ^ (e + 2) * N * ((q : ℕ) * (d : ℕ)) := by
    rw [← mul_assoc]
    dsimp [N]
    exact_mod_cast (selmerHostConductor_le_modulus target e q d).trans
      (selmerHostModulus_le_product target e q d)
  have hflog := Real.log_le_log hfpos hfbound
  rw [Real.log_mul (by positivity) (mul_ne_zero hqpos.ne' hdpos.ne'),
    Real.log_mul (by positivity) hN.ne', pow_add, Real.log_mul (by positivity) (by norm_num),
    Real.log_pow, show ((2 : ℝ) ^ (2 : ℕ)) = 4 by norm_num] at hflog
  rw [Real.log_mul hfpos.ne' htpos.ne']
  push_cast at helog htlog
  linarith only [helog, htlog, hflog, hqd, hsmall']

/-- The minus budget in Theorem 17.12(II), using the host degree, cutoff,
conductor, and the order of the target character. -/
noncomputable def selmerMinusBudget (C : ℝ) (n t f o : ℕ) : ℝ :=
  3 * n * (t : ℝ) ^ (2 : ℕ) * Real.log ((t : ℝ) * f) +
    C * ∑ ℓ ∈ o.primeFactors.erase 2,
      (ℓ : ℝ) * (n : ℝ) ^ (2 : ℕ) * (t : ℝ) ^ (2 : ℕ) *
        Real.log ((t : ℝ) * ℓ * f) ^ (2 : ℕ)

private theorem log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ (2 : ℕ) ≤ 4 * x := by
  have hx₀ := zero_le_one.trans hx
  have h := Real.log_le_rpow_div hx₀ (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  have hs := pow_le_pow_left₀ (Real.log_nonneg hx) h 2
  rw [div_pow, Real.sq_sqrt hx₀] at hs
  norm_num [div_eq_mul_inv] at hs
  exact (mul_comm x 4) ▸ hs

theorem selmerMinusBudget_le (C : ℝ) (hC : 0 ≤ C) (n t f o : ℕ)
    (hnf : n ≤ f) (ht : 0 < t) (hf : 0 < f) :
    selmerMinusBudget C n t f o ≤ (3 + 4 * C * (o : ℝ) ^ (3 : ℕ)) * ((f : ℝ) * t) ^ (3 : ℕ) := by
  let u : ℝ := (f : ℝ) * t
  have hfr : 1 ≤ (f : ℝ) := by exact_mod_cast hf
  have htr : 1 ≤ (t : ℝ) := by exact_mod_cast ht
  have hnr : (n : ℝ) ≤ f := by exact_mod_cast hnf
  have hu : 1 ≤ u := one_le_mul_of_one_le_of_one_le hfr htr
  let ps := o.primeFactors.erase 2
  have hcard : ps.card ≤ o := by
    calc
      _ ≤ (Finset.Icc 1 o).card := Finset.card_le_card (fun ℓ hℓ => Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hℓ)).pos,
          Nat.le_of_mem_primeFactors (Finset.mem_of_mem_erase hℓ)⟩)
      _ = o := by simp
  have hterm (ℓ : ℕ) (hℓ : ℓ ∈ ps) :
      (ℓ : ℝ) * (n : ℝ) ^ (2 : ℕ) * (t : ℝ) ^ (2 : ℕ) *
        Real.log ((t : ℝ) * ℓ * f) ^ (2 : ℕ) ≤ 4 * (o : ℝ) ^ (2 : ℕ) * u ^ (3 : ℕ) := by
    have hℓo : (ℓ : ℝ) ≤ o := by exact_mod_cast Nat.le_of_mem_primeFactors (Finset.mem_of_mem_erase hℓ)
    have hℓ1 : 1 ≤ (ℓ : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hℓ)).pos
    have hlog : Real.log ((t : ℝ) * ℓ * f) ^ (2 : ℕ) ≤ 4 * (u * ℓ) := by
      rw [show (t : ℝ) * ℓ * f = u * ℓ by dsimp [u]; ring]
      exact log_sq_le_four_mul (one_le_mul_of_one_le_of_one_le hu hℓ1)
    have hlog' := hlog.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hℓo (zero_le_one.trans hu)) (by norm_num))
    calc
      _ ≤ (o : ℝ) * (f : ℝ) ^ (2 : ℕ) * (t : ℝ) ^ (2 : ℕ) * (4 * (u * o)) := by gcongr
      _ = _ := by dsimp [u]; ring
  have hsum :
      (∑ ℓ ∈ ps, (ℓ : ℝ) * (n : ℝ) ^ (2 : ℕ) * (t : ℝ) ^ (2 : ℕ) *
        Real.log ((t : ℝ) * ℓ * f) ^ (2 : ℕ)) ≤ 4 * (o : ℝ) ^ (3 : ℕ) * u ^ (3 : ℕ) := by
    calc
      _ ≤ ∑ _ ∈ ps, 4 * (o : ℝ) ^ (2 : ℕ) * u ^ (3 : ℕ) := Finset.sum_le_sum hterm
      _ = ps.card * (4 * (o : ℝ) ^ (2 : ℕ) * u ^ (3 : ℕ)) := by simp
      _ ≤ (o : ℝ) * (4 * (o : ℝ) ^ (2 : ℕ) * u ^ (3 : ℕ)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by ring
  have hfirst : 3 * n * (t : ℝ) ^ (2 : ℕ) * Real.log ((t : ℝ) * f) ≤ 3 * u ^ (3 : ℕ) := by
    rw [show (t : ℝ) * f = u by exact mul_comm _ _]
    have hlog₀ := Real.log_nonneg hu
    have hlog := (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hu)).trans (by linarith : u - 1 ≤ u)
    calc
      _ ≤ 3 * (f : ℝ) * (t : ℝ) ^ (2 : ℕ) * u := by gcongr
      _ = 3 * u ^ (2 : ℕ) * t := by dsimp [u]; ring
      _ ≤ 3 * u ^ (2 : ℕ) * u := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_mul_of_one_le_left (by positivity) hfr
      _ = _ := by ring
  change _ ≤ (3 + 4 * C * (o : ℝ) ^ (3 : ℕ)) * u ^ (3 : ℕ)
  unfold selmerMinusBudget
  have H := add_le_add hfirst (mul_le_mul_of_nonneg_left hsum hC)
  convert H using 1
  ring

/-- A conductor-times-cutoff logarithmic estimate gives the polynomial-to-
exponential bound used for both signs in the window assembly. -/
theorem selmerConductorCutoff_rpow_le {f t : ℕ} (hf : 0 < f) (ht : 0 < t)
    {ε x C : ℝ} (hC : 0 ≤ C)
    (hlog : Real.log ((f : ℝ) * t) ≤ 2 * x ^ (ε / 4)) :
    ((f : ℝ) * t) ^ C ≤ Real.exp (2 * C * x ^ (ε / 4)) := by
  rw [Real.rpow_def_of_pos (by positivity)]
  exact Real.exp_le_exp.mpr (by calc
    _ ≤ (2 * x ^ (ε / 4)) * C := mul_le_mul_of_nonneg_right hlog hC
    _ = _ := by ring)

end Riemann
