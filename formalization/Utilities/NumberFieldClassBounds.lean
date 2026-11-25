module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Utilities.RootDiscriminant
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.Ideal.Int

@[expose] public section

open scoped BigOperators NumberField Real nonZeroDivisors
open Finset NumberField IsDedekindDomain

namespace Utilities

private def boundedPositiveTuples (ι : Type*) [Fintype ι] [DecidableEq ι] (M : ℕ) :
    Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι => Icc 1 M).filter (fun a => ∏ i, a i ≤ M)

private theorem card_boundedPositiveTuples_le (ι : Type*) [Fintype ι] [DecidableEq ι] (M : ℕ) :
    ((boundedPositiveTuples ι M).card : ℝ) ≤ (M : ℝ) ^ 2 * 2 ^ Fintype.card ι := by
  classical
  let T := Fintype.piFinset fun _ : ι => Icc 1 M
  let w (a : ι → ℕ) : ℝ := ∏ i, 1 / (a i : ℝ) ^ (2 : ℕ)
  have hterm (a : ι → ℕ) (ha : a ∈ boundedPositiveTuples ι M) :
      (1 : ℝ) ≤ (M : ℝ) ^ 2 * w a := by
    rw [boundedPositiveTuples] at ha
    obtain ⟨hvals, hprod⟩ := Finset.mem_filter.mp ha
    have hp : (0 : ℝ) < ∏ i, (a i : ℝ) := Finset.prod_pos fun i _ =>
      Nat.cast_pos.mpr ((Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hvals) i)).1)
    have hpM : (∏ i, (a i : ℝ)) ≤ M := by exact_mod_cast hprod
    dsimp only [w]
    rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_pow, ← div_eq_mul_one_div]
    exact (le_div_iff₀ (pow_pos hp _)).mpr
      (by simpa using pow_le_pow_left₀ hp.le hpM (2 : ℕ))
  have hs : (∑ a ∈ Icc 1 M, 1 / (a : ℝ) ^ (2 : ℕ)) ≤ 2 := by
    exact (sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two).trans
      (by nlinarith [Real.pi_pos, Real.pi_lt_d2])
  have hsubset : boundedPositiveTuples ι M ⊆ T := by
    unfold boundedPositiveTuples T
    exact Finset.filter_subset _ _
  calc
    _ = ∑ _ ∈ boundedPositiveTuples ι M, (1 : ℝ) := by simp
    _ ≤ ∑ a ∈ boundedPositiveTuples ι M, (M : ℝ) ^ 2 * w a := Finset.sum_le_sum hterm
    _ ≤ ∑ a ∈ T, (M : ℝ) ^ 2 * w a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by dsimp [w]; positivity)
    _ = (M : ℝ) ^ 2 * ∏ _ : ι, (∑ a ∈ Icc 1 M, 1 / (a : ℝ) ^ (2 : ℕ)) := by
      rw [← Finset.mul_sum, Finset.prod_univ_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Finset.prod_const, Finset.card_univ] using
        (Finset.prod_le_prod₀ (s := (Finset.univ : Finset ι))
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (fun _ _ => hs))

private theorem prod_filterColumns {V : Type*} {n : ℕ} (q : V → ℕ) (idx : V → Fin n)
    (s : Multiset V) :
    (∏ j, ((s.filter (idx · = j)).map q).prod) = (s.map q).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have h (i : Fin n) :
        (((a ::ₘ s).filter (idx · = i)).map q).prod =
          (if idx a = i then q a else 1) * ((s.filter (idx · = i)).map q).prod := by
      by_cases hi : idx a = i <;> simp [hi]
    simp only [h, Finset.prod_mul_distrib, ih, Finset.prod_ite_eq, Finset.mem_univ, ite_true,
      Multiset.map_cons, Multiset.prod_cons]

private theorem multiset_eq_of_filterColumn_products {V : Type*} {n : ℕ} (q : V → ℕ)
    (idx : V → Fin n) (hq : ∀ v, (q v).Prime)
    (hinj : ∀ x y, q x = q y → idx x = idx y → x = y)
    {s t : Multiset V}
    (h : ∀ j, ((s.filter (idx · = j)).map q).prod = ((t.filter (idx · = j)).map q).prod) :
    s = t := by
  classical
  have hfac (u : Multiset V) : UniqueFactorizationMonoid.normalizedFactors (u.map q).prod = u.map q := by
    apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    rintro p hp
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hp
    exact (hq v).prime
  have hpairs : Function.Injective (fun v => (idx v, q v)) :=
    fun x y hxy => hinj x y (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  have hcol (j : Fin n) : s.filter (idx · = j) = t.filter (idx · = j) := by
    have hq' : (s.filter (idx · = j)).map q = (t.filter (idx · = j)).map q := by
      rw [← hfac, h j, hfac]
    have hmap (u : Multiset V) :
        (u.filter (idx · = j)).map (fun v => (idx v, q v)) =
          ((u.filter (idx · = j)).map q).map (fun p => (j, p)) := by
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro v hv
      simp [(Multiset.mem_filter.mp hv).2]
    apply Multiset.map_injective hpairs
    rw [hmap, hmap, hq']
  ext v
  have hcount := congrArg (Multiset.count v) (hcol (idx v))
  change Multiset.count v (s.filter fun w => idx w = idx v) =
    Multiset.count v (t.filter fun w => idx w = idx v) at hcount
  rw [Multiset.count_filter_of_pos (p := fun w => idx w = idx v) (s := s) rfl,
    Multiset.count_filter_of_pos (p := fun w => idx w = idx v) (s := t) rfl] at hcount
  exact hcount

private theorem exists_fiberwise_injective_index {V : Type*} {n : ℕ} (q : V → ℕ)
    (h : ∀ p, ∃ S : Finset V, S.card ≤ n ∧ ∀ x, q x = p → x ∈ S) :
    ∃ idx : V → Fin n, ∀ x y, q x = q y → idx x = idx y → x = y := by
  choose S hS hcov using h
  have he (p : ℕ) : Nonempty (S p ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hS p)
  let e (p : ℕ) := (he p).some
  refine ⟨fun x => e (q x) ⟨x, hcov _ x rfl⟩, fun x y hxy hidx => ?_⟩
  have hy (p : ℕ) (hp : q y = p) :
      e (q y) ⟨y, hcov _ y rfl⟩ = e p ⟨y, hcov _ y hp⟩ := by subst p; rfl
  change e (q x) ⟨x, _⟩ = e (q y) ⟨y, _⟩ at hidx
  rw [hy (q x) hxy.symm] at hidx
  exact congrArg Subtype.val ((e (q x)).injective hidx)

private theorem exists_heightOne_factors (K : Type*) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ s : Multiset (HeightOneSpectrum (𝓞 K)), (s.map (fun v => v.asIdeal)).prod = I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hI rfl).elim
  | h₂ x hx => exact ⟨0, by simpa using (isUnit_iff_eq_one.mp hx).symm⟩
  | h₃ a p ha hp ih =>
    obtain ⟨s, hs⟩ := ih ha
    exact ⟨⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ ::ₘ s, by simp [hs]⟩

/-- The number of primes over a nonzero rational prime ideal is bounded by the degree. -/
theorem card_primesOverFinset_le_numberField_degree (K : Type*) [Field K] [NumberField K]
    {p : Ideal ℤ} [p.IsPrime] (hp : p ≠ ⊥) :
    (primesOverFinset p (𝓞 K)).card ≤ Module.finrank ℚ K := by
  classical
  let _ : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  let t := primesOverFinset p (𝓞 K)
  let e : t ≃ p.primesOver (𝓞 K) :=
    Equiv.subtypeEquivRight (fun q => mem_primesOverFinset_iff hp (P := q))
  let _ : Fintype (p.primesOver (𝓞 K)) := Fintype.ofEquiv t e
  have hdeg : Module.finrank ℤ (𝓞 K) = Module.finrank ℚ K :=
    (IsFractionRing.finrank_eq ℤ ℚ (𝓞 K) K).symm
  rw [← Fintype.card_coe t, Fintype.card_congr e, ← hdeg,
    ← Ideal.sum_ramification_inertia_eq_finrank p (𝓞 K), Fintype.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro q _
  let _ : q.val.IsPrime := q.property.1
  exact Nat.succ_le_of_lt (Nat.mul_pos (q.val.ramificationIdx_pos ℤ) (q.val.inertiaDeg_pos ℤ))

/-- The possible valuation residues at primes over ℓ contribute at most
one `ZMod ℓ` coordinate per field degree. -/
theorem card_numberFieldPrimeValuationResidues_le (K : Type*) [Field K] [NumberField K]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Nat.card ((primesOverFinset (Ideal.span {(ℓ : ℤ)}) (𝓞 K)) → ZMod ℓ) ≤
      ℓ ^ Module.finrank ℚ K := by
  have hp : ℓ.Prime := Fact.out
  let p : Ideal ℤ := Ideal.span {(ℓ : ℤ)}
  have hpzero : p ≠ ⊥ := by simpa [p] using hp.ne_zero
  let _ : p.IsPrime := Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp hp)
  have hcard := card_primesOverFinset_le_numberField_degree K hpzero
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Nat.pow_le_pow_right hp.pos hcard

private theorem card_ideals_absNorm_le_boundedTuples (K : Type*) [Field K] [NumberField K]
    (M : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤
      (boundedPositiveTuples (Fin (Module.finrank ℚ K)) M).card := by
  classical
  let q (v : HeightOneSpectrum (𝓞 K)) : ℕ := Ideal.absNorm (v.asIdeal.under ℤ)
  have hq (v : HeightOneSpectrum (𝓞 K)) : (q v).Prime := by
    let _ := v.isPrime
    let _ : NeZero v.asIdeal := ⟨v.ne_bot⟩
    exact Nat.absNorm_under_prime v.asIdeal
  have hqle (v : HeightOneSpectrum (𝓞 K)) : q v ≤ Ideal.absNorm v.asIdeal :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot))
      (Int.absNorm_under_dvd_absNorm v.asIdeal)
  obtain ⟨idx, hidx⟩ := exists_fiberwise_injective_index (n := Module.finrank ℚ K) q (by
    intro p
    by_cases hp : p.Prime
    · let _ : Fact p.Prime := ⟨hp⟩
      have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
      let _ : (Ideal.span {(p : ℤ)}).IsPrime :=
        Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp hp)
      let S := primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)
      have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) :=
        fun _ _ h => HeightOneSpectrum.ext h
      refine ⟨S.preimage (fun v => v.asIdeal) hinj.injOn, ?_, ?_⟩
      · refine (Finset.card_le_card_of_injOn (fun v => v.asIdeal) ?_ hinj.injOn).trans
          (card_primesOverFinset_le_numberField_degree K hbot)
        intro v hv
        exact Finset.mem_preimage.mp hv
      · intro v hv
        exact Finset.mem_preimage.mpr ((mem_primesOverFinset_iff hbot _).mpr
          ⟨v.isPrime, hv ▸ Int.liesOver_span_absNorm v.asIdeal⟩)
    · exact ⟨∅, by simp, fun v h => (hp (h ▸ hq v)).elim⟩)
  choose s hs using exists_heightOne_factors K
  rw [← Nat.card_eq_finsetCard]
  have hprod (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : ((s I hI).map q).prod ≤ Ideal.absNorm I := by
    conv_rhs => rw [← hs I hI, map_multiset_prod, Multiset.map_map]
    exact Multiset.prod_map_le_prod_map _ _ (fun v _ => hqle v)
  have hpos (u : Multiset (HeightOneSpectrum (𝓞 K))) : 0 < (u.map q).prod := by
    apply Multiset.prod_pos
    intro a ha
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (hq v).pos
  refine Nat.card_le_card_of_injective
    (fun I => ⟨fun j => (((s I.1 I.2.1).filter (idx · = j)).map q).prod, ?_⟩) ?_
  · have hP := (prod_filterColumns q idx (s I.1 I.2.1)).trans_le ((hprod I.1 I.2.1).trans I.2.2)
    rw [boundedPositiveTuples, Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun j => Finset.mem_Icc.mpr ⟨hpos _, (Finset.single_le_prod
      (fun l _ => hpos ((s I.1 I.2.1).filter (idx · = l))) (Finset.mem_univ j)).trans hP⟩, hP⟩
  · intro I J hIJ
    have h := multiset_eq_of_filterColumn_products q idx hq hidx (congrFun (congrArg Subtype.val hIJ))
    apply Subtype.ext
    rw [← hs I.1 I.2.1, ← hs J.1 J.2.1, h]

private theorem two_pow_mul_factorial_le (n : ℕ) :
    (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hBernoulli := one_add_mul_le_pow (a := (((n + 1 : ℕ) : ℝ))⁻¹)
      (le_trans (by norm_num : (-2 : ℝ) ≤ 0) (inv_nonneg.mpr hn.le)) (n + 1)
    rw [mul_inv_cancel₀ hn.ne'] at hBernoulli
    have hpow : 2 * ((n + 1 : ℕ) : ℝ) ^ (n + 1) ≤ ((n + 1 + 1 : ℕ) : ℝ) ^ (n + 1) := by
      have heq : ((n + 1 + 1 : ℕ) : ℝ) =
          (1 + (((n + 1 : ℕ) : ℝ))⁻¹) * ((n + 1 : ℕ) : ℝ) := by
        rw [add_mul, inv_mul_cancel₀ hn.ne']; push_cast; ring
      rw [heq, mul_pow]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc
      _ = ((n + 1 + 1 : ℕ) : ℝ) * (2 * (2 ^ n * ((n + 1).factorial : ℝ))) := by
        rw [Nat.factorial_succ (n + 1), Nat.cast_mul, pow_succ]; ring
      _ ≤ ((n + 1 + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by gcongr
      _ ≤ ((n + 1 + 1 : ℕ) : ℝ) * ((n + 1 + 1 : ℕ) : ℝ) ^ (n + 1) := by gcongr
      _ = _ := by ring

private theorem minkowskiPrefactor_le_one (n r : ℕ) (hn : 0 < n) (hr : 2 * r ≤ n) :
    (4 / Real.pi) ^ r * ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpi : (4 / Real.pi) ≤ 2 :=
    (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have hpow : (4 / Real.pi) ^ r ≤ (2 : ℝ) ^ m :=
    (pow_le_pow_left₀ (by positivity) hpi r).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  rw [← mul_div_assoc, div_le_one (by positivity)]
  exact (mul_le_mul_of_nonneg_right hpow (by positivity)).trans (two_pow_mul_factorial_le m)

private theorem classNumber_le_card_small_ideals (K : Type*) [Field K] [NumberField K] :
    classNumber K ≤ Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧
      Ideal.absNorm I ≤ ⌊√|(discr K : ℝ)|⌋₊} := by
  classical
  let M := ⌊√|(discr K : ℝ)|⌋₊
  have hfinite : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ M}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 K) M).subset (fun _ h => h.2)
  have : Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} := hfinite.to_subtype
  rw [classNumber, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_surjective
    (fun I => ClassGroup.mk0 (⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩ :
      nonZeroDivisors (Ideal (𝓞 K)))) ?_
  intro C
  obtain ⟨I, hI, hnorm⟩ := exists_ideal_in_class_of_norm_le C
  refine ⟨⟨I.1, nonZeroDivisors.coe_ne_zero I, ?_⟩, hI⟩
  apply Nat.le_floor
  refine hnorm.trans ?_
  have h := minkowskiPrefactor_le_one (Module.finrank ℚ K) (InfinitePlace.nrComplexPlaces K)
    Module.finrank_pos (by have := InfinitePlace.card_add_two_mul_card_eq_rank K; omega)
  rw [← mul_assoc]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) h

/-- Count ideal representatives with a square-norm weight and bound the
resulting finite Dirichlet sums by `ζ(2)^n`. -/
theorem log_classNumber_le_log_abs_discr_add (K : Type*) [Field K] [NumberField K] :
    Real.log (classNumber K : ℝ) ≤ Real.log |(discr K : ℝ)| + Module.finrank ℚ K * Real.log 2 := by
  let D : ℝ := |(discr K : ℝ)|
  let s := Real.sqrt D
  let M := Nat.floor s
  let n := Module.finrank ℚ K
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  have hcount : (classNumber K : ℝ) ≤ (M : ℝ) ^ 2 * 2 ^ n := by
    calc
      _ ≤ ((boundedPositiveTuples (Fin n) M).card : ℝ) := by
        exact_mod_cast (classNumber_le_card_small_ideals K).trans
          (card_ideals_absNorm_le_boundedTuples K M)
      _ ≤ _ := by simpa only [Fintype.card_fin] using card_boundedPositiveTuples_le (Fin n) M
  have hMs : (M : ℝ) ≤ s := Nat.floor_le (by dsimp [s]; positivity)
  have hMD : (M : ℝ) ^ (2 : ℕ) ≤ D :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hMs _).trans_eq (Real.sq_sqrt (zero_le_one.trans hD))
  have hclass : (classNumber K : ℝ) ≤ D * 2 ^ n :=
    hcount.trans (mul_le_mul_of_nonneg_right hMD (by positivity))
  calc
    _ ≤ Real.log (D * 2 ^ n) :=
      Real.log_le_log (Nat.cast_pos.mpr (classNumber_pos K)) hclass
    _ = _ := by
      rw [Real.log_mul (zero_lt_one.trans_le hD).ne' (by positivity), Real.log_pow]

/-- A class-number estimate in terms of the degree and a cyclotomic modulus. -/
theorem log_classNumber_le_of_cyclotomic_embedding (E : Type*) [Field E] [NumberField E]
    (N : ℕ) (hN : 2 ≤ N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) :
    Real.log (classNumber E : ℝ) ≤ 2 * Module.finrank ℚ E * Real.log N := by
  have hD : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr
    (by exact_mod_cast NumberField.discr_ne_zero E)
  have hDpow : |(discr E : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ E := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (show ((NumberField.discr E).natAbs : ℝ) ≤ (N : ℝ) ^ Module.finrank ℚ E by
        exact_mod_cast natAbs_discr_le_pow_of_cyclotomic_embedding E N (by omega) j)
  have hDlog := Real.log_le_log hD hDpow
  rw [Real.log_pow] at hDlog
  have hlog2 : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  calc
    _ ≤ Real.log |(discr E : ℝ)| + Module.finrank ℚ E * Real.log 2 :=
      log_classNumber_le_log_abs_discr_add E
    _ ≤ (Module.finrank ℚ E : ℝ) * Real.log N + Module.finrank ℚ E * Real.log N :=
      add_le_add hDlog (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _))
    _ = _ := by ring

theorem finrank_cyclotomicField_le_totient (F : Type*) [Field F] [CharZero F]
    (p : ℕ) [NeZero p] :
    Module.finrank F (CyclotomicField p F) ≤ p.totient := by
  let L := CyclotomicField p F
  let _ : NeZero (p : F) := ⟨by exact_mod_cast NeZero.ne p⟩
  let _ : IsCyclotomicExtension {p} F L := CyclotomicField.isCyclotomicExtension p F
  let ζ := IsCyclotomicExtension.zeta p F L
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p F L
  have hdiv : minpoly F ζ ∣ Polynomial.cyclotomic p F := by
    apply minpoly.dvd
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos p)
  rw [(hζ.powerBasis F).finrank, IsPrimitiveRoot.powerBasis_dim, ← Polynomial.natDegree_cyclotomic p F]
  exact Polynomial.natDegree_le_of_dvd hdiv (Polynomial.cyclotomic.monic _ _).ne_zero

/-- Adjoining a root of unity to a cyclotomic subfield remains inside the
cyclotomic field at the product modulus. -/
theorem nonempty_algHom_cyclotomicField_mul_of_algHom (F : Type*) [Field F] [NumberField F]
    (p f : ℕ) [NeZero p] [NeZero f] (j : F →ₐ[ℚ] CyclotomicField f ℚ) :
    Nonempty (CyclotomicField p F →ₐ[ℚ] CyclotomicField (p * f) ℚ) := by
  let C := CyclotomicField f ℚ
  let K := CyclotomicField (p * f) ℚ
  let _ : NeZero (p * f) := ⟨mul_ne_zero (NeZero.ne p) (NeZero.ne f)⟩
  let _ : NeZero (f : ℚ) := ⟨by exact_mod_cast NeZero.ne f⟩
  let _ : NeZero ((p * f : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne (p * f)⟩
  let _ : IsCyclotomicExtension {p * f} ℚ K := CyclotomicField.isCyclotomicExtension (p * f) ℚ
  let _ : IsCyclotomicExtension {f} ℚ C := CyclotomicField.isCyclotomicExtension f ℚ
  let ζ := IsCyclotomicExtension.zeta (p * f) ℚ K
  have hK : IsPrimitiveRoot ζ (p * f) := IsCyclotomicExtension.zeta_spec (p * f) ℚ K
  have hf : IsPrimitiveRoot (ζ ^ p) f := IsPrimitiveRoot.pow (NeZero.pos _) hK rfl
  have hp : IsPrimitiveRoot (ζ ^ f) p := IsPrimitiveRoot.pow (NeZero.pos _) hK (mul_comm p f)
  let jC : C →ₐ[ℚ] K :=
    ((IsCyclotomicExtension.zeta_spec f ℚ C).embeddingsEquivPrimitiveRoots K
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos f))).symm
        ⟨_, (mem_primitiveRoots (NeZero.pos f)).mpr hf⟩
  let jF := jC.comp j
  let _ : Algebra F K := jF.toRingHom.toAlgebra
  let _ : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq' jF.comp_algebraMap.symm
  let T := IntermediateField.adjoin F ({ζ ^ f} : Set K)
  let _ : IsCyclotomicExtension {p} F T := hp.intermediateField_adjoin_isCyclotomicExtension F
  let _ : IsCyclotomicExtension {p} F (CyclotomicField p F) := CyclotomicField.isCyclotomicExtension p F
  let e := IsCyclotomicExtension.algEquiv {p} F (CyclotomicField p F) T
  exact ⟨(T.val.comp e.toAlgHom).restrictScalars ℚ⟩

/-- Degree and class-number bounds for adjoining a prime root of unity to the
host. This is the field-size input to the relaxed torsion-rank argument. -/
theorem cyclotomicField_prime_degree_log_classNumber_le (F : Type*) [Field F] [NumberField F]
    (p f : ℕ) [Fact p.Prime] [NeZero f] (j : F →ₐ[ℚ] CyclotomicField f ℚ) :
    letI := CyclotomicField.isCyclotomicExtension p F
    letI := IsCyclotomicExtension.numberField {p} F (CyclotomicField p F)
    Module.finrank ℚ (CyclotomicField p F) ≤ p * Module.finrank ℚ F ∧
      Real.log (classNumber (CyclotomicField p F) : ℝ) ≤
        2 * Module.finrank ℚ (CyclotomicField p F) * Real.log ((p : ℝ) * f) := by
  let E := CyclotomicField p F
  let _ : IsCyclotomicExtension {p} F E := CyclotomicField.isCyclotomicExtension p F
  let _ : NumberField E := IsCyclotomicExtension.numberField {p} F E
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨j'⟩ := nonempty_algHom_cyclotomicField_mul_of_algHom F p f j
  have hpf : 2 ≤ p * f := (Fact.out : p.Prime).two_le.trans
    (Nat.le_mul_of_pos_right p (NeZero.pos f))
  constructor
  · rw [← Module.finrank_mul_finrank ℚ F E, mul_comm p]
    exact Nat.mul_le_mul_left _ ((finrank_cyclotomicField_le_totient F p).trans (Nat.totient_le p))
  · simpa only [Nat.cast_mul] using log_classNumber_le_of_cyclotomic_embedding E (p * f) hpf j'

end Utilities
