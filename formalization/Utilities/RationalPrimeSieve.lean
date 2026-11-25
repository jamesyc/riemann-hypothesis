module

public import Utilities.RationalPrime
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors

namespace Utilities

variable (E : Type*) [Field E] [NumberField E]

/-- The rational prime below a nonzero prime of the ring of integers. -/
noncomputable def rationalPrimeBelow (v : HeightOneSpectrum (𝓞 E)) : Nat.Primes := by
  let _ : v.asIdeal.IsPrime := v.isPrime
  let _ : NeZero v.asIdeal := ⟨v.ne_bot⟩
  exact ⟨Ideal.absNorm (v.asIdeal.under ℤ), Nat.absNorm_under_prime v.asIdeal⟩

private theorem card_primesOver_rationalPrime_le (q : Nat.Primes) :
    Nat.card ((Ideal.span ({(q.val : ℤ)} : Set ℤ)).primesOver (𝓞 E)) ≤ Module.finrank ℤ (𝓞 E) := by
  classical
  let _ : Fact q.val.Prime := ⟨q.property⟩
  let P := Ideal.span ({(q.val : ℤ)} : Set ℤ)
  let _ : P.IsMaximal := rationalPrime_isMaximal q.val
  let _ : P.IsPrime := (rationalPrime_isMaximal q.val).isPrime
  let _ : Finite (P.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite (B := 𝓞 E) P).to_subtype
  let _ : Fintype (P.primesOver (𝓞 E)) := Fintype.ofFinite _
  change Nat.card (P.primesOver (𝓞 E)) ≤ _
  rw [Nat.card_eq_fintype_card, ← Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)]
  calc
    _ = ∑ _ : P.primesOver (𝓞 E), (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun Q _ => by
      let _ : Q.val.IsPrime := Q.property.1
      exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
        (Ideal.ramificationIdx_pos ℤ Q.val).ne' (Ideal.inertiaDeg_pos Q.val ℤ).ne')

/-- A rational-prime sieve has summable omitted inverse norms when the
omitted primes away from its modulus have norm at least the square
of the rational prime below them. -/
theorem summable_inverse_norm_of_rational_square (N : ℕ) [NeZero N]
    (S : Set (HeightOneSpectrum (𝓞 E)))
    (hlower : ∀ v : S, ¬ (rationalPrimeBelow E v.val).val ∣ N →
      (rationalPrimeBelow E v.val).val ^ 2 ≤ Ideal.absNorm v.val.asIdeal) :
    Summable (fun v : S => (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹) := by
  classical
  let fiber (q : Nat.Primes) : Set S := {v | rationalPrimeBelow E v.val = q}
  let f (v : S) : ℝ := (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹
  have hf : 0 ≤ f := fun _ => inv_nonneg.mpr (by positivity)
  have hpart (v : S) : ∃! q, v ∈ fiber q := ⟨rationalPrimeBelow E v.val, rfl, fun _ h => h.symm⟩
  let above (q : Nat.Primes) (v : fiber q) : (Ideal.span ({(q.val : ℤ)} : Set ℤ)).primesOver (𝓞 E) :=
    ⟨v.val.val.asIdeal, v.val.val.isPrime, ⟨by
      have hv : Ideal.absNorm (v.val.val.asIdeal.under ℤ) = q.val := congrArg Subtype.val v.property
      rw [← hv, Int.ideal_span_absNorm_eq_self]⟩⟩
  have habove (q : Nat.Primes) : Function.Injective (above q) :=
    fun _ _ h => Subtype.ext (Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)))
  let _ (q : Nat.Primes) : Finite ((Ideal.span ({(q.val : ℤ)} : Set ℤ)).primesOver (𝓞 E)) := by
    let _ : Fact q.val.Prime := ⟨q.property⟩
    exact (IsDedekindDomain.primesOver_finite (B := 𝓞 E) (Ideal.span ({(q.val : ℤ)} : Set ℤ))).to_subtype
  let _ (q : Nat.Primes) : Finite (fiber q) := Finite.of_injective (above q) (habove q)
  have hcard (q : Nat.Primes) : Nat.card (fiber q) ≤ Module.finrank ℤ (𝓞 E) :=
    (Nat.card_le_card_of_injective (above q) (habove q)).trans (card_primesOver_rationalPrime_le E q)
  let g (q : Nat.Primes) : ℝ := (if q.val ≤ N then 1 else 0) + ((q.val : ℝ) ^ 2)⁻¹
  have hg : Summable g := by
    have hind : Summable (fun n : ℕ => if n ≤ N then (1 : ℝ) else 0) := by
      refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
      rw [ite_eq_right (fun h => hn (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h)))]
    exact (hind.comp_injective Subtype.val_injective).add
      (((Real.summable_nat_pow_inv (p := 2)).mpr (by decide)).comp_injective Subtype.val_injective)
  have hle (q : Nat.Primes) (v : fiber q) : f v.val ≤ g q := by
    by_cases hq : q.val ∣ N
    · have hp : (1 : ℕ) ≤ Ideal.absNorm v.val.val.asIdeal :=
        Ideal.absNorm_pos_of_nonZeroDivisors
          ⟨v.val.val.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.val.val.ne_bot⟩
      have hn : 1 ≤ (Ideal.absNorm v.val.val.asIdeal : ℝ) := by exact_mod_cast hp
      have hqN : q.val ≤ N := Nat.le_of_dvd (NeZero.pos N) hq
      have h1 : f v.val ≤ 1 := inv_le_one_of_one_le₀ hn
      exact h1.trans (by simp [g, hqN])
    · have hv : ¬(rationalPrimeBelow E v.val.val).val ∣ N := by rw [v.property]; exact hq
      have h := hlower v.val hv
      rw [v.property] at h
      have hsq : 0 < (q.val : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr q.property.pos) _
      have hnorm : 0 < (Ideal.absNorm v.val.val.asIdeal : ℝ) :=
        Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors
          ⟨v.val.val.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.val.val.ne_bot⟩)
      exact ((inv_le_inv₀ hnorm hsq).mpr (by exact_mod_cast h)).trans
        (le_add_of_nonneg_left (by split_ifs <;> positivity))
  apply (summable_partition hf (s := fiber) hpart).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  refine Summable.of_nonneg_of_le (fun q => tsum_nonneg fun _ => hf _) ?_
    (hg.mul_left (Module.finrank ℤ (𝓞 E) : ℝ))
  intro q
  have hs : (∑' v : fiber q, f v.val) ≤ (Nat.card (fiber q) : ℝ) * g q := by
    let _ : Fintype (fiber q) := Fintype.ofFinite _
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _ : fiber q, g q := Finset.sum_le_sum fun v _ => hle q v
      _ = _ := by simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
  exact hs.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard q)) (by
    unfold g
    split_ifs <;> positivity))

/-- The degree-one primes outside a rational modulus omit a summable
family of inverse norms. -/
theorem summable_inverse_norm_not_degreeOne_or_dvd (N : ℕ) [NeZero N] :
    Summable (fun v : {v : HeightOneSpectrum (𝓞 E) |
      (rationalPrimeBelow E v).val ∣ N ∨ v.asIdeal.inertiaDeg ℤ ≠ 1} =>
      (Ideal.absNorm v.val.asIdeal : ℝ)⁻¹) := by
  apply summable_inverse_norm_of_rational_square E N
  intro v hv
  let _ : v.val.asIdeal.IsPrime := v.val.isPrime
  have hd : 2 ≤ v.val.asIdeal.inertiaDeg ℤ := by
    have hpos := Ideal.inertiaDeg_pos v.val.asIdeal ℤ
    have hne := v.property.resolve_left hv
    omega
  have he : (rationalPrimeBelow E v.val).val ^ v.val.asIdeal.inertiaDeg ℤ =
      Ideal.absNorm v.val.asIdeal := Ideal.absNorm_pow_inertiaDeg (v.val.asIdeal.under ℤ) v.val.asIdeal
  rw [← he]
  exact Nat.pow_le_pow_right (rationalPrimeBelow E v.val).property.pos hd

end Utilities
