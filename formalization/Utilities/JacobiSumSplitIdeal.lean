module

public import Utilities.JacobiSumReduction
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

open IsDedekindDomain

namespace Utilities

open scoped Classical in
/-- If a principal ideal is a product of distinct prime ideals, a divisor of
its generator has precisely the prime factors containing that divisor. -/
theorem span_singleton_eq_prod_filter_of_split
    {R ι : Type*} [CommRing R] [IsDedekindDomain R] [Fintype ι]
    (P : ι → HeightOneSpectrum R) (hinj : Function.Injective P) {x y a : R}
    (ha : a ≠ 0) (hxy : x * y = a) (hs : Ideal.span ({a} : Set R) = ∏ i, (P i).asIdeal) :
    Ideal.span ({x} : Set R) = ∏ i ∈ Finset.univ.filter (fun i => x ∈ (P i).asIdeal), (P i).asIdeal := by
  classical
  let A := ∏ i ∈ Finset.univ.filter (fun i => x ∈ (P i).asIdeal), (P i).asIdeal
  let B := ∏ i ∈ Finset.univ.filter (fun i => x ∉ (P i).asIdeal), (P i).asIdeal
  have hAB : A * B = Ideal.span ({a} : Set R) :=
    (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => x ∈ (P i).asIdeal)
      (fun i => (P i).asIdeal)).trans hs.symm
  have hpair : Pairwise (fun i j => IsCoprime (P i).asIdeal (P j).asIdeal) := by
    intro i j hij
    let _ : (P i).asIdeal.IsMaximal := (P i).isMaximal
    let _ : (P j).asIdeal.IsMaximal := (P j).isMaximal
    exact Ideal.isCoprime_of_isMaximal (fun he => hij (hinj (HeightOneSpectrum.ext he)))
  have hdivA : A ∣ Ideal.span ({x} : Set R) :=
    Finset.prod_dvd_of_coprime (hpair.set_pairwise _) (fun i hi =>
      Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Finset.mem_filter.mp hi).2)))
  have hdivB : B ∣ Ideal.span ({y} : Set R) := by
    apply Finset.prod_dvd_of_coprime (hpair.set_pairwise _)
    intro i hi
    have hx := (Finset.mem_filter.mp hi).2
    have haP : a ∈ (P i).asIdeal := by
      have hd : (P i).asIdeal ∣ Ideal.span ({a} : Set R) :=
        hs.symm ▸ Finset.dvd_prod_of_mem (fun j => (P j).asIdeal) (Finset.mem_univ i)
      exact Ideal.dvd_iff_le.mp hd (Ideal.subset_span (by simp))
    rw [← hxy] at haP
    exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (((P i).isPrime.mem_or_mem haP).resolve_left hx)))
  obtain ⟨C, hC⟩ := hdivA
  obtain ⟨D, hD⟩ := hdivB
  have hnonzero : A * B ≠ 0 := by
    rw [hAB, ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  have hprod : (A * B) * (C * D) = (A * B) * 1 := by
    calc
      _ = (A * C) * (B * D) := by ac_rfl
      _ = Ideal.span ({x * y} : Set R) := by rw [← hC, ← hD, Ideal.span_singleton_mul_span_singleton]
      _ = _ := by rw [hxy, hAB, mul_one]
  have hCD := mul_left_cancel₀ hnonzero hprod
  have hC1 : C = 1 := by
    rw [Ideal.one_eq_top]
    apply top_unique
    calc
      (⊤ : Ideal R) = C * D := by rw [hCD, Ideal.one_eq_top]
      _ ≤ C := Ideal.mul_le_left
  rw [hC, hC1, mul_one]

/-- In a completely split prime product, the Jacobi ideal picks out the
no-carry primes and the inverse Jacobi ideal picks out the carry primes. -/
theorem jacobiSum_splitIdeal_factorization
    {R ι : Type*} [CommRing R] [IsDedekindDomain R] [CharZero R] [Fintype ι]
    (p : ℕ) [Fact p.Prime] (P : ι → HeightOneSpectrum R) (hinj : Function.Injective P)
    (hs : Ideal.span ({(p : R)} : Set R) = ∏ u, (P u).asIdeal)
    (red : ι → R →+* ZMod p) (hker : ∀ u, RingHom.ker (red u) = (P u).asIdeal)
    {χ ψ : MulChar (ZMod p) R} (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    (i j : ι → ℕ) (hi : ∀ u, 0 < i u) (hip : ∀ u, i u < p - 1) (hjp : ∀ u, j u < p - 1)
    (hredχ : ∀ u x, red u (χ x) = x ^ i u) (hredψ : ∀ u x, red u (ψ x) = x ^ j u) :
    (Ideal.span ({jacobiSum χ ψ} : Set R) =
      ∏ u ∈ Finset.univ.filter (fun u => i u + j u < p - 1), (P u).asIdeal) ∧
    (Ideal.span ({jacobiSum χ⁻¹ ψ⁻¹} : Set R) =
      ∏ u ∈ Finset.univ.filter (fun u => p - 1 ≤ i u + j u), (P u).asIdeal) := by
  classical
  have hp : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hJ := jacobiSum_zmod_mul_inv_eq_prime p hχ hψ hχψ
  let A := ∏ u ∈ Finset.univ.filter (fun u => i u + j u < p - 1), (P u).asIdeal
  let B := ∏ u ∈ Finset.univ.filter (fun u => p - 1 ≤ i u + j u), (P u).asIdeal
  have hA : Ideal.span ({jacobiSum χ ψ} : Set R) = A := by
    rw [span_singleton_eq_prod_filter_of_split P hinj hp hJ hs]
    dsimp only [A]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hker u, RingHom.mem_ker]
    exact map_jacobiSum_eq_zero_iff_of_power_reductions p (red u) (hi u) (hip u) (hjp u)
      (hredχ u) (hredψ u)
  have hAB : A * B = Ideal.span ({(p : R)} : Set R) := by
    have hprod := Finset.prod_filter_mul_prod_filter_not Finset.univ (fun u => i u + j u < p - 1)
      (fun u => (P u).asIdeal)
    exact (by simpa only [A, B, not_lt] using hprod : A * B = ∏ u, (P u).asIdeal).trans hs.symm
  have hNZ : A ≠ 0 := by
    intro h0
    rw [h0, zero_mul, Ideal.zero_eq_bot, eq_comm, Ideal.span_singleton_eq_bot] at hAB
    exact hp hAB
  refine ⟨hA, mul_left_cancel₀ hNZ ?_⟩
  calc
    A * Ideal.span ({jacobiSum χ⁻¹ ψ⁻¹} : Set R) =
        Ideal.span ({jacobiSum χ ψ * jacobiSum χ⁻¹ ψ⁻¹} : Set R) := by
      rw [← hA, Ideal.span_singleton_mul_span_singleton]
    _ = A * B := by rw [hJ, hAB]

end Utilities
