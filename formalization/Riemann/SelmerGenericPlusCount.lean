module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Utilities.CharacterKernelCount
import Utilities.PrimeLogSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient

@[expose] public section

open scoped BigOperators Classical

namespace Riemann

/-- The summation by kernels in Proposition 17.14. The arithmetic input is
a (CorGK) bound on each kernel fiber, at the specified twist. The character
coefficient rings and their ramification indices can vary with the prime. -/
theorem genericPlusCount_of_kernelBounds {N : ℕ} [NeZero N] (primes : Finset ℕ)
    (O : ℕ → Type*) [∀ ℓ, CommRing (O ℓ)] [∀ ℓ, IsDomain (O ℓ)]
    (chars : ∀ ℓ, Finset (DirichletCharacter (O ℓ) N))
    (lengths : ∀ ℓ, DirichletCharacter (O ℓ) N → WithTop ℕ)
    (ramification : ℕ → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hcount : ∀ H : Subgroup (ZMod N)ˣ, IsCyclic ((ZMod N)ˣ ⧸ H) →
      let P := primes.filter fun ℓ => ∃ ψ ∈ chars ℓ, ψ.toUnitHom.ker = H
      (∀ ℓ ∈ P, ∀ ψ ∈ chars ℓ, ψ.toUnitHom.ker = H → lengths ℓ ψ ≠ ⊤) ∧
      (∑ ℓ ∈ P, Real.log ℓ * ∑ ψ ∈ (chars ℓ).filter (fun ψ => ψ.toUnitHom.ker = H),
        (((lengths ℓ ψ).untopD 0 : ℕ) : ℝ) / ramification ℓ) ≤ B * H.index.totient) :
    (∀ ℓ ∈ primes, ∀ ψ ∈ chars ℓ, lengths ℓ ψ ≠ ⊤) ∧
      (∑ ℓ ∈ primes, Real.log ℓ * ∑ ψ ∈ chars ℓ,
        (((lengths ℓ ψ).untopD 0 : ℕ) : ℝ) / ramification ℓ) ≤ B * N := by
  classical
  let T : Finset (Subgroup (ZMod N)ˣ) :=
    primes.biUnion fun ℓ => (chars ℓ).image fun ψ => ψ.toUnitHom.ker
  have hmem {ℓ : ℕ} {ψ : DirichletCharacter (O ℓ) N} (hℓ : ℓ ∈ primes)
      (hψ : ψ ∈ chars ℓ) : ψ.toUnitHom.ker ∈ T :=
    Finset.mem_biUnion.mpr ⟨ℓ, hℓ, Finset.mem_image_of_mem _ hψ⟩
  have hcyclic : ∀ H ∈ T, IsCyclic ((ZMod N)ˣ ⧸ H) := by
    intro H hH
    obtain ⟨ℓ, -, h⟩ := Finset.mem_biUnion.mp hH
    obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.mp h
    exact Utilities.isCyclic_quotient_ker_character ψ.toUnitHom
  constructor
  · intro ℓ hℓ ψ hψ
    have hcase := hcount _ (hcyclic _ (hmem hℓ hψ))
    exact hcase.1 ℓ (Finset.mem_filter.mpr ⟨hℓ, ψ, hψ, rfl⟩) ψ hψ rfl
  have htot : (∑ H ∈ T, H.index.totient : ℕ) ≤ N := by
    refine (Utilities.sum_totient_index_le_card T hcyclic).trans ?_
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_le _
  let cost (ℓ : ℕ) (ψ : DirichletCharacter (O ℓ) N) :=
    (((lengths ℓ ψ).untopD 0 : ℕ) : ℝ) / ramification ℓ
  calc
    _ = ∑ ℓ ∈ primes, ∑ H ∈ T, Real.log ℓ *
        ∑ ψ ∈ (chars ℓ).filter (fun ψ => ψ.toUnitHom.ker = H), cost ℓ ψ := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      rw [← Finset.mul_sum]
      congr 1
      exact (Finset.sum_fiberwise_of_maps_to (fun ψ hψ => hmem hℓ hψ) (cost ℓ)).symm
    _ = ∑ H ∈ T, ∑ ℓ ∈ primes.filter (fun ℓ => ∃ ψ ∈ chars ℓ, ψ.toUnitHom.ker = H),
        Real.log ℓ * ∑ ψ ∈ (chars ℓ).filter (fun ψ => ψ.toUnitHom.ker = H), cost ℓ ψ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun H _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      split_ifs with h
      · rfl
      · rw [Finset.filter_false_of_mem (fun ψ hψ hker => h ⟨ψ, hψ, hker⟩),
          Finset.sum_empty, mul_zero]
    _ ≤ ∑ H ∈ T, B * (H.index.totient : ℝ) := by
      exact Finset.sum_le_sum fun H hH => (hcount H (hcyclic H hH)).2
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast htot) hB

/-- Proposition 17.20 followed by the kernel summation in Proposition 17.14.
The two certificates need only be available for the kernels that occur and
control the normalized lengths at primes other than their own exception. -/
theorem genericPlusCount_of_certificates {N p q : ℕ} [NeZero N] (hpq : p ≠ q)
    (primes : Finset ℕ) (O : ℕ → Type*) [∀ ℓ, CommRing (O ℓ)] [∀ ℓ, IsDomain (O ℓ)]
    (chars : ∀ ℓ, Finset (DirichletCharacter (O ℓ) N))
    (lengths : ∀ ℓ, DirichletCharacter (O ℓ) N → WithTop ℕ)
    (ramification : ℕ → ℕ) (height : ℕ → ℝ)
    (hheight : 0 ≤ height p + height q)
    (hcert : ∀ r ∈ ({p, q} : Finset ℕ), ∀ H : Subgroup (ZMod N)ˣ,
      IsCyclic ((ZMod N)ˣ ⧸ H) →
      let P := primes.filter fun ℓ => ∃ ψ ∈ chars ℓ, ψ.toUnitHom.ker = H
      ∃ n : ℕ, 0 < n ∧ Real.log n ≤ height r * H.index.totient ∧
      ∀ ℓ ∈ P, ℓ ≠ r →
        (∀ ψ ∈ chars ℓ, ψ.toUnitHom.ker = H → lengths ℓ ψ ≠ ⊤) ∧
        (∑ ψ ∈ (chars ℓ).filter (fun ψ => ψ.toUnitHom.ker = H),
          (((lengths ℓ ψ).untopD 0 : ℕ) : ℝ) / ramification ℓ) ≤ 2 * n.factorization ℓ) :
    (∀ ℓ ∈ primes, ∀ ψ ∈ chars ℓ, lengths ℓ ψ ≠ ⊤) ∧
      (∑ ℓ ∈ primes, Real.log ℓ * ∑ ψ ∈ chars ℓ,
        (((lengths ℓ ψ).untopD 0 : ℕ) : ℝ) / ramification ℓ) ≤ 2 * (height p + height q) * N := by
  apply genericPlusCount_of_kernelBounds primes O chars lengths ramification (by positivity)
  intro H hH
  obtain ⟨m, _, hm, hpm⟩ := hcert p (by simp) H hH
  obtain ⟨n, _, hn, hqn⟩ := hcert q (by simp) H hH
  dsimp only
  constructor
  · intro ℓ hℓ ψ hψ hker
    by_cases h : ℓ = p
    · exact (hqn ℓ hℓ (h ▸ hpq)).1 ψ hψ hker
    · exact (hpm ℓ hℓ h).1 ψ hψ hker
  calc
    _ ≤ 2 * (Real.log m + Real.log n) :=
      Utilities.sum_log_mul_le_of_two_certificates hpq
        (fun ℓ hℓ h => (hpm ℓ hℓ h).2) (fun ℓ hℓ h => (hqn ℓ hℓ h).2)
    _ ≤ _ := by
      rw [mul_assoc, add_mul]
      linarith

/-- The last polynomial absorption in the generic count of Proposition 17.14. -/
theorem genericPlusCount_budget_le {N e t k A : ℕ} {C : ℝ}
    (hN : 16 ≤ N) (ht : e + 1 ≤ t) (hC : C ≤ 16 ^ k) :
    C * (N : ℝ) * ((N : ℝ) * (e + 1)) ^ A ≤ ((N : ℝ) * t) ^ ((k + 1 + A) : ℕ) := by
  have hN' : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have het : (e : ℝ) + 1 ≤ t := by exact_mod_cast ht
  have hC' : C ≤ (N : ℝ) ^ k := hC.trans (pow_le_pow_left₀ (by norm_num) hN' _)
  have hNt : (N : ℝ) ≤ (N : ℝ) * t :=
    le_mul_of_one_le_right (by positivity) ht'
  have hC'' : C ≤ ((N : ℝ) * t) ^ k := hC'.trans (pow_le_pow_left₀ (by positivity) hNt _)
  calc
    _ ≤ ((N : ℝ) * t) ^ k * ((N : ℝ) * t) * ((N : ℝ) * t) ^ A := by gcongr
    _ = _ := by rw [pow_add, pow_succ]

end Riemann
