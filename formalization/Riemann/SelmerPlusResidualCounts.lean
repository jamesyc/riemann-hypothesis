module

public import Riemann.SelmerPlusCharacterCounts
public import Riemann.SelmerPlusAssembly

@[expose] public section

open Utilities
open scoped BigOperators

namespace Riemann

/-- The two nontrivial residual cases in §17.3. The order is prime to
the residue prime, so the prime-to-residue part in case (II) is the
whole character. -/
def HasSelmerPlusNontrivialResidualCount (evenOrder : Bool) : Prop :=
  ∀ target : BundledDirichletCharacter, target.character.IsPrimitive →
    ∃ (bad : Finset ℕ) (A : ℕ) (P : ℝ), 0 < P ∧
      (∀ ℓ ∈ bad, ℓ.Prime ∧ ℓ ≠ 2) ∧
      ∀ (e t : ℕ) (q d : ℕ+), 2 ≤ e → 2 ≤ t → SelmerEstimatePrimePair target q d →
        max P (2 * (t : ℝ) + 1) < (q : ℕ) → max P (2 * (t : ℝ) + 1) < (d : ℕ) →
        let E := selmerHostField target e q d
        letI : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
        ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → ℓ ∉ bad → ¬ ℓ ∣ Module.finrank ℚ E →
          ℓ.Coprime (selmerHostModulus target e q d) →
          ∀ i ∈ Finset.Ico 1 t, 2 ≤ i → ℓ - 1 ∣ 2 * i →
            ∀ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O]
              [HasEnoughRootsOfUnity O (Monoid.exponent (E ≃ₐ[ℚ] E))],
              ∀ ψ ∈ selmerHostSignCharacters target e q d ℓ i O true, ψ ≠ 1 → ¬ ℓ ∣ orderOf ψ →
                (if evenOrder then Even (orderOf ψ) else Odd (orderOf ψ) ∧ Even i) →
                let n := selmerHostRationalCharacterLength target e q d ℓ i O ψ
                let r := Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O))
                n ≠ ⊤ ∧ ((n.toNat : ℝ) / r.toNat) ≤
                  ((ℓ : ℝ) * (selmerHostModulus target e q d : ℝ) * i) ^ A

/-- The trivial character in the residual range, case (Z) of §17.3. -/
theorem selmerPlus_residual_trivial_length
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))
    [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O]
    (hℓ : 5 ≤ ℓ) (hi : 2 ≤ i) (heven : Even i) (hdiv : ℓ - 1 ∣ 2 * i) :
    selmerHostRationalCharacterLength target e q d ℓ i O 1 = 0 := by
  sorry

/-- Case (II) of §17.3 at the residual primes outside the fixed exceptional set. -/
theorem selmerPlus_residual_evenOrder_count : HasSelmerPlusNontrivialResidualCount true := by
  sorry

/-- Case (III) of §17.3 for a nontrivial odd-order host character. -/
theorem selmerPlus_residual_oddOrder_count : HasSelmerPlusNontrivialResidualCount false := by
  sorry

private theorem selmerPlus_residual_modulusBudget {ℓ i N t A : ℕ} (hN : 0 < N)
    (ht : 2 ≤ t) (hℓ : ℓ ≤ 2 * t) (hi : i ≤ t) :
    ((ℓ : ℝ) * (N : ℝ) * i) ^ A ≤ ((N : ℝ) * t) ^ (3 * A) := by
  let M : ℝ := (N : ℝ) * t
  have ht' : (t : ℝ) ≤ M := by
    change (t : ℝ) ≤ (N : ℝ) * t
    exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hN)
  have hM : 2 ≤ M := (by exact_mod_cast ht : (2 : ℝ) ≤ t).trans ht'
  have hp : ((ℓ : ℝ) * N * i) ≤ M ^ (3 : ℕ) := by
    calc
      _ ≤ (2 * (t : ℝ)) * N * t := by
        gcongr; exact_mod_cast ‹_›
      _ = 2 * M * t := by dsimp only [M]; ring
      _ ≤ M * M * M := by gcongr
      _ = _ := by ring
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) hp _

/-- The three residual counts give the host's plus length bound on the
small good primes, with a single exceptional set and a conductor budget. -/
theorem selmerPlus_residualPrime_counts
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive) :
    ∃ (bad : Finset ℕ) (B : ℕ) (P : ℝ), 0 < P ∧
      (∀ ℓ ∈ bad, ℓ.Prime ∧ ℓ ≠ 2) ∧
      ∀ (e t : ℕ) (q d : ℕ+), 2 ≤ e → 2 ≤ t → SelmerEstimatePrimePair target q d →
        max P (2 * (t : ℝ) + 1) < (q : ℕ) → max P (2 * (t : ℝ) + 1) < (d : ℕ) →
        let F := selmerHostField target e q d
        let M := (selmerHostConductor target e q d : ℝ) * t
        let L := numberFieldSelmerSignLengths true F
        (∀ i ∈ Finset.Ico 1 t, ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∉ bad →
          ℓ - 1 ∣ 2 * i → L ℓ i ≠ ⊤ ∧ (((L ℓ i).untopD 0 : ℕ) : ℝ) ≤ M ^ B) := by
  classical
  obtain ⟨bad₁, A₁, P₁, hP₁, hbad₁, hcount₁⟩ := selmerPlus_residual_evenOrder_count target hprim
  obtain ⟨bad₂, A₂, P₂, _, hbad₂, hcount₂⟩ := selmerPlus_residual_oddOrder_count target hprim
  let A := max A₁ A₂
  let m := (target.modulus : ℕ) * orderOf target.character
  let bad₀ := insert 3 (m.primeFactors.filter (· ≠ 2))
  let P := max (max P₁ P₂) ((target.modulus : ℕ) : ℝ)
  refine ⟨(bad₁ ∪ bad₂) ∪ bad₀, 9 * A + 1, P,
    hP₁.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_, ?_⟩
  · intro ℓ hℓ
    rcases Finset.mem_union.mp hℓ with h | h
    · exact (Finset.mem_union.mp h).elim (hbad₁ ℓ) (hbad₂ ℓ)
    · rcases Finset.mem_insert.mp h with rfl | h
      · decide
      · exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2⟩
  intro e t q d he ht hpair hq hd
  dsimp only
  intro i hi ℓ hℓ hodd hgood hdiv
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let E := selmerHostField target e q d
  let : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
  let N := selmerHostModulus target e q d
  let f := selmerHostConductor target e q d
  let M := (f : ℝ) * t
  have hgood₁ : ℓ ∉ bad₁ := fun h => hgood (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hgood₂ : ℓ ∉ bad₂ := fun h => hgood (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hgood₀ : ℓ ∉ bad₀ := fun h => hgood (Finset.mem_union_right _ h)
  have hm : m ≠ 0 := mul_ne_zero target.modulus.pos.ne' (orderOf_pos target.character).ne'
  have hnodvd : ¬ ℓ ∣ m := fun h =>
    hgood₀ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hℓ.mem_primeFactors h hm, hodd⟩))
  have htarget : ¬ ℓ ∣ (target.modulus : ℕ) := fun h => hnodvd (dvd_mul_of_dvd_left h _)
  have horder : ¬ ℓ ∣ orderOf target.character := fun h => hnodvd (dvd_mul_of_dvd_right h _)
  have hdegree : ¬ ℓ ∣ Module.finrank ℚ E := fun h =>
    horder (odd_prime_dvd_order_of_dvd_selmerHostDegree target e q d hpair hℓ hodd h)
  have hℓ₅ : 5 ≤ ℓ := by
    have h3 : ℓ ≠ 3 := fun h => hgood₀ (h ▸ Finset.mem_insert_self _ _)
    have h4 : ℓ ≠ 4 := fun h => by rw [h] at hℓ; exact (by decide : ¬ Nat.Prime 4) hℓ
    have := hℓ.two_le
    omega
  have hi₂ : 2 ≤ i := by
    have h := Nat.le_of_dvd (show 0 < 2 * i from by have := (Finset.mem_Ico.mp hi).1; omega) hdiv
    omega
  have hqRange : 2 * t < (q : ℕ) := by
    have h : 2 * (t : ℝ) < ((q : ℕ) : ℝ) := by linarith [lt_of_le_of_lt (le_max_right P _) hq]
    exact_mod_cast h
  have hdRange : 2 * t < (d : ℕ) := by
    have h : 2 * (t : ℝ) < ((d : ℕ) : ℝ) := by linarith [lt_of_le_of_lt (le_max_right P _) hd]
    exact_mod_cast h
  have hsmall := selmerPlus_residuePrime_le hℓ hi hdiv
  have hcop : ℓ.Coprime N :=
    selmerHostModulus_coprime_residuePrime target e q d hpair hℓ hodd htarget hsmall hqRange hdRange
  have hP₁P : P₁ ≤ P := (le_max_left _ _).trans (le_max_left _ _)
  have hP₂P : P₂ ≤ P := (le_max_right _ _).trans (le_max_left _ _)
  have hqN : (target.modulus : ℕ) ≤ (q : ℕ) := by
    have h : ((target.modulus : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans (le_of_lt hq)
    exact_mod_cast h
  have hN := selmerHostModulus_pos target e q d
  have hpoly :
      ((ℓ : ℝ) * N * i) ^ A ≤ M ^ (9 * A) := by
    exact (selmerPlus_residual_modulusBudget (A := A) hN ht hsmall (Finset.mem_Ico.mp hi).2.le).trans
      (by simpa only [M, ← mul_assoc, show 3 * 3 = (9 : ℕ) by decide] using
        selmerHostModulus_cutoff_pow_le_conductor target e q d hpair hqN (by omega : 0 < t) (3 * A))
  have hbase : 1 ≤ (ℓ : ℝ) * N * i := by
    exact_mod_cast (show 1 ≤ ℓ * N * i from Nat.succ_le_of_lt (by positivity [hℓ.pos, hN, hi₂]))
  have hM₀ : 0 ≤ M := by dsimp only [M]; positivity
  have hR : SelmerPlusRationalPrimeBound target e q d ℓ hℓ i (M ^ (9 * A + 1)) := by
    intro O _ _ _ T n r
    have hpoint (ψ : Gal(E/ℚ) →* Oˣ) (hψ : ψ ∈ T) :
        n ψ ≠ ⊤ ∧ ((n ψ).toNat : ℝ) / r.toNat ≤ M ^ (9 * A) := by
      by_cases hψ₁ : ψ = 1
      · subst ψ
        have heven := even_of_selmerHostPlusCharacter_odd_order target e q d ℓ i O 1 hψ
          (by rw [orderOf_one]; decide)
        have hzero := selmerPlus_residual_trivial_length target e q d ℓ i O hℓ₅ hi₂ heven hdiv
        have heq : n 1 = 0 := hzero
        rw [heq]
        exact ⟨by simp, by simpa only [ENat.toNat_zero, Nat.cast_zero, zero_div] using
          (pow_nonneg hM₀ (9 * A))⟩
      · have hψorder : ¬ ℓ ∣ orderOf ψ := fun h =>
          hdegree (h.trans (orderOf_selmerHostGaloisCharacter_dvd_degree target e q d ℓ O ψ))
        rcases Nat.even_or_odd (orderOf ψ) with hEven | hOdd
        · obtain ⟨hf, hb⟩ := hcount₁ e t q d he ht hpair
            ((max_le_max_right _ hP₁P).trans_lt hq) ((max_le_max_right _ hP₁P).trans_lt hd)
            ℓ hℓ₅ hgood₁ hdegree hcop i hi hi₂ hdiv O ψ hψ hψ₁ hψorder hEven
          exact ⟨hf, hb.trans ((pow_le_pow_right₀ hbase (le_max_left _ _)).trans hpoly)⟩
        · have heven := even_of_selmerHostPlusCharacter_odd_order target e q d ℓ i O ψ hψ hOdd
          obtain ⟨hf, hb⟩ := hcount₂ e t q d he ht hpair
            ((max_le_max_right _ hP₂P).trans_lt hq) ((max_le_max_right _ hP₂P).trans_lt hd)
            ℓ hℓ₅ hgood₂ hdegree hcop i hi hi₂ hdiv O ψ hψ hψ₁ hψorder ⟨hOdd, heven⟩
          exact ⟨hf, hb.trans ((pow_le_pow_right₀ hbase (le_max_right _ _)).trans hpoly)⟩
    refine ⟨fun ψ hψ => (hpoint ψ hψ).1, ?_⟩
    have hcard : (T.card : ℝ) ≤ f := by
      exact_mod_cast (selmerHostSignCharacters_card_le_degree target e q d ℓ i O true).trans
        (selmerHostDegree_le_conductor target e q d)
    calc
      _ ≤ ∑ _ψ ∈ T, M ^ (9 * A) := Finset.sum_le_sum fun ψ hψ => (hpoint ψ hψ).2
      _ = (T.card : ℝ) * M ^ (9 * A) := by simp
      _ ≤ M * M ^ (9 * A) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hcard.trans (le_mul_of_one_le_right (by positivity) (by exact_mod_cast (show 1 ≤ t by omega)))
      _ = _ := by rw [mul_comm, pow_succ]
  exact selmerPlus_hostLength_le_of_rationalPrimeBound target e q d ℓ hℓ i _ hodd hdegree hR

end Riemann
