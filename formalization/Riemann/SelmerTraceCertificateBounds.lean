module

public import Utilities.PadicProductBound

@[expose] public section

open scoped BigOperators Classical

namespace Riemann

/-- Combine the per-character OneChar inequalities with the common integer
certificate of Proposition 17.21. The fibers distinguish character
indices even when their Eisenstein traces coincide. -/
theorem selmerTraceFiber_lengths_le_factorization
    {p : ℕ} [Fact p.Prime] {L I χ : Type*} [Field L] [Fintype I]
    (emb : L →+* PadicAlgCl p) (f : I → L) (owner : I → χ)
    (n : ℤ) (hn : n ≠ 0) (hprod : (n : L) = ∏ i, f i)
    (chars : Finset χ) (selected : Finset I) (howner : ∀ i ∈ selected, owner i ∈ chars)
    (hint : ∀ i, IsIntegral ℤ (f i))
    (lengths : χ → WithTop ℕ) (ramification : ℕ)
    (hOneChar : ∀ ψ ∈ chars, lengths ψ ≠ ⊤ ∧
      (((lengths ψ).untopD 0 : ℕ) : ℝ) / ramification ≤
        2 * ∑ i ∈ selected.filter (fun i => owner i = ψ),
          -Real.logb (p : ℝ) ‖emb (f i)‖) :
    (∀ ψ ∈ chars, lengths ψ ≠ ⊤) ∧
      (∑ ψ ∈ chars, (((lengths ψ).untopD 0 : ℕ) : ℝ) / ramification) ≤
        2 * n.natAbs.factorization p := by
  refine ⟨fun ψ hψ => (hOneChar ψ hψ).1, ?_⟩
  have hN : ∏ i, emb (f i) = (n : PadicAlgCl p) := by
    simpa only [map_intCast, map_prod] using (congrArg emb hprod).symm
  have hval := Utilities.sum_neg_logb_norm_le_factorization_of_prod
    (fun i => emb (f i)) n hn hN selected
    (fun i _ => Utilities.norm_le_one_of_isIntegral_int ((hint i).map emb.toIntAlgHom))
  calc
    _ ≤ ∑ ψ ∈ chars, (2 * ∑ i ∈ selected.filter (fun i => owner i = ψ),
        -Real.logb (p : ℝ) ‖emb (f i)‖) :=
      Finset.sum_le_sum fun ψ hψ => (hOneChar ψ hψ).2
    _ = 2 * ∑ i ∈ selected, -Real.logb (p : ℝ) ‖emb (f i)‖ := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to howner]
    _ ≤ _ := mul_le_mul_of_nonneg_left hval (by norm_num)

end Riemann
