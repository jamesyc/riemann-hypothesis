module

public import Mathlib.NumberTheory.LSeries.WeakPNT

@[expose] public section

open Filter

namespace Utilities

/-- Two consecutive short intervals give distinct primes in `(x, 2x]` for
all sufficiently large real `x`. -/
theorem eventually_exists_two_primes_Ioc_double :
    ∀ᶠ x : ℝ in atTop, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧
      (p : ℝ) ∈ Set.Ioc x (2 * x) ∧ (q : ℝ) ∈ Set.Ioc x (2 * x) := by
  have hprime := Nat.eventually_exists_prime_mem_Ioc (ε := 1 / 3) (by norm_num)
  have hshift := (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 + 1 / 3)).eventually hprime
  filter_upwards [hprime, hshift, eventually_ge_atTop (0 : ℝ)] with x hp hq hx
  obtain ⟨p, hpp, hpl, hpu⟩ := hp
  obtain ⟨q, hqp, hql, hqu⟩ := hq
  have hpq : (p : ℝ) < (q : ℝ) := hpu.trans_lt hql
  refine ⟨p, q, hpp, hqp, by exact_mod_cast hpq, ⟨hpl, ?_⟩, ⟨hpl.trans hpq, ?_⟩⟩
  · linarith
  · have hu : (q : ℝ) ≤ (1 + 1 / 3) * ((1 + 1 / 3) * x) := by
      simpa only [id_eq] using hqu
    exact hu.trans (by linarith)

end Utilities
