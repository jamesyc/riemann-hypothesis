module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

@[expose] public section

open scoped BigOperators

namespace Utilities

/-- A finite Galois-stable family of nonzero algebraic integers has a
nonzero integer product. The index permutations allow repeated values. -/
theorem exists_int_of_galoisIntegralProduct
    {L ι : Type*} [Field L] [CharZero L] [Algebra ℚ L]
    [IsGalois ℚ L] [FiniteDimensional ℚ L] [Fintype ι]
    (f : ι → L) (hint : ∀ i, IsIntegral ℤ (f i)) (hne : ∀ i, f i ≠ 0)
    (hperm : ∀ σ : L ≃ₐ[ℚ] L, ∃ e : Equiv.Perm ι, ∀ i, σ (f i) = f (e i)) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : L) = ∏ i, f i := by
  let x := ∏ i, f i
  have hfix : ∀ σ : L ≃ₐ[ℚ] L, σ x = x := by
    intro σ
    obtain ⟨e, he⟩ := hperm σ
    dsimp [x]
    rw [map_prod]
    calc
      _ = ∏ i, f (e i) := Finset.prod_congr rfl (fun i _ => he i)
      _ = _ := Equiv.prod_comp e f
  obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).2 hfix
  have hxint : IsIntegral ℤ x := IsIntegral.prod f (fun i _ => hint i)
  have hrint : IsIntegral ℤ r := isIntegral_algebraMap_iff.mp (hr ▸ hxint)
  let : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hrint
  have hnx : (n : L) = x := by
    rw [← hr, ← hn]
    simp
  refine ⟨n, ?_, hnx⟩
  intro h
  subst n
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)) (by simpa [x] using hnx.symm)

end Utilities
