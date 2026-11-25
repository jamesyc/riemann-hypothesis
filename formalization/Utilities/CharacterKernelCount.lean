module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

open scoped BigOperators Classical

namespace Utilities

/-- A finite character's quotient by its kernel is cyclic, including when
its values lie in different characteristic-zero coefficient fields. -/
theorem isCyclic_quotient_ker_character {G O : Type*} [CommGroup G] [Finite G]
    [CommRing O] [IsDomain O] (χ : G →* Oˣ) : IsCyclic (G ⧸ χ.ker) := by
  let : Finite χ.range := Finite.of_surjective _ χ.rangeRestrict_surjective
  let : IsCyclic χ.range := isCyclic_subgroup_units χ.range
  exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange χ).symm
    (QuotientGroup.quotientKerEquivRange χ).symm.surjective

private theorem ker_eq_bot_of_orderOf_card {G : Type*} [CommGroup G] [Finite G]
    (χ : G →* ℂˣ) (hχ : orderOf χ = Nat.card G) : χ.ker = ⊥ := by
  have hp : χ ^ χ.ker.index = 1 := by
    ext1 x
    have hx := Subgroup.pow_index_mem χ.ker x
    rw [MonoidHom.mem_ker, map_pow] at hx
    simpa using hx
  have hd : Nat.card G ∣ χ.ker.index := hχ ▸ orderOf_dvd_of_pow_eq_one hp
  have he : χ.ker.index = Nat.card G := Nat.dvd_antisymm (Subgroup.index_dvd_card _) hd
  have hcard := Subgroup.card_mul_index χ.ker
  rw [he] at hcard
  apply Subgroup.card_eq_one.mp
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by simpa using hcard)

private theorem totient_le_card_characters_with_ker {G : Type*} [CommGroup G] [Finite G]
    [Fintype (G →* ℂˣ)] (S : Subgroup G) (hS : IsCyclic (G ⧸ S)) :
    S.index.totient ≤ (Finset.univ.filter fun ψ : G →* ℂˣ => ψ.ker = S).card := by
  classical
  let : NeZero (Monoid.exponent (G ⧸ S)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (G ⧸ S) ℂ
  let : Finite ((G ⧸ S) →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  let : Fintype ((G ⧸ S) →* ℂˣ) := Fintype.ofFinite _
  let : IsCyclic ((G ⧸ S) →* ℂˣ) := isCyclic_of_surjective e.symm e.symm.surjective
  have hc : Fintype.card ((G ⧸ S) →* ℂˣ) = S.index := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]
    rfl
  rw [← IsCyclic.card_orderOf_eq_totient (α := (G ⧸ S) →* ℂˣ) (d := S.index) (hc ▸ dvd_rfl)]
  refine Finset.card_le_card_of_injOn (fun χ : (G ⧸ S) →* ℂˣ => χ.comp (QuotientGroup.mk' S)) ?_ ?_
  · intro χ hχ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hχ ⊢
    have hker := ker_eq_bot_of_orderOf_card χ hχ
    rw [← MonoidHom.comap_ker, hker, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  · intro a _ b _ hab
    exact QuotientGroup.monoidHom_ext _ hab

/-- Kernel classes having cyclic quotient can be counted in the complex
character group even when the original kernels occur over varying fields. -/
theorem sum_totient_index_le_card {G : Type*} [CommGroup G] [Finite G]
    (kernels : Finset (Subgroup G)) (hS : ∀ S ∈ kernels, IsCyclic (G ⧸ S)) :
    ∑ S ∈ kernels, S.index.totient ≤ Nat.card G := by
  classical
  let : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ
  let : Finite (G →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  let : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  calc
    _ ≤ ∑ S ∈ kernels, (Finset.univ.filter fun ψ : G →* ℂˣ => ψ.ker = S).card :=
      Finset.sum_le_sum fun S h => totient_le_card_characters_with_ker S (hS S h)
    _ = (Finset.univ.filter fun ψ : G →* ℂˣ => ψ.ker ∈ kernels).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ Fintype.card (G →* ℂˣ) := Finset.card_le_univ _
    _ = Nat.card G := by rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]

end Utilities
