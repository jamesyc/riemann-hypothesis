module

public import Utilities.PadicTateCoefficientLength
public import Utilities.KummerRadicalGenerator
import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section

open scoped TensorProduct

namespace Utilities

/-- A nonempty finite set in a cyclic module over a DVR has an element
whose span contains the whole set. -/
theorem exists_smul_generator_of_finite_range_subset_cyclic
    {R W X : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup W] [Module R W] [Nonempty X]
    (f : X → W) (hfin : (Set.range f).Finite)
    (w : W) (hspan : ∀ x : X, ∃ a : R, f x = a • w) :
    ∃ x : X, ∀ y : X, ∃ a : R, f y = a • f x := by
  let V (x : W) := Submodule.span R ({x} : Set W)
  have hmem (x y : W) : V x ≤ V y ↔ ∃ a : R, x = a • y := by
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact exists_congr fun _ => eq_comm
  have htotal (x y : X) : V (f x) ≤ V (f y) ∨ V (f y) ≤ V (f x) := by
    obtain ⟨a, ha⟩ := hspan x
    obtain ⟨b, hb⟩ := hspan y
    rcases le_total (IsDiscreteValuationRing.addVal R a) (IsDiscreteValuationRing.addVal R b) with h | h
    · obtain ⟨d, hd⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp h
      exact Or.inr ((hmem _ _).mpr ⟨d, by rw [hb, hd, mul_comm, mul_smul, ← ha]⟩)
    · obtain ⟨d, hd⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp h
      exact Or.inl ((hmem _ _).mpr ⟨d, by rw [ha, hd, mul_comm, mul_smul, ← hb]⟩)
  obtain ⟨_, ⟨x, rfl⟩, hmax⟩ := hfin.exists_maximalFor V _ (Set.range_nonempty f)
  refine ⟨x, fun y => (hmem _ _).mp ?_⟩
  exact (htotal y x).elim id (hmax (Set.mem_range_self y))

/-- A finite set of values in the prime-power Tate torsion has a value
generating the span of the set. -/
theorem exists_extendedPadicTate_range_generator (p : ℕ) [Fact p.Prime] (S : Type)
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra ℤ_[p] S]
    [Module.Flat ℤ_[p] S] (r : ℕ) {X : Type*} [Nonempty X]
    (f : X → S ⊗[ℤ_[p]] PadicTateQuotient p) (hfin : (Set.range f).Finite)
    (htors : ∀ x, (p : S) ^ r • f x = 0) :
    ∃ x : X, ∀ y : X, ∃ a : S, f y = a • f x := by
  have hp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨w, -, hw⟩ := exists_extendedPadicTate_torsion_generator p S ((p : ℤ_[p]) ^ r) (pow_ne_zero r hp)
  rw [map_pow, map_natCast] at hw
  exact exists_smul_generator_of_finite_range_subset_cyclic f hfin w
    (fun x => (hw (f x) (htors x)).imp fun _ h => h.symm)

/-- A nonzero bounded Tate character with finite image and scalar action
different from the cyclotomic action has a generating value on the radical
stabilizer. -/
theorem exists_extendedPadicTate_generator_on_radical_stabilizer
    {K E L : Type*} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] [Normal K E]
    (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Algebra ℤ_[p] S] [Module.Flat ℤ_[p] S]
    (r k : ℕ) (f : Additive Gal(L/E) →+ (S ⊗[ℤ_[p]] PadicTateQuotient p))
    (hfin : (Set.range f).Finite) (htors : ∀ u, (p : S) ^ r • f u = 0) (hne : f ≠ 0)
    {β : L} (hβ : β ≠ 0)
    (hbase : ∀ s : Gal(L/K), s (β ^ (p ^ r)) = β ^ (p ^ r))
    (hroots : ∀ (u : Gal(L/E)) (x : L), x ^ (p ^ r) = 1 → u x = x)
    (s : Gal(L/K)) (hs : ∀ x : L, x ^ (p ^ r) = 1 → s x = x ^ k)
    {α ε : S} (hsep : IsUnit (α - ε))
    (hconj : ∀ u : Gal(L/E), f (Additive.ofMul (relativeGaloisConj K E L s u)) = α • f (Additive.ofMul u))
    (hscalar : ∀ u : Gal(L/E), k • f (Additive.ofMul u) = ε • f (Additive.ofMul u)) :
    ∃ u : Gal(L/E), u β = β ∧ ∀ v : Gal(L/E), ∃ b : S, f (Additive.ofMul v) = b • f (Additive.ofMul u) := by
  obtain ⟨w, hw⟩ := exists_extendedPadicTate_range_generator p S r f hfin htors
  have hw₀ : f w ≠ 0 := by
    intro h
    apply hne
    apply AddMonoidHom.ext
    intro v
    obtain ⟨b, hb⟩ := hw v
    change f v = 0
    rw [hb, h, smul_zero]
  exact exists_generator_on_radical_stabilizer_of_smul_conjugation f (f w) hw₀
    ⟨w.toMul, rfl⟩ (fun u => hw (Additive.ofMul u)) hβ hbase hroots s hs hsep hconj hscalar

end Utilities
