module

public import Utilities.KummerRadicalEquivariance
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

namespace Utilities

variable {K E L : Type*} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] [Normal K E]
  {R W : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup W] [Module R W]

/-- A cyclic character image with scalar action different from the
cyclotomic action has a generator among the values on the radical stabilizer. -/
theorem exists_generator_on_radical_stabilizer_of_smul_conjugation
    (f : Additive Gal(L/E) →+ W) (w : W) (hw : w ≠ 0)
    (hvalue : ∃ u : Gal(L/E), f (Additive.ofMul u) = w)
    (hgen : ∀ u : Gal(L/E), ∃ b : R, f (Additive.ofMul u) = b • w)
    {n k : ℕ} {β : L} (hβ : β ≠ 0)
    (hbase : ∀ s : Gal(L/K), s (β ^ n) = β ^ n)
    (hroots : ∀ (u : Gal(L/E)) (x : L), x ^ n = 1 → u x = x)
    (s : Gal(L/K)) (hs : ∀ x : L, x ^ n = 1 → s x = x ^ k)
    {α ε : R} (hsep : IsUnit (α - ε))
    (hconj : ∀ u : Gal(L/E), f (Additive.ofMul (relativeGaloisConj K E L s u)) = α • f (Additive.ofMul u))
    (hscalar : ∀ u : Gal(L/E), k • f (Additive.ofMul u) = ε • f (Additive.ofMul u)) :
    ∃ u : Gal(L/E), u β = β ∧ ∀ v : Gal(L/E), ∃ b : R, f (Additive.ofMul v) = b • f (Additive.ofMul u) := by
  let P : Submodule R W :=
    Submodule.map (LinearMap.toSpanSingleton R W w) (IsLocalRing.maximalIdeal R)
  let q := P.mkQ
  let fbar := q.toAddMonoidHom.comp f
  have hwP : w ∉ P := by
    rintro ⟨b, hb, he⟩
    change b • w = w at he
    have hu : IsUnit (1 - b) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits b hb
    exact hw (hu.smul_eq_zero.mp (by rw [sub_smul, one_smul, he, sub_self]))
  have hbar : fbar ≠ 0 := by
    intro h
    obtain ⟨u, hu⟩ := hvalue
    have hEq : q (f (Additive.ofMul u)) = 0 := DFunLike.congr_fun h (Additive.ofMul u)
    exact hwP ((Submodule.Quotient.mk_eq_zero P).mp (hu ▸ hEq))
  have hconjbar (u : Gal(L/E)) :
      fbar (Additive.ofMul (relativeGaloisConj K E L s u)) = α • fbar (Additive.ofMul u) := by
    change q (f (Additive.ofMul (relativeGaloisConj K E L s u))) = α • q (f (Additive.ofMul u))
    rw [hconj, map_smul]
  have hscalarbar (u : Gal(L/E)) : k • fbar (Additive.ofMul u) = ε • fbar (Additive.ofMul u) := by
    change k • q (f (Additive.ofMul u)) = ε • q (f (Additive.ofMul u))
    rw [← map_nsmul, hscalar, map_smul]
  obtain ⟨u, hu, hnonzero⟩ := exists_nonzero_on_radical_stabilizer_of_smul_conjugation
    fbar hbar hβ hbase hroots s hs hsep hconjbar hscalarbar
  obtain ⟨b, hb⟩ := hgen u
  have hunit : IsUnit b := by
    by_contra h
    apply hnonzero
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    exact ⟨b, (IsLocalRing.mem_maximalIdeal _).mpr h, hb.symm⟩
  obtain ⟨b', hb'⟩ := hunit.exists_left_inv
  refine ⟨u, hu, fun v => ?_⟩
  obtain ⟨c, hc⟩ := hgen v
  exact ⟨c * b', by rw [hc, hb, mul_smul, ← mul_smul b' b, hb', one_smul]⟩

end Utilities
