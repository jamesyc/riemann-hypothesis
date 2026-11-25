module

public import Utilities.SelmerNormalization
public import Utilities.ModuleLengthBounds
public import Utilities.PadicTateTorsion
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

open scoped TensorProduct

namespace Utilities

/-- The scalar-extended Tate coefficient module remains power torsion
for the same rational prime. -/
theorem exists_pow_smul_eq_zero_extendedPadicTate (ℓ : ℕ) [Fact ℓ.Prime]
    (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S] (a : S ⊗[ℤ_[ℓ]] PadicTateQuotient ℓ) :
    ∃ r : ℕ, (ℓ : S) ^ r • a = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul s x =>
    obtain ⟨r, hr⟩ := exists_pow_smul_eq_zero_padicTateQuotient ℓ x
    refine ⟨r, ?_⟩
    rw [← map_natCast (algebraMap ℤ_[ℓ] S) ℓ, ← map_pow,
      IsScalarTower.algebraMap_smul S, ← TensorProduct.tmul_smul, hr, TensorProduct.tmul_zero]
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨max m n, ?_⟩
    rw [smul_add, pow_smul_eq_zero_of_le (le_max_left _ _) hm,
      pow_smul_eq_zero_of_le (le_max_right _ _) hn, add_zero]

/-- A uniform bound on weighted layer lengths gives a bound on the
weighted total length whenever uniform extended-natural bounds pass to it. -/
theorem length_log_bound_of_uniform_layers (len : ℕ∞) (layerLength : ℕ → ℕ∞)
    (hbound : ∀ N : ℕ∞, (∀ n, layerLength n ≤ N) → len ≤ N)
    {L : ℝ} (hL : 0 < L) (K : ℝ)
    (hLayer : ∀ n, layerLength n ≠ ⊤ ∧ ((layerLength n).toNat : ℝ) * L ≤ K) :
    len ≠ ⊤ ∧ (len.toNat : ℝ) * L ≤ K := by
  have hK : 0 ≤ K := (mul_nonneg (Nat.cast_nonneg _) hL.le).trans (hLayer 0).2
  have hdiv : 0 ≤ K / L := div_nonneg hK hL.le
  let N : ℕ := ⌊K / L⌋₊
  have hN (n : ℕ) : layerLength n ≤ (N : ℕ∞) := by
    obtain ⟨hfinite, hle⟩ := hLayer n
    rw [← ENat.natCast_toNat hfinite, ENat.natCast_le_natCast]
    exact (Nat.le_floor_iff hdiv).mpr ((le_div_iff₀ hL).mpr hle)
  have hlen := hbound N hN
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hlen, ?_⟩
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast ENat.toNat_le_of_le_natCast hlen) hL.le).trans
    ((le_div_iff₀ hL).mp (Nat.floor_le hdiv))

namespace DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [CompactSpace G]
  (A : DiscreteGaloisModule k G) (D : Set (Subgroup G)) (δ : G)

/-- On a compact source, a normalized locally constant cocycle takes
values in a single bounded layer of a power-torsion coefficient module. -/
theorem normalizedSelmerCocycles_powTorsion (a : k)
    (htors : ∀ x : A.rep, ∃ n : ℕ, a ^ n • x = 0)
    (f : normalizedSelmerCocycles A D δ) : ∃ n : ℕ, a ^ n • f = 0 := by
  have hfinite := f.property.1.1.2.range_finite
  classical
  choose m hm using htors
  obtain ⟨n, hn⟩ := (hfinite.image m).bddAbove
  refine ⟨n, ?_⟩
  apply Subtype.ext
  funext g
  change a ^ n • f.val g = 0
  exact pow_smul_eq_zero_of_le (hn (Set.mem_image_of_mem m (Set.mem_range_self g))) (hm _)

/-- A uniform bound on the normalized torsion layers bounds the full
Selmer kernel. -/
theorem selmerKernel_length_le_of_normalized_torsionLayers
    (hδ : Function.Bijective (A.rep.ρ δ - 1 : Module.End k A.rep))
    (a : k) (htors : ∀ x : A.rep, ∃ n : ℕ, a ^ n • x = 0)
    (N : ℕ∞) (hN : ∀ n : ℕ, Module.length k
      (Submodule.torsionBy k (normalizedSelmerCocycles A D δ) (a ^ n)) ≤ N) :
    Module.length k (A.selmerKernel D) ≤ N := by
  rw [← (normalizedSelmerCocyclesEquiv A D δ hδ).length_eq]
  exact module_length_le_of_torsionBy_pow_bounds a
    (normalizedSelmerCocycles_powTorsion A D δ a htors) N hN

/-- A common real bound for the weighted lengths of the finite exponent
layers gives the same bound on the full Selmer length. -/
theorem selmerKernel_log_bound_of_normalized_torsionLayers
    (hδ : Function.Bijective (A.rep.ρ δ - 1 : Module.End k A.rep))
    (a : k) (htors : ∀ x : A.rep, ∃ n : ℕ, a ^ n • x = 0)
    {L : ℝ} (hL : 0 < L) (K : ℝ)
    (hN : ∀ n : ℕ,
      let m : ℕ∞ := Module.length k
        (Submodule.torsionBy k (normalizedSelmerCocycles A D δ) (a ^ n))
      m ≠ ⊤ ∧ (ENat.toNat m : ℝ) * L ≤ K) :
    Module.length k (A.selmerKernel D) ≠ ⊤ ∧
      ((Module.length k (A.selmerKernel D)).toNat : ℝ) * L ≤ K := by
  exact length_log_bound_of_uniform_layers _ _
    (selmerKernel_length_le_of_normalized_torsionLayers A D δ hδ a htors) hL K hN

end DiscreteGaloisModule
end Utilities
