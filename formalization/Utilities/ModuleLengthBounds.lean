module

public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

namespace Utilities

theorem module_length_le_of_ker_le_range {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.ker ≤ f.range) :
    Module.length R B ≤ Module.length R A + Module.length R C := by
  rw [Module.length_eq_add_of_exact g.ker.subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])]
  exact add_le_add
    ((Module.length_le_of_injective _ (Submodule.inclusion_injective h)).trans
      (Module.length_le_of_surjective _ f.surjective_rangeRestrict))
    (Module.length_le_of_injective _ (Submodule.subtype_injective _))

/-- The kernel of a composite has length at most the sum of the two kernel lengths. -/
theorem module_length_ker_mul_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f g : Module.End R M) :
    Module.length R (LinearMap.ker (f * g)) ≤
      Module.length R (LinearMap.ker f) + Module.length R (LinearMap.ker g) := by
  have hle : g.ker ≤ (f * g).ker := by
    intro x hx
    rw [LinearMap.mem_ker, mul_apply_eq_comp, LinearMap.mem_ker.mp hx, map_zero]
  have hg : ∀ x ∈ (f * g).ker, g x ∈ f.ker := fun _ hx => hx
  rw [add_comm]
  apply module_length_le_of_ker_le_range (Submodule.inclusion hle) (LinearMap.restrict g hg)
  intro x hx
  exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩

theorem module_length_ker_pow_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f : Module.End R M) (r : ℕ) :
    Module.length R (LinearMap.ker (f ^ r)) ≤
      (r : ℕ∞) * Module.length R f.ker := by
  induction r with
  | zero =>
    rw [show f ^ (0 : ℕ) = (1 : Module.End R M) from pow_zero f, Nat.cast_zero, zero_mul]
    change Module.length R (LinearMap.ker (LinearMap.id : M →ₗ[R] M)) ≤ 0
    rw [LinearMap.ker_id, nonpos_iff_eq_zero, Module.length_eq_zero_iff]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    calc
      _ ≤ Module.length R (LinearMap.ker (f ^ n)) + Module.length R f.ker :=
        module_length_ker_mul_le (f ^ n) f
      _ ≤ (n : ℕ∞) * Module.length R f.ker + Module.length R f.ker := add_le_add ih le_rfl
      _ = _ := by push_cast; rw [add_mul, one_mul]

/-- The cokernel of a composite has length at most the sum of the two
cokernel lengths. -/
theorem module_length_coker_mul_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f g : Module.End R M) :
    Module.length R (M ⧸ LinearMap.range (f * g)) ≤
      Module.length R (M ⧸ LinearMap.range f) + Module.length R (M ⧸ LinearMap.range g) := by
  have hg : g.range ≤ (LinearMap.range (f * g)).comap f := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have hf : LinearMap.range (f * g) ≤ f.range.comap LinearMap.id := by
    rintro _ ⟨y, rfl⟩
    exact ⟨g y, rfl⟩
  rw [add_comm]
  refine module_length_le_of_ker_le_range (g.range.mapQ _ f hg) (_root_.Submodule.mapQ _ _ LinearMap.id hf)
    fun x hx => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨Submodule.Quotient.mk y, by rw [Submodule.mapQ_apply, hy]; rfl⟩

/-- A submodule killed by a power has length controlled by the exponent and
the first torsion layer of the ambient module. -/
theorem module_length_le_torsionBy_pow {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] (P : Submodule R M)
    (a : R) (r : ℕ) (hP : ∀ x ∈ P, a ^ r • x = 0) :
    Module.length R P ≤ (r : ℕ∞) * Module.length R (Submodule.torsionBy R M a) := by
  let f := a • (1 : Module.End R M)
  have hker : f.ker = Submodule.torsionBy R M a := by
    ext x
    simp [f, Submodule.mem_torsionBy_iff]
  have hle : P ≤ (f ^ r).ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    simpa [f, smul_pow] using hP x hx
  calc
    _ ≤ Module.length R (f ^ r).ker :=
      Module.length_le_of_injective _ (Submodule.inclusion_injective hle)
    _ ≤ _ := by rw [← hker]; exact module_length_ker_pow_le f r

/-- A strictly increasing finite rank pays for the length lost at each
step. A step is required only while the current submodule is nonzero. -/
theorem module_length_add_rank_le_of_bounded_steps {R M ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (C : ι → Submodule R M) (rank : ι → ℕ∞) (B : ℕ∞)
    (hB : B ≠ ⊤) (hbound : ∀ i, rank i ≤ B)
    (hstep : ∀ i, C i ≠ ⊥ → ∃ j, rank i < rank j ∧
      Module.length R (C i) + rank i ≤ Module.length R (C j) + rank j)
    (i : ι) : Module.length R (C i) + rank i ≤ B := by
  have hfinite (j : ι) : rank j ≠ ⊤ := ne_top_of_le_ne_top hB (hbound j)
  suffices h : ∀ n : ℕ, ∀ j : ι, B.toNat - (rank j).toNat = n →
      Module.length R (C j) + rank j ≤ B by exact h _ i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro j hj
    by_cases hz : C j = ⊥
    · rw [hz, Module.length_bot, zero_add]
      exact hbound j
    · obtain ⟨k, hk, hle⟩ := hstep j hz
      have hkn : (rank j).toNat < (rank k).toNat := by
        rw [← ENat.natCast_toNat (hfinite j), ← ENat.natCast_toNat (hfinite k)] at hk
        exact_mod_cast hk
      have hb := ENat.toNat_le_toNat (hbound k) hB
      exact hle.trans (ih _ (by omega) k rfl)

/-- A module covered by an increasing sequence of submodules of uniformly
bounded length has that same length bound. -/
theorem module_length_le_of_covering_monotone {R X : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] (P : ℕ → Submodule R X) (hmono : Monotone P)
    (hcover : ∀ x : X, ∃ n, x ∈ P n) (N : ℕ∞) (hN : ∀ n, Module.length R (P n) ≤ N) :
    Module.length R X ≤ N := by
  classical
  rw [Module.length_eq_height]
  apply Order.height_le
  intro p _
  have hstep (j : Fin p.length) : p j.castSucc < p j.succ := p.step j
  choose x hx hx' using fun j : Fin p.length => IsConcreteLE.exists_of_lt (hstep j)
  choose m hm using fun j : Fin p.length => hcover (x j)
  let n := Finset.univ.sup m
  have hxn (j : Fin p.length) : x j ∈ P n :=
    hmono (Finset.le_sup (Finset.mem_univ j)) (hm j)
  let q : LTSeries (Submodule R (P n)) :=
    { length := p.length
      toFun := fun j => (p j).comap (P n).subtype
      step := fun j => by
        apply lt_of_le_of_ne (Submodule.comap_mono (hstep j).le)
        intro he
        have hmem : (⟨x j, hxn j⟩ : P n) ∈ (p j.succ).comap (P n).subtype := hx j
        exact hx' j (show (⟨x j, hxn j⟩ : P n) ∈ (p j.castSucc).comap (P n).subtype from he.symm ▸ hmem) }
  have hq : (p.length : ℕ∞) ≤ Order.height (⊤ : Submodule R (P n)) :=
    Order.length_le_height (p := q) le_top
  exact hq.trans ((Module.length_eq_height R (P n)).symm ▸ hN n)

/-- Bound the length of a power-torsion module by uniformly bounding its
bounded-exponent layers. -/
theorem module_length_le_of_torsionBy_pow_bounds {R X : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] (a : R) (ha : ∀ x : X, ∃ n : ℕ, a ^ n • x = 0)
    (N : ℕ∞) (hN : ∀ n : ℕ, Module.length R (Submodule.torsionBy R X (a ^ n)) ≤ N) :
    Module.length R X ≤ N :=
  module_length_le_of_covering_monotone (fun n => Submodule.torsionBy R X (a ^ n))
    (fun _ _ h => Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow a h))
    (fun x => Exists.imp (fun n h => (Submodule.mem_torsionBy_iff (a ^ n) x).mpr h) (ha x)) N hN

end Utilities
