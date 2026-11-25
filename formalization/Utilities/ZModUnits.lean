module

public import Mathlib.Data.ZMod.Units
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace Utilities

theorem zmodUnitsMap_comp_apply {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) (u : (ZMod c)ˣ) :
    ZMod.unitsMap hab (ZMod.unitsMap hbc u) = ZMod.unitsMap (dvd_trans hab hbc) u :=
  DFunLike.congr_fun (ZMod.unitsMap_comp hab hbc) u

theorem zmodUnitsMap_neg_one {m n : ℕ} (h : m ∣ n) : ZMod.unitsMap h (-1) = -1 :=
  Units.map_neg_one (ZMod.castHom h (ZMod m))

/-- CRT on the unit groups, using the ring isomorphism on each factor. -/
noncomputable def zmodUnitsCRT {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans .prodUnits

theorem zmodUnitsCRT_apply {m n : ℕ} (h : m.Coprime n) (u : (ZMod (m * n))ˣ) :
    zmodUnitsCRT h u = (ZMod.unitsMap (dvd_mul_right m n) u,
      ZMod.unitsMap (dvd_mul_left n m) u) := by
  apply Prod.ext <;> apply Units.ext
  · exact Prod.fst_zmod_cast (u : ZMod (m * n))
  · exact Prod.snd_zmod_cast (u : ZMod (m * n))

theorem zmodUnitsCongr_apply {m n : ℕ} (h : m = n) (hd : n ∣ m) (u : (ZMod m)ˣ) :
    Units.mapEquiv (ZMod.ringEquivCongr h).toMulEquiv u = ZMod.unitsMap hd u := by
  subst n
  rw [ZMod.ringEquivCongr_refl, ZMod.unitsMap_self]
  rfl

theorem zmodUnitsMap_unitOfCoprime {N M a : ℕ} (h : N ∣ M)
    (haN : a.Coprime N) (haM : a.Coprime M) :
    ZMod.unitsMap h (ZMod.unitOfCoprime a haM) = ZMod.unitOfCoprime a haN := by
  apply Units.ext
  simp only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]

/-- Split a sum over units at the larger level into residue classes at
the smaller level when raising the level introduces no new prime divisors. -/
theorem sum_zmodUnits_mul_level {N m : ℕ} [NeZero N] [NeZero m]
    (hcoprime : ∀ r : ℕ, r.Coprime N → r.Coprime (N * m))
    {A : Type*} [AddCommMonoid A] (f : (ZMod N)ˣ → ℕ → A) :
    (∑ u : (ZMod (N * m))ˣ, f (ZMod.unitsMap (dvd_mul_right N m) u) (u : ZMod (N * m)).val) =
      ∑ b : (ZMod N)ˣ, ∑ j ∈ Finset.range m, f b ((b : ZMod N).val + j * N) := by
  let r := ZMod.unitsMap (dvd_mul_right N m)
  let residue (z : (ZMod N)ˣ × Fin m) : ℕ := (z.1 : ZMod N).val + z.2.val * N
  have hcop (z : (ZMod N)ˣ × Fin m) : (residue z).Coprime (N * m) :=
    hcoprime _ ((Nat.coprime_add_mul_right_left _ _ _).mpr (ZMod.val_coe_unit_coprime z.1))
  have hlt (z : (ZMod N)ˣ × Fin m) : residue z < N * m := by
    calc
      residue z < N + z.2.val * N := Nat.add_lt_add_right (ZMod.val_lt _) _
      _ = (z.2.val + 1) * N := by rw [Nat.add_mul, one_mul, Nat.add_comm]
      _ ≤ N * m := by
        rw [Nat.mul_comm N m]
        exact Nat.mul_le_mul_right N (Nat.succ_le_of_lt z.2.isLt)
  let lift (z : (ZMod N)ˣ × Fin m) := ZMod.unitOfCoprime (residue z) (hcop z)
  have hval (z : (ZMod N)ˣ × Fin m) : (lift z : ZMod (N * m)).val = residue z :=
    ZMod.val_natCast_of_lt (hlt z)
  have hred (z : (ZMod N)ˣ × Fin m) : r (lift z) = z.1 := by
    apply Units.ext
    change (ZMod.unitsMap (dvd_mul_right N m) (lift z) : ZMod N) = z.1.val
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val, hval]
    simp [residue, Nat.cast_add, Nat.cast_mul]
  let parts (u : (ZMod (N * m))ˣ) : (ZMod N)ˣ × Fin m :=
    (r u, ⟨(u : ZMod (N * m)).val / N,
      (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr (by simpa [Nat.mul_comm] using ZMod.val_lt u.val)⟩)
  let e : (ZMod (N * m))ˣ ≃ (ZMod N)ˣ × Fin m :=
    { toFun := parts
      invFun := lift
      left_inv := fun u => by
        apply Units.ext
        apply ZMod.val_injective (N * m)
        rw [hval]
        dsimp only [residue, parts, r]
        rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast]
        exact Nat.mod_add_div' _ _
      right_inv := fun z => Prod.ext (hred z) (Fin.ext (by
        change (lift z : ZMod (N * m)).val / N = z.2.val
        rw [hval]
        dsimp only [residue]
        rw [Nat.mul_comm z.2.val N, Nat.add_mul_div_left _ _ (NeZero.pos N),
          Nat.div_eq_of_lt (ZMod.val_lt z.1.val), zero_add])) }
  have hsum : (∑ u : (ZMod (N * m))ˣ, f (r u) (u : ZMod (N * m)).val) =
      ∑ z : (ZMod N)ˣ × Fin m, f z.1 (residue z) := by
    symm
    apply Fintype.sum_equiv e.symm
    intro z
    change f z.1 (residue z) = f (r (lift z)) (lift z : ZMod (N * m)).val
    rw [hred, hval]
  change (∑ u : (ZMod (N * m))ˣ, f (r u) (u : ZMod (N * m)).val) = _
  rw [hsum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  exact Fin.sum_univ_eq_sum_range (fun j => f b ((b : ZMod N).val + j * N)) m

end Utilities
