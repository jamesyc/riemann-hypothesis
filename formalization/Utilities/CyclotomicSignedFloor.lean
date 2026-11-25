module

public import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace Utilities

/-- The signed floor exponents of a Jacobi radicand. -/
def cyclotomicSignedFloor (N b : ℕ) (t : ZMod N) : ℤ :=
  (b * t.val / N : ℕ) - ((b * (-t).val / N : ℕ) : ℤ)

private theorem sum_affine_mod {q b : ℕ} (hq : 0 < q) (hb : q.Coprime b) (a : ℕ) :
    ∑ i ∈ Finset.range q, (a + i * b) % q = ∑ i ∈ Finset.range q, i := by
  let f (i : ℕ) := (a + i * b) % q
  have hinj : Set.InjOn f (Finset.range q : Set ℕ) := by
    intro i hi j hj hij
    exact (Nat.ModEq.cancel_right_of_coprime hb (Nat.ModEq.add_left_cancel' a hij)).eq_of_lt_of_lt
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  have himage : (Finset.range q).image f = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · rintro j hj
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
    · rw [Finset.card_image_of_injOn hinj]
  simpa only [himage, id_eq, f] using (Finset.sum_image (f := id) hinj).symm

private theorem sum_floor_on_progression {N q b : ℕ} (hN : 0 < N) (hq : q.Prime)
    (hb : b < q) (a : ℕ) :
    ∑ i ∈ Finset.range q, ((a + i * N) * b) / (q * N) =
      a * b / N + ∑ i ∈ Finset.range q, i * b / q := by
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp
  have hcop := Nat.coprime_of_lt_prime hb₀ hb hq
  have hsum (c : ℕ) :
      q * (∑ i ∈ Finset.range q, (c + i * b) / q) + ∑ i ∈ Finset.range q, i =
        q * c + ∑ i ∈ Finset.range q, i * b := by
    rw [← sum_affine_mod hq.pos hcop c, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [Nat.div_add_mod, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rfl
  have hadd (c : ℕ) : ∑ i ∈ Finset.range q, (c + i * b) / q =
      c + ∑ i ∈ Finset.range q, i * b / q := by
    have h0 := hsum 0
    simp only [zero_add, mul_zero] at h0
    have hc := hsum c
    apply Nat.eq_of_mul_eq_mul_left hq.pos
    rw [mul_add]
    omega
  rw [← hadd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm q N, ← Nat.div_div_eq_div_mul,
    show (a + i * N) * b = a * b + i * b * N by ring, Nat.add_mul_div_right _ _ hN]

private theorem sum_residue_class {A : Type*} [AddCommMonoid A]
    {N q a : ℕ} (ha : a < N) (f : ℕ → A) :
    ∑ n ∈ (Finset.range (q * N)).filter (fun n => n % N = a), f n =
      ∑ i ∈ Finset.range q, f (a + i * N) := by
  have hN : 0 < N := Nat.zero_lt_of_lt ha
  symm
  refine Finset.sum_nbij' (fun i => a + i * N) (fun n => n / N) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_filter] at hi ⊢
    exact ⟨by nlinarith, by simp [Nat.mod_eq_of_lt ha]⟩
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter] at hn ⊢
    exact (Nat.div_lt_iff_lt_mul hN).mpr hn.1
  · intro i _
    rw [Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt ha, zero_add]
  · intro n hn
    rw [← (Finset.mem_filter.mp hn).2, mul_comm]
    exact Nat.mod_add_div n N

variable {N q : ℕ} [NeZero N] [NeZero (q * N)]

local notation "ρ" => ZMod.unitsMap (dvd_mul_left N q)

-- The fiber of units is the full residue class with its unique multiple of q removed.
private theorem sum_unit_fiber {A : Type*} [AddCommMonoid A]
    (hq : q.Prime) (u t : (ZMod N)ˣ) (hu : (u : ZMod N) = q) (f : ℕ → A) :
    (∑ x ∈ Finset.univ.filter (fun x : (ZMod (q * N))ˣ => ρ x = t), f (x : ZMod (q * N)).val) +
      f (q * ((u⁻¹ * t : (ZMod N)ˣ) : ZMod N).val) =
      ∑ i ∈ Finset.range q, f ((t : ZMod N).val + i * N) := by
  let s := u⁻¹ * t
  have hmul : (q : ZMod N) * (s : ZMod N) = t := by
    rw [← hu, ← Units.val_mul, show u * s = t by simp [s]]
  have hmod (n : ℕ) : n % N = (t : ZMod N).val ↔ (n : ZMod N) = t := by
    rw [← ZMod.val_natCast]
    exact (ZMod.val_injective N).eq_iff
  let S := (Finset.range (q * N)).filter (fun n => n % N = (t : ZMod N).val)
  let e := q * (s : ZMod N).val
  have he : e ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hq.pos), (hmod _).mpr ?_⟩
    simpa only [e, Nat.cast_mul, ZMod.natCast_zmod_val] using hmul
  have hdvd (n : ℕ) (hn : n ∈ S) : q ∣ n ↔ n = e := by
    refine ⟨?_, fun h => h ▸ dvd_mul_right q (s : ZMod N).val⟩
    rintro ⟨k, rfl⟩
    have hk : k < N := Nat.lt_of_mul_lt_mul_left (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
    have hcast := (hmod _).mp (Finset.mem_filter.mp hn).2
    rw [Nat.cast_mul, ← hmul, ← hu] at hcast
    have hval := congrArg ZMod.val (u.isUnit.mul_left_cancel hcast)
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk] at hval
    simp [e, hval]
  rw [← sum_residue_class (ZMod.val_lt (t : ZMod N)) f]
  change _ + f e = ∑ n ∈ S, f n
  rw [← Finset.sum_erase_add S f he]
  congr 1
  refine Finset.sum_bij (fun x _ => (x : ZMod (q * N)).val) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hmem : (x : ZMod (q * N)).val ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), (hmod _).mpr ?_⟩
      rw [← hx'.2, ZMod.unitsMap_val, ZMod.natCast_val]
    refine Finset.mem_erase.mpr ⟨fun h => ?_, hmem⟩
    have hc := (ZMod.val_coe_unit_coprime x).of_dvd_right (dvd_mul_right q N)
    exact (hq.coprime_iff_not_dvd.mp hc.symm) ((hdvd _ hmem).mpr h)
  · intro x _ y _ h
    exact Units.ext (ZMod.val_injective _ h)
  · intro n hn
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hn
    obtain ⟨hlt, hrem⟩ := Finset.mem_filter.mp hmem
    have ht := (hmod _).mp hrem
    have hcN : n.Coprime N := (ZMod.isUnit_iff_coprime n N).mp (ht.symm ▸ t.isUnit)
    have hcq := (hq.coprime_iff_not_dvd.mpr (fun h => hne ((hdvd _ hmem).mp h))).symm
    let x := ZMod.unitOfCoprime n (hcq.mul_right hcN)
    have hx : (x : ZMod (q * N)).val = n := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hlt)]
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Units.ext ?_⟩, hx⟩
    rw [ZMod.unitsMap_val, ← ZMod.natCast_val, hx, ht]

/-- The exponents above a lower-level automorphism sum to its signed exponent minus
the exponent translated by inverse Frobenius at the new prime. -/
theorem cyclotomicSignedFloor_sum_fiber (hq : q.Prime) {b : ℕ} (hb : b < q)
    (u t : (ZMod N)ˣ) (hu : (u : ZMod N) = q) :
    ∑ x ∈ Finset.univ.filter (fun x : (ZMod (q * N))ˣ => ρ x = t), cyclotomicSignedFloor (q * N) b x.val =
      cyclotomicSignedFloor N b t.val - cyclotomicSignedFloor N b (u⁻¹ * t).val := by
  let floor (n m : ℕ) : ℤ := (n * b / m : ℕ)
  let C : ℤ := (∑ i ∈ Finset.range q, i * b / q : ℕ)
  have hf (s : (ZMod N)ˣ) :
      (∑ x ∈ Finset.univ.filter (fun x : (ZMod (q * N))ˣ => ρ x = s), floor (x : ZMod (q * N)).val (q * N)) +
        floor ((u⁻¹ * s : (ZMod N)ˣ) : ZMod N).val N = floor (s : ZMod N).val N + C := by
    have h := sum_unit_fiber hq u s hu (fun n => n * b / (q * N))
    rw [sum_floor_on_progression (Nat.pos_of_ne_zero (NeZero.ne N)) hq hb,
      mul_assoc, Nat.mul_div_mul_left _ _ hq.pos] at h
    dsimp only [floor, C]
    exact_mod_cast h
  have hneg (x : (ZMod (q * N))ˣ) : ρ (-x) = -ρ x := by
    apply Units.ext
    rw [ZMod.unitsMap_val, Units.val_neg, Units.val_neg, ZMod.unitsMap_val,
      ZMod.cast_neg (dvd_mul_left N q)]
  have hreindex :
      (∑ x ∈ Finset.univ.filter (fun x : (ZMod (q * N))ˣ => ρ x = t), floor (-(x : ZMod (q * N))).val (q * N)) =
        ∑ x ∈ Finset.univ.filter (fun x : (ZMod (q * N))ˣ => ρ x = -t), floor (x : ZMod (q * N)).val (q * N) := by
    refine Finset.sum_equiv (Equiv.neg _) (fun x => ?_) (fun x _ => ?_)
    · simp [hneg]
    · simp only [Equiv.neg_apply, Units.val_neg]
  have ht := hf t
  have hnt := hf (-t)
  rw [mul_neg, Units.val_neg, Units.val_neg] at hnt
  simp only [cyclotomicSignedFloor, mul_comm b, Finset.sum_sub_distrib]
  change (_ - ∑ x ∈ Finset.univ.filter (fun x : (ZMod (q * N))ˣ => ρ x = t),
      floor (-(x : ZMod (q * N))).val (q * N)) = _
  rw [hreindex]
  linarith

end Utilities
