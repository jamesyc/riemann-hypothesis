module

public import Utilities.KummerRadicalEquivariance
public import Utilities.RationalCyclotomicQuotient
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

namespace Utilities

private theorem root_pow_eq_of_modEq {L : Type*} [Field L] {z : L} {n a b : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) (h : a ≡ b [MOD n]) : z ^ a = z ^ b :=
  (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hz⟩).pow_eq_pow_iff_modEq.mpr
    (h.of_dvd (orderOf_dvd_of_pow_eq_one hz))

/-- A rational radical of order dividing the current cyclotomic level
cannot force an odd prime's next cyclotomic layer into its fixing field. -/
theorem exists_fixes_radical_and_roots_not_next
    {L : Type*} [Field L] [CharZero L] [IsGalois ℚ L] [IsAlgClosed L]
    {p n m a : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (hn : n ≠ 0) (hpn : p ∣ n)
    (hm : m ∣ n) (ha : a ≠ 0) {β : L} (hβ : β ^ m = (a : L)) :
    ∃ g : Gal(L/ℚ), (∀ z : L, z ^ n = 1 → g z = z) ∧ g β = β ∧
      ¬ (∀ z : L, z ^ (n * p) = 1 → g z = z) := by
  let N := n * p
  have hN : N ≠ 0 := mul_ne_zero hn hp.ne_zero
  let _ : NeZero N := ⟨hN⟩
  let _ : NeZero (N : L) := ⟨Nat.cast_ne_zero.mpr hN⟩
  have hnN : n ∣ N := dvd_mul_right _ _
  have hmN : m ∣ N := hm.trans hnN
  have hm₀ : m ≠ 0 := fun h => hN (zero_dvd_iff.mp (h ▸ hmN))
  have hβ₀ : β ≠ 0 := fun h => ha (Nat.cast_eq_zero.mp (by simpa only [h, zero_pow hm₀] using hβ.symm))
  obtain ⟨γ, hγsurj, hγ⟩ := exists_rationalCyclotomicQuotient (L := L) N
  have hcoord (s : Gal(L/ℚ)) {b : ℕ} (hb : ((γ s : (ZMod N)ˣ) : ZMod N) = b)
      {z : L} (hz : z ^ N = 1) : s z = z ^ b := by
    rw [hγ s z hz]
    apply root_pow_eq_of_modEq hN hz
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp ((ZMod.natCast_zmod_val _).trans hb)
  have hcop : (n + 1).Coprime N :=
    Nat.Coprime.mul_right (by simp) ((show (n + 1).Coprime n by simp).coprime_dvd_right hpn)
  let b := ZMod.unitOfCoprime (n + 1) hcop
  obtain ⟨u, hu⟩ := hγsurj b
  obtain ⟨s, hs⟩ := hγsurj (-1)
  have hsVal : ((γ s : (ZMod N)ˣ) : ZMod N) = ((N - 1 : ℕ) : ZMod N) := by
    rw [hs, Units.val_neg, Units.val_one, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN),
      ZMod.natCast_self, Nat.cast_one, zero_sub]
  have huVal : ((γ u : (ZMod N)ˣ) : ZMod N) = ((n + 1 : ℕ) : ZMod N) := by
    rw [hu, ZMod.coe_unitOfCoprime]
  have hrootN {z : L} {d : ℕ} (hd : d ∣ N) (hz : z ^ d = 1) : z ^ N = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one hz).trans hd)
  have huFix {z : L} (hz : z ^ m = 1) : u z = z := by
    rw [hcoord u huVal (hrootN hmN hz), pow_succ]
    rw [orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one hz).trans hm), one_mul]
  have hbase (t : Gal(L/ℚ)) : t (β ^ m) = β ^ m := by rw [hβ, map_natCast]
  have hconj := galoisConj_apply_radical_eq_pow hβ₀ hbase u (fun _ => huFix) s
    (fun _ hz => hcoord s hsVal (hrootN hmN hz))
  let g := u * (s * u * s⁻¹)
  have hgβ : g β = β := by
    change u ((s * u * s⁻¹) β) = β
    rw [hconj, ← AlgEquiv.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN)]
    have huRatio : (u β / β) ^ m = 1 := by
      rw [div_pow, ← map_pow, hbase, div_self (pow_ne_zero _ hβ₀)]
    rw [algEquiv_pow_apply_radical_eq hβ₀ u (hbase u) (fun _ => huFix),
      hrootN hmN huRatio, one_mul]
  have hgVal : ((γ g : (ZMod N)ˣ) : ZMod N) = (((n + 1) ^ 2 : ℕ) : ZMod N) := by
    have he : γ g = (γ u) ^ 2 := by
      dsimp only [g]
      simp only [map_mul, map_inv, mul_comm (γ s) (γ u), mul_inv_cancel_right, pow_two]
    rw [he, Units.val_pow_eq_pow_val, huVal, Nat.cast_pow]
  have hmod : (n + 1) ^ 2 ≡ 1 [MOD n] := by
    have h : n + 1 ≡ 1 [MOD n] := by simp [Nat.ModEq]
    simpa only [one_pow] using h.pow 2
  refine ⟨g, fun z hz => ?_, hgβ, fun hnext => ?_⟩
  · rw [hcoord g hgVal (hrootN hnN hz)]
    exact (root_pow_eq_of_modEq hn hz hmod).trans (pow_one z)
  · obtain ⟨ζ, hζ⟩ := (inferInstance : HasEnoughRootsOfUnity L N).prim
    have hζpow : ζ ^ ((n + 1) ^ 2) = ζ ^ (1 : ℕ) :=
      (hcoord g hgVal hζ.pow_eq_one).symm.trans ((hnext ζ hζ.pow_eq_one).trans (pow_one ζ).symm)
    have hh := (hζ.isOfFinOrder hN).pow_eq_pow_iff_modEq.mp hζpow
    rw [← hζ.eq_orderOf] at hh
    have hdiv : N ∣ (n + 1) ^ 2 - 1 := hh.symm.dvd'
    have hbinom : (n + 1) ^ 2 = n * (n + 2) + 1 := by ring
    rw [hbinom, Nat.add_sub_cancel] at hdiv
    have hpd : p ∣ n + 2 := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hn) hdiv
    have hp₂' : p ∣ 2 := (Nat.dvd_add_left hpn).mp (by simpa only [Nat.add_comm] using hpd)
    exact hp₂ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp₂')

/-- The quotient from one cyclotomic level to the next has exponent
dividing the prime when that prime already divides the current level. -/
theorem algEquiv_pow_prime_fixes_next_roots
    {L : Type*} [Field L] [CharZero L] [IsGalois ℚ L] [IsAlgClosed L]
    {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hpn : p ∣ n)
    (g : Gal(L/ℚ)) (hg : ∀ z : L, z ^ n = 1 → g z = z)
    {z : L} (hz : z ^ (n * p) = 1) : (g ^ p) z = z := by
  let N := n * p
  have hN : N ≠ 0 := mul_ne_zero hn hp.ne_zero
  let _ : NeZero N := ⟨hN⟩
  let _ : NeZero (N : L) := ⟨Nat.cast_ne_zero.mpr hN⟩
  let _ : NeZero (n : L) := ⟨Nat.cast_ne_zero.mpr hn⟩
  let _ : Fact (1 < N) := ⟨hp.one_lt.trans_le (Nat.le_mul_of_pos_left p (Nat.pos_of_ne_zero hn))⟩
  obtain ⟨γ, -, hγ⟩ := exists_rationalCyclotomicQuotient (L := L) N
  let b := (γ g).val.val
  have hb₀ : b ≠ 0 := by
    intro h
    have hval : (γ g).val = (b : ZMod N) := (ZMod.natCast_zmod_val _).symm
    exact (γ g).ne_zero (hval.trans (by simp [h]))
  obtain ⟨ζ, hζ⟩ := (inferInstance : HasEnoughRootsOfUnity L n).prim
  have hζN : ζ ^ N = 1 := by rw [show N = n * p from rfl, pow_mul, hζ.pow_eq_one, one_pow]
  have hh : ζ ^ b = ζ ^ (1 : ℕ) := (hγ g ζ hζN).symm.trans ((hg ζ hζ.pow_eq_one).trans (pow_one ζ).symm)
  have hd := (hζ.isOfFinOrder hn).pow_eq_pow_iff_modEq.mp hh
  rw [← hζ.eq_orderOf] at hd
  obtain ⟨k, hk⟩ := hd.symm.dvd'
  have hb : b = n * k + 1 :=
    (Nat.sub_add_cancel (Nat.pos_of_ne_zero hb₀)).symm.trans (congrArg (· + 1) hk)
  let t : ZMod N := ((n * k : ℕ) : ZMod N)
  have hval : (γ g).val = 1 + t := by
    rw [← ZMod.natCast_zmod_val (γ g).val]
    change (b : ZMod N) = _
    rw [hb, Nat.cast_add, Nat.cast_one, add_comm]
  have ht₂ : t * t = 0 := by
    change (((n * k : ℕ) : ZMod N) * ((n * k : ℕ) : ZMod N)) = 0
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    obtain ⟨j, hj⟩ := hpn
    refine ⟨j * k * k, ?_⟩
    dsimp only [N]
    rw [hj]
    ring
  have hpt : (p : ZMod N) * t = 0 := by
    change (p : ZMod N) * ((n * k : ℕ) : ZMod N) = 0
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact ⟨k, by dsimp only [N]; ring⟩
  have hpow (i : ℕ) : (1 + t) ^ i = 1 + (i : ZMod N) * t := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ih, Nat.cast_succ]
      calc
        _ = 1 + ((i : ZMod N) + 1) * t + (i : ZMod N) * (t * t) := by ring
        _ = _ := by rw [ht₂, mul_zero, add_zero]
  have he : γ (g ^ p) = 1 := by
    apply Units.ext
    rw [map_pow, Units.val_pow_eq_pow_val, hval, hpow, hpt, add_zero, Units.val_one]
  rw [hγ (g ^ p) z hz, he, Units.val_one, ZMod.val_one, pow_one]

/-- The subgroup fixing the current cyclotomic layer and the auxiliary
radical is not contained in the fixing subgroup of the next layer. -/
theorem radical_stabilizer_not_le_next_cyclotomic_fixingSubgroup
    {L : Type*} [Field L] [CharZero L] [IsGalois ℚ L] [IsAlgClosed L]
    {p n m a : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (hn : n ≠ 0) (hpn : p ∣ n)
    (hm : m ∣ n) (ha : a ≠ 0) {β : L} (hβ : β ^ m = (a : L))
    (E E' : IntermediateField ℚ L) [IsCyclotomicExtension {n} ℚ E]
    [IsCyclotomicExtension {n * p} ℚ E'] :
    ¬ E.fixingSubgroup ⊓ MulAction.stabilizer Gal(L/ℚ) β ≤ E'.fixingSubgroup := by
  let _ : NeZero n := ⟨hn⟩
  let _ : NeZero (n * p) := ⟨mul_ne_zero hn hp.ne_zero⟩
  obtain ⟨g, hg, hgβ, hnext⟩ := exists_fixes_radical_and_roots_not_next hp hp₂ hn hpn hm ha hβ
  intro h
  have hgE' := h ⟨mem_fixingSubgroup_of_fixes_cyclotomicLayer n E g hg, hgβ⟩
  apply hnext
  intro z hz
  exact (IntermediateField.mem_fixingSubgroup_iff E' g).mp hgE' z
    (mem_cyclotomicLayer_of_pow_eq_one (n * p) E' hz)

end Utilities
