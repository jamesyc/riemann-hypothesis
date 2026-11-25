module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Utilities.ModuleLengthBounds
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.Nakayama

@[expose] public section

open scoped BigOperators

namespace Utilities

section Nilpotence

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem range_pow_succ (f : Module.End R M) (n : ℕ) :
    LinearMap.range (f ^ (n + 1)) = (LinearMap.range (f ^ n)).map f := by
  rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]

/-- A nilpotent endomorphism vanishes at the module's composition length.
Equal consecutive ranges would force the earlier range to vanish. -/
theorem pow_eq_zero_of_isNilpotent_of_moduleLength_le
    (f : Module.End R M) {r : ℕ} (h : IsNilpotent f) (hlen : Module.length R M ≤ r) :
    f ^ r = 0 := by
  by_contra hne
  have hnonzero (n : ℕ) (hn : n ≤ r) : f ^ n ≠ 0 :=
    fun hz => hne (pow_eq_zero_of_le hn hz)
  have hstrict (n : ℕ) (hn : n ≤ r) :
      LinearMap.range (f ^ (n + 1)) < LinearMap.range (f ^ n) := by
    refine lt_of_le_of_ne ?_ ?_
    · rw [pow_succ, Module.End.mul_eq_comp]
      exact LinearMap.range_comp_le_range _ _
    · intro he
      obtain ⟨k, hk⟩ := h
      have hstable (j : ℕ) : LinearMap.range (f ^ (n + j)) = LinearMap.range (f ^ n) := by
        induction j with
        | zero => simp
        | succ j ih => rw [← add_assoc, range_pow_succ, ih, ← range_pow_succ, he]
      have hlast := hstable k
      rw [pow_add, hk, mul_zero, LinearMap.range_zero] at hlast
      exact hnonzero n hn (LinearMap.range_eq_bot.mp hlast.symm)
  have hheight (d n : ℕ) (hn : n + d = r) :
      (d : ℕ∞) + 1 ≤ Order.height (LinearMap.range (f ^ n)) := by
    induction d generalizing n with
    | zero =>
      have hbot : (⊥ : Submodule R M) < LinearMap.range (f ^ n) :=
        bot_lt_iff_ne_bot.mpr (fun hz => hnonzero n (by omega) (LinearMap.range_eq_bot.mp hz))
      simpa using (Order.height_add_one_le hbot : _)
    | succ d ih =>
      have hprev := ih (n + 1) (by omega)
      have hle := Order.height_add_one_le (hstrict n (by omega))
      push_cast
      simpa only [add_assoc] using (add_le_add hprev (le_refl (1 : ℕ∞))).trans hle
  rw [Module.length_eq_height] at hlen
  have hbad := (hheight r 0 (by simp)).trans ((Order.height_mono le_top).trans hlen)
  norm_cast at hbad
  omega

end Nilpotence

section Padic

variable {p : ℕ} [hp : Fact p.Prime] {X : Type*} [AddCommGroup X] [Module ℤ_[p] X]

/-- Composition length of an endomorphism's cokernel over the p-adic integers. -/
noncomputable def padicCokernelLength (f : Module.End ℤ_[p] X) : ℕ∞ :=
  Module.length ℤ_[p] (X ⧸ f.range)

/-- The submodule of scalar multiples, written as the range of multiplication. -/
noncomputable abbrev padicScalarRange (a : ℤ_[p]) : Submodule ℤ_[p] X :=
  LinearMap.range (a • (1 : Module.End ℤ_[p] X))

private theorem mem_padicScalarRange {a : ℤ_[p]} {x : X} :
    x ∈ padicScalarRange a ↔ ∃ y : X, x = a • y := by
  simp only [padicScalarRange, LinearMap.mem_range, LinearMap.smul_apply, one_apply_eq_self]
  exact exists_congr fun _ => eq_comm

/-- Reduce an endomorphism of a p-adic module modulo its submodule of
multiples of `p`. -/
noncomputable def padicEndModPrime (p : ℕ) [Fact p.Prime] (X : Type*) [AddCommGroup X] [Module ℤ_[p] X] :
    Module.End ℤ_[p] X →+* Module.End ℤ_[p] (X ⧸ padicScalarRange (X := X) (p : ℤ_[p])) := by
  let J : Submodule ℤ_[p] X := padicScalarRange (p : ℤ_[p])
  let red (f : Module.End ℤ_[p] X) := J.mapQ J f (by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_padicScalarRange.mp hx
    exact mem_padicScalarRange.mpr ⟨f y, f.map_smul _ _⟩)
  refine { toFun := red, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }
  · apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := J.mkQ_surjective q
    rfl
  · intro f g
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := J.mkQ_surjective q
    rfl
  · apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := J.mkQ_surjective q
    change J.mkQ 0 = _
    simp
  · intro f g
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := J.mkQ_surjective q
    change J.mkQ (f x + g x) = J.mkQ (f x) + J.mkQ (g x)
    exact map_add _ _ _

private theorem padicEndModPrime_eq_zero {f : Module.End ℤ_[p] X} :
    padicEndModPrime p X f = 0 ↔ ∀ x, ∃ y : X, f x = (p : ℤ_[p]) • y := by
  let J : Submodule ℤ_[p] X := padicScalarRange (p : ℤ_[p])
  have h (x : X) : padicEndModPrime p X f (J.mkQ x) = J.mkQ (f x) := rfl
  constructor
  · intro hz x
    have hx := h x
    rw [hz, LinearMap.zero_apply] at hx
    exact mem_padicScalarRange.mp ((Submodule.Quotient.mk_eq_zero J).mp hx.symm)
  · intro hz
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := J.mkQ_surjective q
    rw [h, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero J).mpr (mem_padicScalarRange.mpr (hz x))

private theorem length_modPrime_le {r : ℕ} (π : (Fin r → ℤ_[p]) →ₗ[ℤ_[p]] X)
    (hπ : Function.Surjective π) : Module.length ℤ_[p] (X ⧸ padicScalarRange (X := X) (p : ℤ_[p])) ≤ r := by
  classical
  let I : Submodule ℤ_[p] ℤ_[p] := IsLocalRing.maximalIdeal ℤ_[p]
  let P : Submodule ℤ_[p] (Fin r → ℤ_[p]) := Submodule.pi Set.univ fun _ => I
  let J : Submodule ℤ_[p] X := padicScalarRange (p : ℤ_[p])
  have hle : P ≤ J.comap π := by
    intro v hv
    have hcoord (i : Fin r) : ∃ t : ℤ_[p], v i = (p : ℤ_[p]) * t := by
      have hi := (Submodule.mem_pi.mp hv) i (Set.mem_univ i)
      change v i ∈ IsLocalRing.maximalIdeal ℤ_[p] at hi
      rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hi
    choose w hw using hcoord
    have hv' : v = (p : ℤ_[p]) • w := funext hw
    exact mem_padicScalarRange.mpr ⟨π w, by rw [hv', map_smul]⟩
  have hsurj : Function.Surjective (P.mapQ J π hle) := by
    intro z
    obtain ⟨x, rfl⟩ := J.mkQ_surjective z
    obtain ⟨v, rfl⟩ := hπ x
    exact ⟨P.mkQ v, rfl⟩
  have hsimple : IsSimpleModule ℤ_[p] (ℤ_[p] ⧸ I) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  have hlength : Module.length ℤ_[p] ((Fin r → ℤ_[p]) ⧸ P) = r := by
    rw [(Submodule.quotientPi (fun _ : Fin r => I)).length_eq, Module.length_pi_of_fintype]
    simp [Module.length_eq_one]
  exact (Module.length_le_of_surjective _ hsurj).trans_eq hlength

private theorem sum_powers_congruent (w : Module.End ℤ_[p] X) {a : ℤ_[p]}
    (h : ∀ x : X, (w - 1) x ∈ padicScalarRange a) (n : ℕ) (x : X) :
    ∃ y : X, (∑ j ∈ Finset.range n, w ^ j) x = (n : ℤ_[p]) • x + a • y := by
  have hpow (j : ℕ) : ∃ y : X, (w ^ j) x = x + a • y := by
    induction j with
    | zero => exact ⟨0, by simp⟩
    | succ j ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := mem_padicScalarRange.mp (h ((w ^ j) x))
      refine ⟨y + z, ?_⟩
      rw [pow_succ', mul_apply_eq_comp, smul_add, ← hz]
      simp only [LinearMap.sub_apply, one_apply_eq_self]
      rw [← add_assoc, ← hy]
      abel
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨z, hz⟩ := hpow n
    refine ⟨y + z, ?_⟩
    rw [Finset.sum_range_succ, LinearMap.add_apply, hy, hz, Nat.cast_succ, add_smul, one_smul, smul_add]
    abel

private theorem pow_sub_one_maps_to_padicScalarRange (w : Module.End ℤ_[p] X) {a : ℤ_[p]}
    (h : ∀ x : X, (w - 1) x ∈ padicScalarRange a) (n : ℕ) (x : X) :
    (w ^ n - 1) x ∈ padicScalarRange a := by
  obtain ⟨y, hy⟩ := mem_padicScalarRange.mp (h x)
  exact mem_padicScalarRange.mpr ⟨(∑ j ∈ Finset.range n, w ^ j) y, by
    rw [← geom_sum_mul, mul_apply_eq_comp, hy, map_smul]⟩

private theorem prime_pow_sub_one_maps_to_square (w : Module.End ℤ_[p] X)
    (h : ∀ x : X, (w - 1) x ∈ padicScalarRange (p : ℤ_[p])) (x : X) :
    (w ^ p - 1) x ∈ padicScalarRange ((p : ℤ_[p]) ^ 2) := by
  obtain ⟨y, hy⟩ := mem_padicScalarRange.mp (h x)
  obtain ⟨z, hz⟩ := sum_powers_congruent w h p y
  exact mem_padicScalarRange.mpr ⟨y + z, by
    rw [← geom_sum_mul, mul_apply_eq_comp, hy, map_smul, hz, ← smul_add, smul_smul, pow_two]⟩

private theorem range_prime_smul_le_range_geomSum {r : ℕ}
    (π : (Fin r → ℤ_[p]) →ₗ[ℤ_[p]] X) (hπ : Function.Surjective π) (w : Module.End ℤ_[p] X)
    (hw : ∀ x : X, (w - 1) x ∈ padicScalarRange ((p : ℤ_[p]) ^ 2)) :
    padicScalarRange (p : ℤ_[p]) ≤ LinearMap.range (∑ j ∈ Finset.range p, w ^ j) := by
  let _ : Module.Finite ℤ_[p] X := Module.Finite.of_surjective π hπ
  refine Submodule.le_of_le_smul_of_le_jacobson (I := Ideal.span {(p : ℤ_[p])})
    (IsNoetherian.noetherian _) ?_ ?_
  · rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
  · intro v hv
    obtain ⟨x, rfl⟩ := mem_padicScalarRange.mp hv
    obtain ⟨y, hy⟩ := sum_powers_congruent w hw p x
    have hx : (p : ℤ_[p]) • x =
        (∑ j ∈ Finset.range p, w ^ j) x + (p : ℤ_[p]) • ((p : ℤ_[p]) • (-y)) := by
      rw [hy, pow_two, mul_smul]
      simp
    rw [hx]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (mem_padicScalarRange.mpr ⟨-y, rfl⟩))

private theorem cokerLength_le_of_range_le {f g : Module.End ℤ_[p] X} (h : g.range ≤ f.range) :
    padicCokernelLength f ≤ padicCokernelLength g :=
  Module.length_le_of_surjective _ (Submodule.factor_surjective h)

private theorem padicCokernelLength_pow_sub_one_step {r : ℕ}
    (π : (Fin r → ℤ_[p]) →ₗ[ℤ_[p]] X) (hπ : Function.Surjective π) (w : Module.End ℤ_[p] X)
    (hw : ∀ x : X, (w - 1) x ∈ padicScalarRange ((p : ℤ_[p]) ^ 2)) :
    padicCokernelLength (w ^ p - 1) ≤ padicCokernelLength (w - 1) + r := by
  have hsum := cokerLength_le_of_range_le (range_prime_smul_le_range_geomSum π hπ w hw)
  have hmul := module_length_coker_mul_le (∑ j ∈ Finset.range p, w ^ j) (w - 1)
  rw [geom_sum_mul] at hmul
  exact hmul.trans ((add_le_add (hsum.trans (length_modPrime_le π hπ)) le_rfl).trans_eq (add_comm _ _))

private theorem padicCokernelLength_pow_sub_one_mono (g : Module.End ℤ_[p] X)
    {a b : ℕ} (hab : a ∣ b) : padicCokernelLength (g ^ a - 1) ≤ padicCokernelLength (g ^ b - 1) := by
  obtain ⟨k, rfl⟩ := hab
  apply cokerLength_le_of_range_le
  rw [pow_mul, ← mul_geom_sum]
  exact LinearMap.range_comp_le_range _ _

private theorem padicEndModPrime_natCast_prime :
    (Nat.cast p : Module.End ℤ_[p] (X ⧸ padicScalarRange (X := X) (p : ℤ_[p]))) = 0 := by
  rw [← map_natCast (padicEndModPrime p X)]
  apply padicEndModPrime_eq_zero.mpr
  intro x
  exact ⟨x, by rw [natCast_apply_eq_smul, Nat.cast_smul_eq_nsmul]⟩

private theorem pow_sub_one_maps_to_prime (g : Module.End ℤ_[p] X)
    {k : ℕ} (hg : (padicEndModPrime p X g - 1) ^ (p ^ k) = 0) (x : X) :
    (g ^ (p ^ k) - 1) x ∈ padicScalarRange (p : ℤ_[p]) := by
  apply mem_padicScalarRange.mpr
  apply padicEndModPrime_eq_zero.mp _ x
  rw [map_sub, map_pow, map_one]
  let W := Module.End ℤ_[p] (X ⧸ padicScalarRange (X := X) (p : ℤ_[p]))
  cases subsingleton_or_nontrivial W with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    let _ : Nontrivial W := h
    let _ : CharP W p := (CharP.charP_iff_prime_eq_zero hp.out).mpr padicEndModPrime_natCast_prime
    rw [sub_pow_char_pow_of_commute (p := p) (n := k) (Commute.one_right _), one_pow] at hg
    exact hg

/-- A scalar congruent to one does not change the reduction of an
endomorphism modulo `p`. -/
theorem padicEndModPrime_smul_of_dvd_sub_one (g : Module.End ℤ_[p] X) {a : ℤ_[p]}
    (ha : (p : ℤ_[p]) ∣ a - 1) :
    padicEndModPrime p X (a • g) = padicEndModPrime p X g := by
  obtain ⟨b, hb⟩ := ha
  rw [← sub_eq_zero, ← map_sub, padicEndModPrime_eq_zero]
  intro x
  exact ⟨b • g x, by
    change a • g x - g x = (p : ℤ_[p]) • (b • g x)
    rw [← mul_smul, ← hb, sub_smul, one_smul]⟩

/-- An endomorphism unipotent modulo `p` has cokernel lengths growing
by at most the generator bound per prime-power step beyond the reference
depth. Infinite lengths are allowed. -/
theorem padicCokernelLength_primePower_le_of_isNilpotent {r : ℕ}
    (π : (Fin r → ℤ_[p]) →ₗ[ℤ_[p]] X) (hπ : Function.Surjective π) (g : Module.End ℤ_[p] X)
    (hg : IsNilpotent (padicEndModPrime p X g - 1)) (j : ℕ) (hj : Nat.log p r + 2 ≤ j) (m : ℕ) :
    padicCokernelLength (g ^ (p ^ m) - 1) ≤
      padicCokernelLength (g ^ (p ^ j) - 1) + ((r * (m - j) : ℕ) : ℕ∞) := by
  let k := Nat.log p r + 1
  have hrk : r ≤ p ^ k := (Nat.lt_pow_succ_log_self hp.out.one_lt r).le
  have hmod : (padicEndModPrime p X g - 1) ^ (p ^ k) = 0 :=
    pow_eq_zero_of_le hrk (pow_eq_zero_of_isNilpotent_of_moduleLength_le _
      hg (length_modPrime_le π hπ))
  have hstart (x : X) : (g ^ (p ^ k) - 1) x ∈ padicScalarRange (p : ℤ_[p]) :=
    pow_sub_one_maps_to_prime g hmod x
  have hsquare (x : X) : (g ^ (p ^ (k + 1)) - 1) x ∈ padicScalarRange ((p : ℤ_[p]) ^ 2) := by
    rw [pow_succ p k, pow_mul]
    exact prime_pow_sub_one_maps_to_square _ hstart x
  have hstep (n : ℕ) (hn : j ≤ n) :
      padicCokernelLength (g ^ (p ^ (n + 1)) - 1) ≤ padicCokernelLength (g ^ (p ^ n) - 1) + r := by
    have hk : k + 1 ≤ n := hj.trans hn
    have hpow (x : X) : (g ^ (p ^ n) - 1) x ∈ padicScalarRange ((p : ℤ_[p]) ^ 2) := by
      rw [← Nat.add_sub_of_le hk, pow_add, pow_mul]
      exact pow_sub_one_maps_to_padicScalarRange _ hsquare _ x
    rw [pow_succ p n, pow_mul]
    exact padicCokernelLength_pow_sub_one_step π hπ _ hpow
  rcases le_total m j with hm | hm
  · simpa only [Nat.sub_eq_zero_of_le hm, mul_zero, Nat.cast_zero, add_zero] using
      padicCokernelLength_pow_sub_one_mono g (pow_dvd_pow p hm)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      _ ≤ padicCokernelLength (g ^ (p ^ (j + d)) - 1) + r :=
        hstep (j + d) (Nat.le_add_right _ _)
      _ ≤ (padicCokernelLength (g ^ (p ^ j) - 1) + ((r * d : ℕ) : ℕ∞)) + r := add_le_add ih le_rfl
      _ = _ := by push_cast; ring

end Padic

end Utilities
