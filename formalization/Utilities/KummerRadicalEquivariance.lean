module

public import Utilities.KrullConjugation
public import Mathlib.Algebra.Group.TypeTags.Hom

@[expose] public section

namespace Utilities

variable {K E L : Type*} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] [Normal K E]

private theorem radicalRatio_pow_eq_one {n : ℕ} {β : L} (hβ : β ≠ 0)
    (s : Gal(L/K)) (hs : s (β ^ n) = β ^ n) :
    (s β / β) ^ n = 1 := by
  rw [div_pow, ← map_pow, hs, div_self (pow_ne_zero n hβ)]

/-- Powers of an automorphism fixing the roots act on a radical by
the corresponding powers of its radical ratio. -/
theorem algEquiv_pow_apply_radical_eq {n : ℕ} {β : L} (hβ : β ≠ 0)
    (u : Gal(L/K)) (hu : u (β ^ n) = β ^ n)
    (hroots : ∀ x : L, x ^ n = 1 → u x = x) (j : ℕ) :
    (u ^ j) β = (u β / β) ^ j * β := by
  let ζ := u β / β
  have hζ : ζ ^ n = 1 := radicalRatio_pow_eq_one hβ u hu
  have huβ : u β = ζ * β := (div_mul_cancel₀ _ hβ).symm
  change (u ^ j) β = ζ ^ j * β
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hroots ζ hζ, huβ, pow_succ, mul_assoc]

/-- Conjugating an automorphism that fixes the nth roots changes its
radical ratio by the conjugating automorphism's action on those roots. -/
theorem galoisConj_apply_radical_eq_pow {n k : ℕ} {β : L} (hβ : β ≠ 0)
    (hbase : ∀ s : Gal(L/K), s (β ^ n) = β ^ n)
    (u : Gal(L/K)) (hroots : ∀ x : L, x ^ n = 1 → u x = x)
    (s : Gal(L/K)) (hs : ∀ x : L, x ^ n = 1 → s x = x ^ k) :
    (s * u * s⁻¹) β = (u ^ k) β := by
  let ζ := u β / β
  let ξ := s.symm β / β
  have hζ : ζ ^ n = 1 := radicalRatio_pow_eq_one hβ u (hbase u)
  have hξ : ξ ^ n = 1 := radicalRatio_pow_eq_one hβ s.symm (hbase _)
  have hu : u β = ζ * β := (div_mul_cancel₀ _ hβ).symm
  have hsu : u (s.symm β) = ζ * s.symm β := by
    have he : s.symm β = ξ * β := (div_mul_cancel₀ _ hβ).symm
    rw [he, map_mul, hroots ξ hξ, hu, mul_left_comm]
  change s (u (s.symm β)) = _
  rw [hsu, map_mul, s.apply_symm_apply, hs ζ hζ, algEquiv_pow_apply_radical_eq hβ u (hbase u) hroots]

/-- The radical conjugation formula on the relative Galois group. -/
theorem relativeGaloisConj_apply_radical_eq_pow {n k : ℕ} {β : L} (hβ : β ≠ 0)
    (hbase : ∀ s : Gal(L/K), s (β ^ n) = β ^ n)
    (hroots : ∀ (u : Gal(L/E)) (x : L), x ^ n = 1 → u x = x)
    (s : Gal(L/K)) (hs : ∀ x : L, x ^ n = 1 → s x = x ^ k) (u : Gal(L/E)) :
    relativeGaloisConj K E L s u β = (u ^ k) β := by
  have h := galoisConj_apply_radical_eq_pow hβ hbase (u.restrictScalars K) (hroots u) s hs
  have hp : (u.restrictScalars K) ^ k = (u ^ k).restrictScalars K :=
    (map_pow (AlgEquiv.restrictScalarsHom K) u k).symm
  rw [← relativeGaloisConj_restrictScalars K E L s u, hp] at h
  exact h

/-- An additive character that vanishes on the radical's stabilizer
transforms under conjugation by the cyclotomic power on its quotient. -/
theorem additiveCharacter_conj_eq_nsmul_of_radical_vanishing
    {W : Type*} [AddGroup W] (f : Additive Gal(L/E) →+ W)
    {n k : ℕ} {β : L} (hβ : β ≠ 0)
    (hbase : ∀ s : Gal(L/K), s (β ^ n) = β ^ n)
    (hroots : ∀ (u : Gal(L/E)) (x : L), x ^ n = 1 → u x = x)
    (hvan : ∀ u : Gal(L/E), u β = β → f (Additive.ofMul u) = 0)
    (s : Gal(L/K)) (hs : ∀ x : L, x ^ n = 1 → s x = x ^ k) (u : Gal(L/E)) :
    f (Additive.ofMul (relativeGaloisConj K E L s u)) = k • f (Additive.ofMul u) := by
  let v := relativeGaloisConj K E L s u
  have he := relativeGaloisConj_apply_radical_eq_pow hβ hbase hroots s hs u
  let w := (u ^ k)⁻¹ * v
  have hw : w β = β := by
    change (u ^ k).symm (v β) = β
    rw [show v β = (u ^ k) β from he, AlgEquiv.symm_apply_apply]
  have hdecomp : v = (u ^ k) * w := (mul_inv_cancel_left _ _).symm
  calc
    f (Additive.ofMul v) = f (Additive.ofMul (u ^ k) + Additive.ofMul w) :=
      congrArg (f ∘ Additive.ofMul) hdecomp
    _ = _ := by rw [map_add, hvan w hw, add_zero]; exact map_nsmul f k (Additive.ofMul u)

/-- A nonzero character of different scalar action from the cyclotomic
action is nonzero on the stabilizer of a rational Kummer radical. -/
theorem exists_nonzero_on_radical_stabilizer_of_smul_conjugation
    {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (f : Additive Gal(L/E) →+ W) (hne : f ≠ 0)
    {n k : ℕ} {β : L} (hβ : β ≠ 0)
    (hbase : ∀ s : Gal(L/K), s (β ^ n) = β ^ n)
    (hroots : ∀ (u : Gal(L/E)) (x : L), x ^ n = 1 → u x = x)
    (s : Gal(L/K)) (hs : ∀ x : L, x ^ n = 1 → s x = x ^ k)
    {α ε : R} (hsep : IsUnit (α - ε))
    (hconj : ∀ u : Gal(L/E), f (Additive.ofMul (relativeGaloisConj K E L s u)) = α • f (Additive.ofMul u))
    (hscalar : ∀ u : Gal(L/E), k • f (Additive.ofMul u) = ε • f (Additive.ofMul u)) :
    ∃ u : Gal(L/E), u β = β ∧ f (Additive.ofMul u) ≠ 0 := by
  classical
  by_contra! hvan
  apply hne
  apply AddMonoidHom.ext
  intro u
  let v := Additive.toMul u
  have hc := additiveCharacter_conj_eq_nsmul_of_radical_vanishing f hβ hbase hroots hvan s hs v
  rw [hconj, hscalar] at hc
  change f (Additive.ofMul v) = 0
  exact hsep.smul_eq_zero.mp (by rw [sub_smul, hc, sub_self])

end Utilities
