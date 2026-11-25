module

public import Utilities.PadicTateTwist
public import Utilities.PadicCyclotomicImage
public import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Utilities.SelmerKernelTorsion

@[expose] public section

open groupCohomology

namespace Utilities

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime]

/-- Finite reduction of the p-adic cyclotomic character. -/
noncomputable def padicCyclotomicReduction (r : ℕ) :
    Field.absoluteGaloisGroup F →* (ZMod (p ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow (p := p) r).toMonoidHom).comp
    (show Field.absoluteGaloisGroup F →* ℤ_[p]ˣ from padicCyclotomicUnitsMap F p)

/-- The reduction of the cyclotomic character is characterized by
the automorphism's action on roots of unity. -/
theorem cyclotomicCharacter_toZModPow_eq_iff (K : Type*) [Field K]
    [∀ n, HasEnoughRootsOfUnity K (p ^ n)] (r : ℕ)
    (σ : K ≃+* K) (b : ZMod (p ^ r)) :
    (cyclotomicCharacter K p σ).val.toZModPow r = b ↔
      ∀ ζ : K, ζ ^ (p ^ r) = 1 → σ ζ = ζ ^ b.val := by
  constructor
  · intro h ζ hζ
    rw [cyclotomicCharacter.spec p σ ζ hζ, h]
  · intro h
    rw [cyclotomicCharacter.toZModPow]
    symm
    apply modularCyclotomicCharacter.unique
    intro ζ hζ
    exact h _ ((mem_rootsOfUnity' _ _).mp hζ)

/-- Reduction of the cyclotomic character is one exactly when the
automorphism fixes the roots of unity at that precision. -/
theorem cyclotomicCharacter_toZModPow_eq_one_iff (K : Type*) [Field K]
    [∀ n, HasEnoughRootsOfUnity K (p ^ n)] (r : ℕ) (σ : K ≃+* K) :
    (cyclotomicCharacter K p σ).val.toZModPow r = 1 ↔
      ∀ ζ : K, ζ ^ (p ^ r) = 1 → σ ζ = ζ := by
  rw [cyclotomicCharacter_toZModPow_eq_iff]
  by_cases hr : r = 0
  · subst r
    simp only [pow_zero, pow_one]
    constructor <;> intro _ ζ hζ <;> subst ζ <;> simp
  · let _ : Fact (1 < p ^ r) := ⟨one_lt_pow₀ (Fact.out : p.Prime).one_lt hr⟩
    simp only [ZMod.val_one, pow_one]

/-- On a root-fixing automorphism the Tate scalar is one modulo the
prime power defining the corresponding coefficient layer. -/
theorem padicTateScalarOnAut_toZModPow_eq_one_of_fixes_roots (K : Type) [Field K]
    [∀ n, HasEnoughRootsOfUnity K (p ^ n)] (i r : ℕ) (σ : K ≃+* K)
    (hσ : ∀ ζ : K, ζ ^ (p ^ r) = 1 → σ ζ = ζ) :
    PadicInt.toZModPow r (padicTateScalarOnAut K p i σ) = 1 := by
  let q := PadicInt.toZModPow (p := p) r
  have hu : Units.map q.toMonoidHom (cyclotomicCharacter K p σ) = 1 :=
    Units.ext ((cyclotomicCharacter_toZModPow_eq_one_iff p K r σ).mpr hσ)
  change ((Units.map q.toMonoidHom ((cyclotomicCharacter K p σ) ^ (-(i : ℤ)))) :
    ZMod (p ^ r)) = 1
  rw [map_zpow, hu, one_zpow, Units.val_one]

/-- The finite cyclotomic reduction is characterized by its action on roots of unity. -/
theorem padicCyclotomicReduction_eq_iff [CharZero F] (r : ℕ)
    (σ : Field.absoluteGaloisGroup F) (b : (ZMod (p ^ r))ˣ) :
    padicCyclotomicReduction F p r σ = b ↔
      ∀ ζ : AlgebraicClosure F, ζ ^ (p ^ r) = 1 →
        (show Gal(AlgebraicClosure F/F) from σ) ζ = ζ ^ b.val.val := by
  let τ : Gal(AlgebraicClosure F/F) := σ
  rw [← Units.val_inj]
  exact cyclotomicCharacter_toZModPow_eq_iff p (AlgebraicClosure F) r τ.toRingEquiv b.val

/-- The finite reduction is trivial exactly on automorphisms fixing the
roots of order `p ^ r`. -/
theorem mem_ker_padicCyclotomicReduction_iff [CharZero F] (r : ℕ)
    (σ : Field.absoluteGaloisGroup F) :
    σ ∈ (padicCyclotomicReduction F p r).ker ↔
      ∀ ζ : AlgebraicClosure F, ζ ^ (p ^ r) = 1 →
        (show Gal(AlgebraicClosure F/F) from σ) ζ = ζ := by
  rw [MonoidHom.mem_ker, ← Units.val_inj]
  exact cyclotomicCharacter_toZModPow_eq_one_iff p (AlgebraicClosure F) r
    (show Gal(AlgebraicClosure F/F) from σ).toRingEquiv

/-- The kernel of the full p-adic cyclotomic character fixes the roots
at every finite prime-power level. -/
theorem fixes_primePowRoots_of_mem_ker_padicCyclotomicUnitsMap [CharZero F]
    {σ : Field.absoluteGaloisGroup F} (hσ : σ ∈ (padicCyclotomicUnitsMap F p).ker)
    (r : ℕ) {ζ : AlgebraicClosure F} (hζ : ζ ^ (p ^ r) = 1) :
    (show Gal(AlgebraicClosure F/F) from σ) ζ = ζ := by
  apply (mem_ker_padicCyclotomicReduction_iff F p r σ).mp _ ζ hζ
  change Units.map (PadicInt.toZModPow (p := p) r).toMonoidHom
    (padicCyclotomicUnitsMap F p σ) = 1
  have hχ : padicCyclotomicUnitsMap F p (show Gal(AlgebraicClosure F/F) from σ) = 1 := hσ
  exact (congrArg (Units.map (PadicInt.toZModPow (p := p) r).toMonoidHom) hχ).trans (map_one _)

/-- Reduction agrees with the power action at any level divisible by the precision. -/
theorem cyclotomicCharacter_toZModPow_eq_natCast_of_acts_on_roots (K : Type*) [Field K]
    [∀ n, HasEnoughRootsOfUnity K (p ^ n)] (r : ℕ) {M : ℕ} (h : p ^ r ∣ M)
    (σ : K ≃+* K) (a : ℕ) (hσ : ∀ ζ : K, ζ ^ M = 1 → σ ζ = ζ ^ a) :
    (cyclotomicCharacter K p σ).val.toZModPow r = (a : ZMod (p ^ r)) := by
  apply (cyclotomicCharacter_toZModPow_eq_iff p K r σ _).mpr
  intro ζ hζ
  have hM : ζ ^ M = 1 := by
    obtain ⟨j, hj⟩ := h
    rw [hj, pow_mul, hζ, one_pow]
  rw [hσ ζ hM, ZMod.val_natCast]
  conv_lhs =>
    rw [← Nat.mod_add_div a (p ^ r), pow_add, pow_mul, hζ, one_pow, mul_one]

theorem padicCyclotomicReduction_eq_unitsMap_of_acts_on_roots [CharZero F]
    (r : ℕ) {M : ℕ} [NeZero M] (h : p ^ r ∣ M)
    (σ : Field.absoluteGaloisGroup F) (b : (ZMod M)ˣ)
    (hσ : ∀ ζ : AlgebraicClosure F, ζ ^ M = 1 →
      (show Gal(AlgebraicClosure F/F) from σ) ζ = ζ ^ b.val.val) :
    padicCyclotomicReduction F p r σ = ZMod.unitsMap h b := by
  let τ : Gal(AlgebraicClosure F/F) := σ
  apply Units.ext
  change (cyclotomicCharacter (AlgebraicClosure F) p τ.toRingEquiv).val.toZModPow r =
    (ZMod.unitsMap h b).val
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
  exact cyclotomicCharacter_toZModPow_eq_natCast_of_acts_on_roots p (AlgebraicClosure F)
    r h τ.toRingEquiv b.val.val hσ

/-- Congruent scalars act identically on the corresponding torsion layer. -/
theorem padicInt_smul_eq_of_toZModPow_eq {r : ℕ} {s t : ℤ_[p]}
    (hst : PadicInt.toZModPow r s = PadicInt.toZModPow r t)
    {X : Type*} [AddCommMonoid X] [Module ℤ_[p] X] {a : X}
    (ha : (p : ℤ_[p]) ^ r • a = 0) : s • a = t • a := by
  have hker : s - t ∈ RingHom.ker (PadicInt.toZModPow r) :=
    RingHom.mem_ker.mpr (by rw [map_sub, hst, sub_self])
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨b, hb⟩ := hker
  have he : s = t + (p : ℤ_[p]) ^ r * b := by linear_combination hb
  rw [he, add_smul, mul_comm ((p : ℤ_[p]) ^ r) b, mul_smul, ha, smul_zero, add_zero]

/-- A scalar congruent to one acts trivially on the corresponding torsion layer. -/
theorem padicInt_smul_eq_self_of_toZModPow_eq_one {r : ℕ} {s : ℤ_[p]}
    (hs : PadicInt.toZModPow r s = 1)
    {X : Type*} [AddCommMonoid X] [Module ℤ_[p] X] {a : X}
    (ha : (p : ℤ_[p]) ^ r • a = 0) : s • a = a := by
  simpa only [one_smul] using padicInt_smul_eq_of_toZModPow_eq p (hs.trans (map_one _).symm) ha

/-- The positive residue weight cancels the negative Tate action modulo the
prime power killing the coefficient. -/
theorem pow_smul_padicTateScalarOnAut_eq_self (K : Type) [Field K] (i r : ℕ)
    (σ : K ≃+* K) (B : ℤ_[p])
    (hB : PadicInt.toZModPow r B = PadicInt.toZModPow r (cyclotomicCharacter K p σ).val)
    {X : Type*} [AddCommMonoid X] [Module ℤ_[p] X] {x : X} (hx : (p : ℤ_[p]) ^ r • x = 0) :
    B ^ i • (padicTateScalarOnAut K p i σ • x) = x := by
  let u := cyclotomicCharacter K p σ
  let q := PadicInt.toZModPow (p := p) r
  rw [smul_smul]
  apply padicInt_smul_eq_self_of_toZModPow_eq_one p _ hx
  change q (B ^ i * ((u ^ (-(i : ℤ)) : ℤ_[p]ˣ) : ℤ_[p])) = 1
  rw [map_mul, map_pow, hB, ← map_pow, ← map_mul]
  change q ((u ^ i * u ^ (-(i : ℤ)) : ℤ_[p]ˣ).val) = 1
  simp only [zpow_neg, zpow_natCast, mul_inv_cancel, Units.val_one, map_one]

/-- The residue of a cyclotomic lift cancels the Tate factor on the bounded coefficients. -/
theorem natCast_pow_smul_padicTateScalarOnAut_eq_self_of_acts_on_roots
    (K : Type) [Field K] [∀ n, HasEnoughRootsOfUnity K (p ^ n)]
    (i r : ℕ) {M : ℕ} (h : p ^ r ∣ M) (σ : K ≃+* K) (a : ℕ)
    (hσ : ∀ ζ : K, ζ ^ M = 1 → σ ζ = ζ ^ a)
    {X : Type*} [AddCommMonoid X] [Module ℤ_[p] X] {x : X} (hx : (p : ℤ_[p]) ^ r • x = 0) :
    (a : ℤ_[p]) ^ i • (padicTateScalarOnAut K p i σ • x) = x :=
  pow_smul_padicTateScalarOnAut_eq_self p K i r σ (a : ℤ_[p])
    (by rw [map_natCast, cyclotomicCharacter_toZModPow_eq_natCast_of_acts_on_roots p K r h σ a hσ]) hx

/-- The kernel at precision `r` acts trivially on coefficients killed by `p ^ r`. -/
theorem padicTateTwist_ρ_apply_eq_self_on_powTorsion (i r : ℕ)
    {σ : Field.absoluteGaloisGroup F} (hσ : σ ∈ (padicCyclotomicReduction F p r).ker)
    (a : (padicTateTwist F p i).rep) (ha : (p : ℤ_[p]) ^ r • a = 0) :
    (padicTateTwist F p i).rep.ρ σ a = a := by
  let q := PadicInt.toZModPow (p := p) r
  let u := padicCyclotomicUnitsMap F p (show Gal(AlgebraicClosure F/F) from σ)
  have hu : Units.map q.toMonoidHom u = 1 := hσ
  let s := padicTateScalar F p i σ
  have hs : q s = 1 := by
    change ((Units.map q.toMonoidHom (u ^ (-(i : ℤ)))) : ZMod (p ^ r)) = 1
    rw [map_zpow, hu, one_zpow, Units.val_one]
  rw [padicTateTwist_ρ_apply]
  exact padicInt_smul_eq_self_of_toZModPow_eq_one p hs ha

variable (i r : ℕ) (D : Set (Subgroup (Field.absoluteGaloisGroup F)))

/-- A class killed by `p ^ r` has a locally trivial cocycle representative
whose values are killed by the same power. -/
theorem exists_powTorsion_tateSelmerRepresentative
    (x : (padicTateTwist F p i).selmerKernel D) (hx : (p : ℤ_[p]) ^ r • x = 0) :
    ∃ c : (padicTateTwist F p i).locallyTrivialCocycles₁ D,
      (Submodule.Quotient.mk c : (padicTateTwist F p i).selmerKernel D) = x ∧
      (p : ℤ_[p]) ^ r • c = 0 := by
  let A := padicTateTwist F p i
  let C := A.locallyTrivialCocycles₁ D
  let B := (coboundaries₁ A.rep).comap C.subtype
  let s : ℤ_[p] := (p : ℤ_[p]) ^ r
  have hs : s ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hmap : (Submodule.torsionBy ℤ_[p] C s).map B.mkQ =
      Submodule.torsionBy ℤ_[p] (A.selmerKernel D) s :=
    A.map_torsionBy_mkQ_eq D s (padicTateQuotient_smul_surjective s hs)
  have hx' : x ∈ Submodule.torsionBy ℤ_[p] (A.selmerKernel D) s := hx
  rw [← hmap] at hx'
  obtain ⟨c, hc, he⟩ := hx'
  exact ⟨c, he, hc⟩

/-- On the finite cyclotomic kernel a bounded Tate cocycle restricts to a
homomorphism, since the action on its values is trivial. -/
noncomputable def padicTateFiniteCocycleRestriction
    (c : (padicTateTwist F p i).locallyTrivialCocycles₁ D) (hc : (p : ℤ_[p]) ^ r • c = 0) :
    Additive (padicCyclotomicReduction F p r).ker →+ (padicTateTwist F p i).rep where
  toFun σ := c.val σ.toMul.val
  map_zero' := cocycles₁_map_one (⟨c.val, c.property.1.1⟩ : cocycles₁ (padicTateTwist F p i).rep)
  map_add' σ τ := by
    have ht : (p : ℤ_[p]) ^ r • c.val τ.toMul.val = 0 :=
      congrFun (congrArg Subtype.val hc) τ.toMul.val
    change c.val (σ.toMul.val * τ.toMul.val) = c.val σ.toMul.val + c.val τ.toMul.val
    rw [(mem_cocycles₁_iff c.val).mp c.property.1.1,
      padicTateTwist_ρ_apply_eq_self_on_powTorsion F p i r σ.toMul.property _ ht, add_comm]

theorem isLocallyConstant_padicTateFiniteCocycleRestriction
    (c : (padicTateTwist F p i).locallyTrivialCocycles₁ D) (hc : (p : ℤ_[p]) ^ r • c = 0) :
    IsLocallyConstant (fun σ => padicTateFiniteCocycleRestriction F p i r D c hc (Additive.ofMul σ)) :=
  c.property.1.2.comp_continuous continuous_subtype_val

/-- The finite-level homomorphism kills all intersections with the
specified local subgroups if the local coboundary can be taken in the
same torsion layer. -/
theorem padicTateFiniteCocycleRestriction_eq_zero_of_torsion_coboundary
    (c : (padicTateTwist F p i).locallyTrivialCocycles₁ D) (hc : (p : ℤ_[p]) ^ r • c = 0)
    (σ : (padicCyclotomicReduction F p r).ker)
    (a : (padicTateTwist F p i).rep) (ha : (p : ℤ_[p]) ^ r • a = 0)
    (hσ : c.val σ.val = (padicTateTwist F p i).rep.ρ σ.val a - a) :
    padicTateFiniteCocycleRestriction F p i r D c hc (Additive.ofMul σ) = 0 := by
  change c.val σ.val = 0
  rw [hσ, padicTateTwist_ρ_apply_eq_self_on_powTorsion F p i r σ.property a ha, sub_self]

end Utilities
