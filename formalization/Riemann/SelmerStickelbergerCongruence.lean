module

public import Riemann.SelmerStickelbergerNorm
public import Utilities.HigherStickelbergerCongruence
public import Utilities.PadicCyclotomicRestriction
import Utilities.PadicTateTorsion
import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section

open Utilities
open scoped IsMulCommutative

namespace Riemann

/-- The integral twisted weight-one element at level `f * ℓ * ℓ ^ m`,
projected to the host Galois group. -/
noncomputable def selmerTwistedWeightOneStickelberger (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ℓ i m : ℕ) [Fact ℓ.Prime] :
    MonoidAlgebra ℤ (selmerHostField target e q d ≃ₐ[ℚ] selmerHostField target e q d) := by
  let f := selmerHostConductor target e q d
  let N := f * ℓ
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let _ : NeZero N := ⟨mul_ne_zero (selmerHostConductor_pos target e q d).ne' (NeZero.ne ℓ)⟩
  have hℓN : ℓ ∣ N := dvd_mul_left _ _
  let a := 2 * N + 1
  have ha : a.Coprime N := by simp [a]
  exact twistedWeightOneStickelberger
    ((selmerStickelbergerGalMap target e q d ℓ).comp (ZMod.unitsMap (dvd_mul_right N (ℓ ^ m))))
    i a (ha.mul_right ((ha.coprime_dvd_right hℓN).pow_right m))

/-- On each host Selmer class, the action of the finite-level twisted
weight-one element eventually equals the action of the higher element. -/
theorem selmerTwistedWeightOneStickelberger_eventually_acts_eq (target : BundledDirichletCharacter)
    (e : ℕ) (q d : ℕ+) (ℓ i : ℕ) [Fact ℓ.Prime] (hodd : ℓ ≠ 2) :
    let E := selmerHostField target e q d
    letI := selmerHostField_isAbelianGalois target e q d
    let ρ := Representation.asAlgebraHom (numberFieldSelmerGaloisAction E ℓ i)
    ∀ x : (padicTateTwist E ℓ i).selmerKernel (numberFieldSelmerRestrictions E ℓ),
      ∃ m₀ : ℕ, ∀ m ≥ m₀,
        ρ (MonoidAlgebra.mapRingHom (E ≃ₐ[ℚ] E) (Int.castRingHom ℤ_[ℓ])
          (selmerTwistedWeightOneStickelberger target e q d ℓ i m)) x =
        ρ (selmerPadicHigherStickelberger target e q d ℓ i hodd) x := by
  intro E ρ x
  let _ : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
  let _ : CompactSpace (Field.absoluteGaloisGroup E) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure E/E))
  obtain ⟨r, hkill⟩ := exists_pow_smul_eq_zero_padicTateSelmerKernel E ℓ i
    (numberFieldSelmerRestrictions E ℓ) x
  refine ⟨r + multiplicity ℓ (i + 1) + 1, fun m hm => ?_⟩
  let N := selmerHostConductor target e q d * ℓ
  let _ : NeZero N := ⟨mul_ne_zero (selmerHostConductor_pos target e q d).ne'
    (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨v, hv⟩ := exists_twistedWeightOne_eq_padicHigherStickelberger_add_pow_smul
    (N := N) ℓ hodd (dvd_mul_left _ _) (selmerStickelbergerGalMap target e q d ℓ) i r m hm
  have hcongruence : MonoidAlgebra.mapRingHom (E ≃ₐ[ℚ] E) (Int.castRingHom ℤ_[ℓ])
      (selmerTwistedWeightOneStickelberger target e q d ℓ i m) =
      selmerPadicHigherStickelberger target e q d ℓ i hodd + (ℓ : ℤ_[ℓ]) ^ r • v := hv
  exact algHom_end_apply_eq_of_eq_add_smul ρ hcongruence hkill

/-- The finite-level arithmetic input. For arbitrarily high levels the
twisted weight-one action vanishes on the specified cyclotomic restrictions. -/
def HasSelmerTwistedWeightOneRestrictionVanishing : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i : ℕ, 1 ≤ i →
      let E := selmerHostField target e q d
      letI := selmerHostField_isAbelianGalois target e q d
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ℓ ∣ Module.finrank ℚ E →
        let N := selmerHostConductor target e q d * ℓ
        let ρ := Representation.asAlgebraHom (numberFieldSelmerGaloisAction E ℓ i)
        ∀ (x : numberFieldSelmerMinusPart E ℓ i) (m₀ : ℕ), ∃ m ≥ m₀,
          ∀ σ : padicCyclotomicKernel E ℓ,
            (∀ ζ : AlgebraicClosure E, ζ ^ N = 1 →
              (show Gal(AlgebraicClosure E/E) from σ.val) ζ = ζ) →
            padicTateSelmerRestriction E ℓ i (numberFieldSelmerRestrictions E ℓ)
              (ρ (MonoidAlgebra.mapRingHom (E ≃ₐ[ℚ] E) (Int.castRingHom ℤ_[ℓ])
                (selmerTwistedWeightOneStickelberger target e q d ℓ i m)) x.val) σ = 0

/-- The finite-level vanishing implies annihilation by the integral higher
element after multiplication by the totient of the base level. -/
theorem selmerHigherStickelbergerAnnihilation_of_twistedWeightOneRestriction
    (h : HasSelmerTwistedWeightOneRestrictionVanishing) : HasSelmerHigherStickelbergerAnnihilation := by
  apply selmerHigherStickelbergerAnnihilation_of_padicLift
  intro target ht e q d he hpair i hi
  dsimp only
  intro ℓ _ hodd hdiv x
  let E := selmerHostField target e q d
  let _ : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
  let N := selmerHostConductor target e q d * ℓ
  have hN : 1 < N := (Fact.out : ℓ.Prime).one_lt.trans_le
    (Nat.le_mul_of_pos_left ℓ (selmerHostConductor_pos target e q d))
  let _ : NeZero N := ⟨(Nat.zero_lt_of_lt hN).ne'⟩
  let ρ := Representation.asAlgebraHom (numberFieldSelmerGaloisAction E ℓ i)
  let w := selmerPadicHigherStickelberger target e q d ℓ i hodd
  obtain ⟨m₀, hact⟩ := selmerTwistedWeightOneStickelberger_eventually_acts_eq target e q d ℓ i hodd x.val
  obtain ⟨m, hm, hz⟩ := h target ht e q d he hpair i hi ℓ hodd hdiv x m₀
  have hzero : N.totient • ρ w x.val = 0 :=
    totient_smul_selmerClass_eq_zero_of_restriction_eq_zero E ℓ hodd i hi N hN
      (numberFieldSelmerRestrictions E ℓ) _ (fun σ hfix =>
        (congrArg (fun y => padicTateSelmerRestriction E ℓ i (numberFieldSelmerRestrictions E ℓ) y σ)
          (hact m hm)).symm.trans (hz σ hfix))
  exact (map_nsmul (ρ w) N.totient x.val).trans hzero

end Riemann
