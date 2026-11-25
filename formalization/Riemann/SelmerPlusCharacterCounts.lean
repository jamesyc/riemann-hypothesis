module

public import Riemann.SelmerSignCharacterCounts
public import Riemann.SelmerHostCharacterSupport

@[expose] public section

open Utilities
open scoped BigOperators

namespace Riemann

/-- Finiteness and a bound for the sum of the rational inverse-twist
lengths at one generic prime. The lengths are normalized by base change. -/
def SelmerPlusRationalPrimeBound (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (i : ℕ) (B : ℝ) : Prop :=
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  let E := selmerHostField target e q d
  letI : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
  ∀ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O]
    [HasEnoughRootsOfUnity O (Monoid.exponent (E ≃ₐ[ℚ] E))],
    let T := selmerHostSignCharacters target e q d ℓ i O true
    let n := selmerHostRationalCharacterLength target e q d ℓ i O
    let r := Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O))
    (∀ ψ ∈ T, n ψ ≠ ⊤) ∧ (∑ ψ ∈ T, ((n ψ).toNat : ℝ) / r.toNat) ≤ B

theorem selmerPlus_hostLength_le_of_rationalPrimeBound
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (i : ℕ) (B : ℝ)
    (hodd : ℓ ≠ 2) (hdegree : ¬ ℓ ∣ Module.finrank ℚ (selmerHostField target e q d))
    (h : SelmerPlusRationalPrimeBound target e q d ℓ hℓ i B) :
    let L := numberFieldSelmerSignLengths true (selmerHostField target e q d) ℓ i
    L ≠ ⊤ ∧ ((L.untopD 0 : ℕ) : ℝ) ≤ B := by
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let E := selmerHostField target e q d
  let : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
  let n := Monoid.exponent (E ≃ₐ[ℚ] E)
  let : NeZero n := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨O, hDVR, hfin, hroots⟩ := exists_padicSplittingCoefficients ℓ n
  let : IsDiscreteValuationRing O := hDVR
  let : Module.Finite ℤ_[ℓ] O := hfin
  let : HasEnoughRootsOfUnity O (Monoid.exponent (E ≃ₐ[ℚ] E)) := hroots
  let : FaithfulSMul ℤ_[ℓ] O := (faithfulSMul_iff_algebraMap_injective ℤ_[ℓ] O).mpr
    (padicSubalgebra_algebraMap_injective ℓ O)
  let : IsLocalHom (algebraMap ℤ_[ℓ] O) := Algebra.IsIntegral.isLocalHom ℤ_[ℓ] O
  obtain ⟨r, hr, hrlen⟩ := exists_padicBaseChangeLength ℓ O (padicSubalgebra_algebraMap_injective ℓ O)
  obtain ⟨hfinite, hsum⟩ := h O
  rw [hrlen, ENat.toNat_natCast] at hsum
  obtain ⟨hf, hb⟩ := selmerHostSignLength_le_characterSum target e q d ℓ i O true hodd hdegree hr hrlen
    hfinite
  exact ⟨hf, hb.trans hsum⟩

/-- The generic-prime input of Proposition 17.14 for the rational
inverse-character groups of the host. Its budget uses the ambient modulus. -/
theorem selmerPlus_genericRationalCharacterCounts
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive) :
    ∃ (bad : Finset ℕ) (A : ℕ) (P : ℝ), 0 < P ∧
      (∀ ℓ ∈ bad, ℓ.Prime ∧ ℓ ≠ 2) ∧
      ∀ (e t : ℕ) (q d : ℕ+), 2 ≤ e → 2 ≤ t → SelmerEstimatePrimePair target q d →
        max P (2 * (t : ℝ) + 1) < (q : ℕ) → max P (2 * (t : ℝ) + 1) < (d : ℕ) →
        ∀ i ∈ Finset.Ico 1 t,
          ∃ B : ℕ → ℝ,
            (∀ ℓ : ℕ, ∀ hℓ : ℓ.Prime, ℓ ≠ 2 → ℓ ∉ bad →
              ¬ ℓ ∣ orderOf target.character → ¬ ℓ - 1 ∣ 2 * i →
              SelmerPlusRationalPrimeBound target e q d ℓ hℓ i (B ℓ)) ∧
            ∀ primes : Finset ℕ,
              (∀ ℓ ∈ primes, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∉ bad ∧
                ¬ ℓ ∣ orderOf target.character ∧ ¬ ℓ - 1 ∣ 2 * i) →
              (∑ ℓ ∈ primes, Real.log ℓ * B ℓ) ≤ ((selmerHostModulus target e q d : ℝ) * t) ^ A := by
  sorry

end Riemann
