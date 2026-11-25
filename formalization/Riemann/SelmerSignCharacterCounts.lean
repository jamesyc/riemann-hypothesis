module

public import Riemann.SelmerSharedClosure
import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

open Utilities
open scoped IsMulCommutative TensorProduct BigOperators

namespace Riemann

variable (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)

local notation "F" => selmerHostField target e q d
local notation "G" => Gal((selmerHostField target e q d)/ℚ)
local notation "c" => selmerHostConductorGalMap target e q d (-1)

local instance : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d

variable (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))

/-- The order of a host Galois character divides the host degree. -/
theorem orderOf_selmerHostGaloisCharacter_dvd_degree (ψ : G →* Oˣ) :
    orderOf ψ ∣ Module.finrank ℚ F := by
  apply orderOf_dvd_of_pow_eq_one
  apply MonoidHom.ext
  intro g
  have hg : g ^ Module.finrank ℚ F = 1 := by
    rw [← IsGalois.card_aut_eq_finrank ℚ F]
    exact pow_card_eq_one'
  rw [MonoidHom.pow_apply, ← map_pow, hg, map_one, MonoidHom.one_apply]

variable [HasEnoughRootsOfUnity O (Monoid.exponent (Gal((selmerHostField target e q d)/ℚ)))]

/-- The host characters with the conjugation eigenvalue of the selected sign. -/
noncomputable def selmerHostSignCharacters (positive : Bool) : Finset (G →* Oˣ) := by
  classical
  let : Fintype G := Fintype.ofFinite _
  let : Fintype (G →* Oˣ) := Fintype.ofEquiv G
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G O).some.toEquiv.symm
  exact Finset.univ.filter fun ψ => (ψ c : O) = selmerSignScalar positive i

theorem mem_selmerHostSignCharacters (positive : Bool) (ψ : G →* Oˣ) :
    ψ ∈ selmerHostSignCharacters target e q d ℓ i O positive ↔
      (ψ c : O) = selmerSignScalar positive i := by
  simp only [selmerHostSignCharacters, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The sign family has at most the host degree many characters. -/
theorem selmerHostSignCharacters_card_le_degree (positive : Bool) :
    (selmerHostSignCharacters target e q d ℓ i O positive).card ≤ Module.finrank ℚ F := by
  classical
  let : Fintype G := Fintype.ofFinite _
  let E := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G O).some.toEquiv
  let : Fintype (G →* Oˣ) := Fintype.ofEquiv G E.symm
  refine (Finset.card_le_univ _).trans ?_
  rw [Fintype.card_congr E, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

/-- An odd-order character of plus parity occurs only at an even twist. -/
theorem even_of_selmerHostPlusCharacter_odd_order (ψ : G →* Oˣ)
    (hψ : ψ ∈ selmerHostSignCharacters target e q d ℓ i O true)
    (horder : Odd (orderOf ψ)) : Even i := by
  by_contra hn
  have hi : Odd i := Nat.not_even_iff_odd.mp hn
  have hsign : (ψ c : O) = -1 := by
    have h := (mem_selmerHostSignCharacters target e q d ℓ i O true ψ).mp hψ
    simpa [selmerSignScalar, hi.neg_one_pow] using h
  have hpow := congrArg (fun ϕ : G →* Oˣ => (ϕ c : O)) (pow_orderOf_eq_one ψ)
  simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one,
    hsign, horder.neg_one_pow] at hpow
  exact (by norm_num : (-1 : O) ≠ 1) hpow

/-- Length of the actual inverse-character Selmer group over the rational base. -/
noncomputable def selmerHostRationalCharacterLength (ψ : G →* Oˣ) : ℕ∞ :=
  Module.length O ((numberFieldSelmerSharedInverseTwist F ℓ i O ψ).selmerKernel
    (numberFieldSelmerRestrictionsIn ℚ (AlgebraicClosure F) ℓ))

set_option maxHeartbeats 1200000 in
/-- The base change of a sign part has the sum of its matching
character-eigenspace lengths. -/
theorem selmerHostSignBaseChangeLength_eq_eigenspaceSum
    (positive : Bool) (hodd : ℓ ≠ 2) (hdegree : ¬ ℓ ∣ Module.finrank ℚ F) :
    Module.length O (O ⊗[ℤ_[ℓ]] numberFieldSelmerSignPart positive F ℓ i) =
      ∑ ψ ∈ selmerHostSignCharacters target e q d ℓ i O positive,
        Module.length O (characterEigenspace (numberFieldSelmerSignBaseChangeAction F ℓ i O positive) ψ) := by
  classical
  let : Fintype G := Fintype.ofFinite _
  let : Fintype (G →* Oˣ) := Fintype.ofEquiv G
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G O).some.toEquiv.symm
  let M := numberFieldSelmerSignPart positive F ℓ i
  let ρ := numberFieldSelmerSignBaseChangeAction F ℓ i O positive
  let T := selmerHostSignCharacters target e q d ℓ i O positive
  let s : O := selmerSignScalar positive i
  have hunit (n : ℕ) (hn : ¬ ℓ ∣ n) : IsUnit (n : O) := by
    rw [← map_natCast (algebraMap ℤ_[ℓ] O)]
    exact (PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Fact.out : ℓ.Prime).coprime_iff_not_dvd.mpr hn))).map _
  have hcard : Fintype.card G = Module.finrank ℚ F := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  have horder : IsUnit (Fintype.card G : O) := hunit _ (by rw [hcard]; exact hdegree)
  have htwo : IsUnit (2 : O) := hunit 2
    (fun h => hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h))
  have hs : s ^ 2 = 1 := by
    have hs' : ((-1 : O) ^ i) ^ 2 = 1 := by rw [pow_right_comm]; simp
    cases positive <;> simpa [s, selmerSignScalar] using hs'
  have hc : c ^ 2 = 1 := by simp [← map_pow]
  have hρ : ρ c = s • 1 := by
    let : IsAlgClosure ℚ (AlgebraicClosure F) := IsAlgClosure.ofAlgebraic ℚ F _
    let a : AlgebraicClosure F →ₐ[ℚ] ℂ := IsAlgClosed.lift
    have he := selmerHostConductorGalMap_neg_one_eq_conjugation target e q d (a.domRestrict F)
    exact (congrArg ρ he).trans (numberFieldSelmerSignBaseChangeAction_complexConj F ℓ i O positive)
  have hT : T = Finset.univ.filter (fun ψ : G →* Oˣ => (ψ c : O) = s) := by
    apply Finset.ext
    intro ψ
    exact (mem_selmerHostSignCharacters target e q d ℓ i O positive ψ).trans
      (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl)
  let w (ψ : G →* Oˣ) := Module.length O (characterEigenspace ρ ψ)
  change Module.length O (O ⊗[ℤ_[ℓ]] M) = ∑ ψ ∈ T, w ψ
  calc
    _ = ∑ ψ : G →* Oˣ, if (ψ c : O) = s then w ψ else 0 := by
      refine (length_eq_sum_characterEigenspace_of_scalar_involution ρ horder htwo c hc s hs hρ).trans ?_
      refine Finset.sum_congr rfl fun ψ _ => ?_
      by_cases h : (ψ c : O) = s <;> simp [h, w]
    _ = ∑ ψ ∈ Finset.univ.filter (fun ψ : G →* Oˣ => (ψ c : O) = s), w ψ :=
      (Finset.sum_filter _ _).symm
    _ = _ := congrArg (fun S : Finset (G →* Oˣ) => ∑ ψ ∈ S, w ψ) hT.symm

/-- The selected sign component, after base change, is bounded by the sum
of the rational inverse-twist lengths of matching parity. -/
theorem selmerHostSignLength_scaled_le_characterSum
    [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O] (positive : Bool)
    (hodd : ℓ ≠ 2) (hdegree : ¬ ℓ ∣ Module.finrank ℚ F) {r : ℕ}
    (hrlen : Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map
      (algebraMap ℤ_[ℓ] O)) = r) :
    Module.length ℤ_[ℓ] (numberFieldSelmerSignPart positive F ℓ i) * (r : ℕ∞) ≤
      ∑ ψ ∈ selmerHostSignCharacters target e q d ℓ i O positive,
        selmerHostRationalCharacterLength target e q d ℓ i O ψ := by
  let : FaithfulSMul ℤ_[ℓ] O :=
    (faithfulSMul_iff_algebraMap_injective ℤ_[ℓ] O).mpr (padicSubalgebra_algebraMap_injective ℓ O)
  let : Module.Free ℤ_[ℓ] O := inferInstance
  let : IsLocalHom (algebraMap ℤ_[ℓ] O) := Algebra.IsIntegral.isLocalHom ℤ_[ℓ] O
  let M := numberFieldSelmerSignPart positive F ℓ i
  let T := selmerHostSignCharacters target e q d ℓ i O positive
  let ρ := numberFieldSelmerSignBaseChangeAction F ℓ i O positive
  calc
    _ = Module.length O (O ⊗[ℤ_[ℓ]] M) :=
      (congrArg (fun n : ℕ∞ => Module.length ℤ_[ℓ] M * n) hrlen.symm).trans
        (IsLocalRing.length_baseChange ℤ_[ℓ] O (↥M)).symm
    _ = ∑ ψ ∈ T, Module.length O (characterEigenspace ρ ψ) :=
      selmerHostSignBaseChangeLength_eq_eigenspaceSum target e q d ℓ i O positive hodd hdegree
    _ ≤ _ := Finset.sum_le_sum fun ψ _ =>
      numberFieldSelmerSignCharacterLength_le_sharedTwist F ℓ i O positive hdegree ψ

/-- When the matching rational twist groups have finite length, the sign
part has finite length and is bounded by their normalized sum. -/
theorem selmerHostSignLength_le_characterSum
    [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O] (positive : Bool)
    (hodd : ℓ ≠ 2) (hdegree : ¬ ℓ ∣ Module.finrank ℚ F) {r : ℕ} (hr : 0 < r)
    (hrlen : Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map
      (algebraMap ℤ_[ℓ] O)) = r)
    (hfinite : ∀ ψ ∈ selmerHostSignCharacters target e q d ℓ i O positive,
      selmerHostRationalCharacterLength target e q d ℓ i O ψ ≠ ⊤) :
    let n := numberFieldSelmerSignLengths positive F ℓ i
    n ≠ ⊤ ∧ (ENat.toNat n : ℝ) ≤
      ∑ ψ ∈ selmerHostSignCharacters target e q d ℓ i O positive,
        ((selmerHostRationalCharacterLength target e q d ℓ i O ψ).toNat : ℝ) / r := by
  let n : ℕ∞ := numberFieldSelmerSignLengths positive F ℓ i
  let T := selmerHostSignCharacters target e q d ℓ i O positive
  let m := selmerHostRationalCharacterLength target e q d ℓ i O
  have h : n * (r : ℕ∞) ≤ ∑ ψ ∈ T, m ψ := by
    exact (congrArg (fun z : ℕ∞ => z * (r : ℕ∞))
      (numberFieldSelmerSignLengths_eq_moduleLength positive F ℓ i)).le.trans
        (selmerHostSignLength_scaled_le_characterSum target e q d ℓ i O positive hodd hdegree hrlen)
  have hr₀ : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  obtain ⟨hf, hb⟩ := length_log_bound_of_scaled_sum T n hr m
    (fun ψ => ((m ψ).toNat : ℝ) / r) 1 zero_le_one h
      (fun ψ hψ => ⟨hfinite ψ hψ, by rw [mul_one, mul_div_cancel₀ _ hr₀]⟩)
  rw [mul_one] at hb
  exact ⟨hf, hb⟩

end Riemann
