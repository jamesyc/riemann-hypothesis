module

public import Riemann.SelmerExceptionalBounds
public import Riemann.SelmerGaloisAction
public import Utilities.CharacterEigenspaceLength
public import Utilities.PadicSplittingCoefficients
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

open Utilities
open scoped IsMulCommutative TensorProduct

namespace Riemann

section SignAction

variable (F : Type) [Field F] [NumberField F] [IsAbelianGalois ℚ F]
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)

local instance : IsAlgClosure ℚ (AlgebraicClosure F) := IsAlgClosure.ofAlgebraic ℚ F _

local notation "ι" => (IsAlgClosed.lift : AlgebraicClosure F →ₐ[ℚ] ℂ)
local notation "ρ" => numberFieldSelmerGaloisAction F ℓ i
local notation "c" => algEquiv_complexConjugation F (AlgHom.domRestrict F ι)

/-- The action of the abelian host Galois group on either sign part. -/
noncomputable def numberFieldSelmerSignGaloisAction (positive : Bool) :
    (F ≃ₐ[ℚ] F) →* Module.End ℤ_[ℓ] (numberFieldSelmerSignPart positive F ℓ i) :=
  Representation.subrepresentation ρ (numberFieldSelmerSignPart positive F ℓ i) (by
    intro g x hx
    have hc := numberFieldSelmerGaloisAction_complexConjugation F ℓ i ι
    have hcomm : ρ c * ρ g = ρ g * ρ c := (Commute.all c g).map ρ
    change ρ g x ∈ (numberFieldSelmerConjugation F ℓ i ι).eigenspace _
    apply Module.End.mem_eigenspace_iff.mpr
    rw [← hc, ← mul_apply_eq_comp, hcomm, mul_apply_eq_comp, hc,
      Module.End.mem_eigenspace_iff.mp hx, map_smul])

theorem numberFieldSelmerSignGaloisAction_complexConj (positive : Bool) :
    numberFieldSelmerSignGaloisAction F ℓ i positive c =
      (selmerSignScalar positive i : ℤ_[ℓ]) • 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ρ c x.val = (selmerSignScalar positive i : ℤ_[ℓ]) • x.val
  rw [numberFieldSelmerGaloisAction_complexConjugation F ℓ i ι]
  exact Module.End.mem_eigenspace_iff.mp x.property

noncomputable abbrev numberFieldSelmerMinusGaloisAction :=
  numberFieldSelmerSignGaloisAction F ℓ i false

theorem numberFieldSelmerMinusGaloisAction_complexConj :
    numberFieldSelmerMinusGaloisAction F ℓ i c = ((-1 : ℤ_[ℓ]) ^ (i + 1)) • 1 := by
  simpa [selmerSignScalar, pow_succ, mul_neg_one]
    using numberFieldSelmerSignGaloisAction_complexConj F ℓ i false

variable (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]

/-- Extend the selected sign representation to a coefficient ring. -/
noncomputable def numberFieldSelmerSignBaseChangeAction (positive : Bool) :
    (F ≃ₐ[ℚ] F) →* Module.End O (O ⊗[ℤ_[ℓ]] numberFieldSelmerSignPart positive F ℓ i) :=
  (Module.End.baseChangeHom ℤ_[ℓ] O (↥(numberFieldSelmerSignPart positive F ℓ i))).toMonoidHom.comp
    (numberFieldSelmerSignGaloisAction F ℓ i positive)

theorem numberFieldSelmerSignBaseChangeAction_complexConj (positive : Bool) :
    numberFieldSelmerSignBaseChangeAction F ℓ i O positive c = (selmerSignScalar positive i : O) • 1 := by
  change (Module.End.baseChangeHom ℤ_[ℓ] O (↥(numberFieldSelmerSignPart positive F ℓ i)))
    (numberFieldSelmerSignGaloisAction F ℓ i positive c) = _
  rw [numberFieldSelmerSignGaloisAction_complexConj, map_smul, map_one]
  rw [← IsScalarTower.algebraMap_smul O (selmerSignScalar positive i : ℤ_[ℓ])
    (1 : Module.End O (O ⊗[ℤ_[ℓ]] numberFieldSelmerSignPart positive F ℓ i))]
  rw [map_selmerSignScalar]

noncomputable abbrev numberFieldSelmerMinusBaseChangeAction :=
  numberFieldSelmerSignBaseChangeAction F ℓ i O false

theorem numberFieldSelmerMinusBaseChangeAction_complexConj :
    numberFieldSelmerMinusBaseChangeAction F ℓ i O c = ((-1 : O) ^ (i + 1)) • 1 := by
  simpa [selmerSignScalar, pow_succ, mul_neg_one]
    using numberFieldSelmerSignBaseChangeAction_complexConj F ℓ i O false

end SignAction

section Bernoulli

variable (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (O : Type) [CommRing O] [IsDomain O]
  [IsLocalRing O] [Algebra ℤ_[ℓ] O] [IsLocalHom (algebraMap ℤ_[ℓ] O)] [Module.Flat ℤ_[ℓ] O]

local notation "F" => selmerHostField target e q d
local notation "G" => (F ≃ₐ[ℚ] F)
local notation "f" => selmerHostConductor target e q d
local notation "π" => selmerHostConductorGalMap target e q d

local instance : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
noncomputable local instance : Fintype G := Fintype.ofFinite _
local notation "M" => numberFieldSelmerMinusPart F ℓ i

/-- The Dirichlet character attached to a coefficient-valued host character. -/
noncomputable def selmerDirichletOfCharacter (j : O →+* PadicAlgCl ℓ) (ψ : G →* Oˣ) :
    DirichletCharacter (PadicAlgCl ℓ) f :=
  MulChar.ofUnitHom ((Units.map j.toMonoidHom).comp (ψ.comp π))

set_option maxHeartbeats 900000 in
/-- A comparison on each character summand of the scalar-extended minus
part gives the local inequality used in the common Bernoulli product. -/
theorem selmerBernoulliComparison_atPrime_of_characterLengths
    [HasEnoughRootsOfUnity O (Monoid.exponent G)] (hodd : ℓ ≠ 2)
    (hdegree : ¬ ℓ ∣ Module.finrank ℚ F) (j : O →+* PadicAlgCl ℓ) (hj : Function.Injective j)
    {r : ℕ} (hr : 0 < r)
    (hrlen : Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O)) = r)
    (h : ∀ ψ : G →* Oˣ, (ψ (π (-1)) : O) = (-1 : O) ^ (i + 1) →
      let n := Module.length O (characterEigenspace (numberFieldSelmerMinusBaseChangeAction F ℓ i O) ψ)
      n ≠ ⊤ ∧ (ENat.toNat n : ℝ) * Real.log ℓ ≤ (r : ℝ) *
        (-Real.log ‖(generalizedBernoulliDenominator f (i + 1) : PadicAlgCl ℓ) *
          primitiveBernoulliValue (i + 1) (selmerDirichletOfCharacter target e q d ℓ O j ψ)‖)) :
    let n := numberFieldSelmerSignLengths false F ℓ i
    n ≠ ⊤ ∧ ∃ T : Finset (DirichletCharacter (PadicAlgCl ℓ) f),
      (∀ χ ∈ T, χ ∈ dirichletCharactersWithKernelIn (PadicAlgCl ℓ)
        (selmerMinusBernoulliKernels target e q d i)) ∧
      Real.log (ℓ : ℝ) * (ENat.toNat n : ℝ) ≤
        ∑ χ ∈ T, -Real.log ‖(generalizedBernoulliDenominator f (i + 1) : PadicAlgCl ℓ) *
          primitiveBernoulliValue (i + 1) χ‖ := by
  classical
  let _ : Fintype (G →* Oˣ) := Fintype.ofEquiv G
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G O).some.toEquiv.symm
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  let s := (-1 : O) ^ (i + 1)
  let c := π (-1)
  let ρ := numberFieldSelmerMinusBaseChangeAction F ℓ i O
  let T := Finset.univ.filter fun ψ : G →* Oˣ => (ψ c : O) = s
  let χ := selmerDirichletOfCharacter target e q d ℓ O j
  let B (χ : DirichletCharacter (PadicAlgCl ℓ) f) :=
    -Real.log ‖(generalizedBernoulliDenominator f (i + 1) : PadicAlgCl ℓ) *
      primitiveBernoulliValue (i + 1) χ‖
  let n (ψ : G →* Oˣ) := Module.length O (characterEigenspace ρ ψ)
  have hcard : Fintype.card G = Module.finrank ℚ F := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  have hunit (k : ℕ) (hk : ¬ ℓ ∣ k) : IsUnit (k : O) := by
    rw [← map_natCast (algebraMap ℤ_[ℓ] O)]
    exact (PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Fact.out : ℓ.Prime).coprime_iff_not_dvd.mpr hk))).map _
  have hs : s ^ 2 = 1 := by
    dsimp [s]
    rw [pow_right_comm]
    simp
  have hc : c ^ 2 = 1 := by simp [c, ← map_pow]
  have hρ : ρ c = s • 1 := by
    let _ : IsAlgClosure ℚ (AlgebraicClosure F) := IsAlgClosure.ofAlgebraic ℚ F _
    let a : AlgebraicClosure F →ₐ[ℚ] ℂ := IsAlgClosed.lift
    have hc' : c = algEquiv_complexConjugation F (a.domRestrict F) :=
      selmerHostConductorGalMap_neg_one_eq_conjugation target e q d (a.domRestrict F)
    exact (congrArg ρ hc').trans (numberFieldSelmerMinusBaseChangeAction_complexConj F ℓ i O)
  have horder : IsUnit (Fintype.card G : O) := hunit _ (by rw [hcard]; exact hdegree)
  have htwo : IsUnit (2 : O) := by
    have hp : IsUnit (2 : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr
      ((PadicInt.norm_natCast_eq_one_iff (n := 2)).mpr
        ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hodd))
    simpa only [map_ofNat] using hp.map (algebraMap ℤ_[ℓ] O)
  have hsum : Module.length O (O ⊗[ℤ_[ℓ]] M) = ∑ ψ ∈ T, n ψ := by
    rw [length_eq_sum_characterEigenspace_of_scalar_involution ρ horder htwo c hc s hs hρ]
    rw [Finset.sum_filter]
  have hmul : Module.length ℤ_[ℓ] M * (r : ℕ∞) ≤ ∑ ψ ∈ T, n ψ := by
    rw [← hsum, IsLocalRing.length_baseChange, hrlen]
  have hlog : 0 ≤ Real.log (ℓ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le)
  obtain ⟨hfinite, hlen⟩ := length_log_bound_of_scaled_sum T _ hr n (B ∘ χ) _ hlog hmul
    (fun ψ hψ => h ψ (Finset.mem_filter.mp hψ).2)
  have hχeval (ψ : G →* Oˣ) (u : (ZMod f)ˣ) :
      χ ψ u = j (ψ (π u) : O) := by
    simp [χ, selmerDirichletOfCharacter]
  have hinj : Function.Injective χ := by
    intro ψ θ hψ
    apply MonoidHom.ext
    intro g
    obtain ⟨u, rfl⟩ := selmerHostConductorGalMap_surjective target e q d g
    have he : χ ψ u = χ θ u := congrArg (fun k : DirichletCharacter _ _ => k u) hψ
    exact Units.ext (hj ((hχeval ψ u).symm.trans (he.trans (hχeval θ u))))
  rw [numberFieldSelmerSignLengths_false_eq_moduleLength F ℓ i]
  refine ⟨hfinite, T.image χ, ?_, ?_⟩
  · intro k hk
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hk
    change (χ ψ).toUnitHom.ker ∈ selmerMinusBernoulliKernels target e q d i
    refine ⟨?_, ?_⟩
    · intro u hu
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      rw [MulChar.coe_toUnitHom, hχeval, MonoidHom.mem_ker.mp hu, map_one, Units.val_one, map_one]
      rfl
    · have hsign : χ ψ (↑(-1 : (ZMod f)ˣ)) = (-1 : PadicAlgCl ℓ) ^ (i + 1) := by
        rw [hχeval, (Finset.mem_filter.mp hψ).2]
        simp [s]
      rw [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one, hsign]
      exact neg_one_pow_eq_one_iff_even (by norm_num)
  · rw [Finset.sum_image (fun _ _ _ _ hEq => hinj hEq)]
    change Real.log (ℓ : ℝ) * _ ≤ ∑ ψ ∈ T, (B ∘ χ) ψ
    rwa [mul_comm (Real.log (ℓ : ℝ))]

end Bernoulli

/-- The remaining prime-to-degree comparison on one character eigenspace
over a finite splitting coefficient ring. -/
def HasSelmerBernoulliCharacterLengthComparison : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i ≥ 1,
      let F := selmerHostField target e q d
      letI : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
      let f := selmerHostConductor target e q d
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ¬ ℓ ∣ Module.finrank ℚ F →
        ∀ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))
          [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O]
          [HasEnoughRootsOfUnity O (Monoid.exponent (F ≃ₐ[ℚ] F))],
          ∀ ψ : (F ≃ₐ[ℚ] F) →* Oˣ,
            (ψ (selmerHostConductorGalMap target e q d (-1)) : O) = (-1 : O) ^ (i + 1) →
            let ρ := numberFieldSelmerMinusBaseChangeAction F ℓ i O
            let n := Module.length O (characterEigenspace ρ ψ)
            let r := Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O))
            n ≠ ⊤ ∧ (ENat.toNat n : ℝ) * Real.log ℓ ≤ (ENat.toNat r : ℝ) *
              (-Real.log ‖(generalizedBernoulliDenominator f (i + 1) : PadicAlgCl ℓ) *
                primitiveBernoulliValue (i + 1)
                  (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ)‖)

set_option maxHeartbeats 750000 in
/-- Summing the per-character estimates gives the comparison for the full
minus Selmer part at every prime not dividing the host degree. -/
theorem selmerBernoulliValuationComparison_of_characterLengths
    (h : HasSelmerBernoulliCharacterLengthComparison) : HasSelmerBernoulliValuationComparison := by
  intro target ht e q d he hpair i hi
  dsimp only
  intro ℓ _ hodd hdegree
  let F := selmerHostField target e q d
  let G := (F ≃ₐ[ℚ] F)
  let n := Monoid.exponent G
  let _ : NeZero n := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨O, hDVR, hfin, hroots⟩ := exists_padicSplittingCoefficients ℓ n
  let _ : IsDiscreteValuationRing O := hDVR
  let _ : Module.Finite ℤ_[ℓ] O := hfin
  let _ : HasEnoughRootsOfUnity O n := hroots
  have hinj := padicSubalgebra_algebraMap_injective ℓ O
  let _ : FaithfulSMul ℤ_[ℓ] O :=
    (faithfulSMul_iff_algebraMap_injective ℤ_[ℓ] O).mpr hinj
  let _ : IsLocalHom (algebraMap ℤ_[ℓ] O) := Algebra.IsIntegral.isLocalHom ℤ_[ℓ] O
  let _ : Module.Flat ℤ_[ℓ] O := inferInstance
  obtain ⟨r, hr, hrlen⟩ := exists_padicBaseChangeLength ℓ O hinj
  refine selmerBernoulliComparison_atPrime_of_characterLengths target e q d ℓ i O hodd hdegree
    O.val.toRingHom Subtype.val_injective hr hrlen ?_
  intro ψ hψ
  have hbound := h target ht e q d he hpair i hi ℓ hodd hdegree O ψ hψ
  dsimp only at hbound
  simpa only [hrlen, ENat.toNat_natCast] using hbound

end Riemann
