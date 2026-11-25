module

public import Riemann.SelmerResidualCyclotomic
public import Riemann.SelmerTwistLocalWitness
import Utilities.RationalCyclotomicInertia
import Utilities.RationalPrime
import Utilities.AbsoluteCyclotomicInertia
import Utilities.PadicTateFiniteRestriction
import Utilities.PadicProductBound
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

open NumberField Utilities DiscreteGaloisModule
open scoped NumberField TensorProduct

namespace Riemann

section SharedTwist

variable (F : Type) [Field F] [NumberField F] [IsAbelianGalois ℚ F]
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S]
  (ψ : Gal(F/ℚ) →* Sˣ)

local notation "Ω" => AlgebraicClosure F
local notation "G" => Gal(Ω/ℚ)
local notation "T" => numberFieldSelmerSharedInverseTwist F ℓ i S ψ
local notation "D" => numberFieldSelmerRestrictionsIn ℚ Ω ℓ
local instance : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω

/-- Difference between the inverse twist scalar and the cyclotomic scalar. -/
noncomputable def sharedTwistCyclotomicDifference (g : G) : S :=
  ((((ψ (g.restrictNormal F))⁻¹ : Sˣ) : S) *
    algebraMap ℤ_[ℓ] S (padicTateScalarIn ℚ Ω ℓ i g)) -
    algebraMap ℤ_[ℓ] S (cyclotomicCharacter Ω ℓ g.toRingEquiv).val

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- The inverse-twist Selmer kernel vanishes when its scalar action is
residually cyclotomic and the host degree is prime to the odd Tate prime. -/
theorem sharedTwist_selmerKernel_subsingleton_of_residualCyclotomic
    [IsDomain S] [CharZero S] [IsDiscreteValuationRing S] [Module.Finite ℤ_[ℓ] S]
    (hodd : ℓ ≠ 2) (hdegree : ¬ ℓ ∣ Module.finrank ℚ F)
    (hres : ∀ g : G, ¬ IsUnit (sharedTwistCyclotomicDifference F ℓ i S ψ g)) :
    Subsingleton ((T).selmerKernel D) := by
  have hprime : ℓ.Prime := Fact.out
  let α (g : G) : S :=
    ((((ψ (g.restrictNormal F))⁻¹ : Sˣ) : S) *
      algebraMap ℤ_[ℓ] S (padicTateScalarIn ℚ Ω ℓ i g))
  let ε (g : G) : ℤ_[ℓ] := (cyclotomicCharacter Ω ℓ g.toRingEquiv).val
  let n (g : G) := (PadicInt.toZModPow 1 (ε g)).val
  let η (g : G) : ZMod ℓ := n g
  have hηval (g : G) : (η g).val = n g :=
    ZMod.val_natCast_of_lt (by simpa only [pow_one] using ZMod.val_lt (PadicInt.toZModPow 1 (ε g)))
  have hηact (g : G) (z : Ω) (hz : z ^ ℓ = 1) : g z = z ^ (η g).val := by
    rw [hηval]
    exact cyclotomicCharacter.spec ℓ g.toRingEquiv z (by simpa only [pow_one] using hz)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hmax (x : S) : x ∈ IsLocalRing.maximalIdeal S ↔ π ∣ x := by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  have hπℓ : π ∣ (ℓ : S) := by
    apply (hmax _).mp
    have hcomap : (IsLocalRing.maximalIdeal S).comap (algebraMap ℤ_[ℓ] S) =
        IsLocalRing.maximalIdeal ℤ_[ℓ] :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[ℓ])
        (IsLocalRing.maximalIdeal S))
    have hm : (ℓ : ℤ_[ℓ]) ∈ (IsLocalRing.maximalIdeal S).comap (algebraMap ℤ_[ℓ] S) := by
      rw [hcomap, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    change algebraMap ℤ_[ℓ] S (ℓ : ℤ_[ℓ]) ∈ IsLocalRing.maximalIdeal S at hm
    simpa only [map_natCast] using hm
  have hαn (g : G) : π ∣ α g - (n g : S) := by
    have h₁ : π ∣ α g - algebraMap ℤ_[ℓ] S (ε g) :=
      (hmax _).mp ((IsLocalRing.mem_maximalIdeal _).mpr (hres g))
    have hker : ε g - (n g : ℤ_[ℓ]) ∈ RingHom.ker (PadicInt.toZModPow (p := ℓ) 1) := by
      rw [RingHom.mem_ker, map_sub, map_natCast]
      change PadicInt.toZModPow 1 (ε g) - ((PadicInt.toZModPow 1 (ε g)).val : ZMod (ℓ ^ 1)) = 0
      rw [ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at hker
    have h₂ : π ∣ algebraMap ℤ_[ℓ] S (ε g) - (n g : S) := by
      have h := map_dvd (algebraMap ℤ_[ℓ] S) hker
      rw [map_sub, map_natCast, map_natCast] at h
      exact hπℓ.trans h
    simpa only [sub_add_sub_cancel] using dvd_add h₁ h₂
  have htors (x : (T).rep) : ∃ r : ℕ, π ^ r • x = 0 := by
    obtain ⟨r, hr⟩ := exists_pow_smul_eq_zero_extendedPadicTate ℓ S x
    obtain ⟨d, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (Nat.cast_ne_zero.mpr hprime.ne_zero : (ℓ : S) ≠ 0) hπ
    change (ℓ : S) ^ r • x = 0 at hr
    rw [hu, mul_pow, ← pow_mul, mul_smul] at hr
    exact ⟨d * r, (u.isUnit.pow r).smul_eq_zero.mp hr⟩
  have hρ (g : G) (x : (T).rep) (hx : π • x = 0) :
      (T).rep.ρ g x = (η g).val • x := by
    obtain ⟨b, hb⟩ := hαn g
    have he : (α g - (n g : S)) • x = 0 := by rw [hb, mul_comm, mul_smul, hx, smul_zero]
    rw [numberFieldSelmerSharedInverseTwist_ρ F ℓ i S ψ g, LinearMap.smul_apply, one_apply_eq_self,
      hηval, ← Nat.cast_smul_eq_nsmul S]
    exact sub_eq_zero.mp (by simpa only [sub_smul] using he)
  have haway (P : Ideal (𝓞 Ω)) [P.IsPrime] (hP : (ℓ : 𝓞 Ω) ∉ P)
      (g : G) (hg : g ∈ P.inertia G) : (T).rep.ρ g = 1 := by
    have ha : α g = (((ψ (g.restrictNormal F))⁻¹ : Sˣ) : S) := by
      dsimp only [α]
      rw [padicTateScalarIn_eq_one_of_mem_inertia ℚ Ω ℓ i hP hg, map_one, mul_one]
    have he : ε g = 1 :=
      congrArg Units.val (cyclotomicCharacter_eq_one_of_mem_inertia ℚ Ω ℓ hP hg)
    have hψ : ψ (g.restrictNormal F) = 1 := by
      by_contra hn
      apply hres g
      change IsUnit (α g - algebraMap ℤ_[ℓ] S (ε g))
      rw [ha, he, map_one]
      exact sharedTwist_hostInverse_subOne_isUnit F ℓ S ψ hdegree hn
    rw [sharedTwist_inertia_scalar F ℓ i S ψ hP hg, hψ, inv_one, Units.val_one, one_smul]
  let I := Ideal.span {(ℓ : ℤ)}
  let _ : I.IsMaximal := rationalPrime_isMaximal ℓ
  obtain ⟨P, hP, hPI⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral I (S := 𝓞 Ω)
  let _ : P.IsPrime := hP.isPrime
  let _ : P.LiesOver I := hPI
  have hIne : I ≠ ⊥ := by
    change Ideal.span {(ℓ : ℤ)} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hprime.ne_zero
  have hPne := Ideal.ne_bot_of_liesOver_of_ne_bot hIne P
  have hPℓ : (ℓ : 𝓞 Ω) ∈ P := (natCast_mem_iff_dvd_of_liesOver_rationalPrime P ℓ ℓ).mpr dvd_rfl
  let _ : NeZero (ℓ : Ω) := ⟨Nat.cast_ne_zero.mpr hprime.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := (inferInstance : HasEnoughRootsOfUnity Ω ℓ).prim
  obtain ⟨t, ht, hta⟩ := exists_inertia_acts_by_unit_on_prime_roots P (-1 : (ZMod ℓ)ˣ)
  have hηt : η t = -1 := by
    apply ZMod.val_injective ℓ
    apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    exact (hηact t ζ hζ.pow_eq_one).symm.trans
      (by simpa only [Units.val_neg, Units.val_one] using hta ζ hζ.pow_eq_one)
  have ht₁ : η t ≠ 1 := by
    let _ : Fact (2 < ℓ) := ⟨lt_of_le_of_ne hprime.two_le hodd.symm⟩
    rw [hηt]
    exact ZMod.neg_one_ne_one
  have htdiv : ℓ ∣ n t + 1 := (ZMod.natCast_eq_zero_iff _ _).mp (by
    rw [Nat.cast_add, Nat.cast_one]
    change η t + 1 = 0
    rw [hηt, neg_add_cancel])
  have hπnt : π ∣ (n t : S) + 1 := hπℓ.trans (by
    have hd := map_dvd (Nat.castRingHom S) htdiv
    change (ℓ : S) ∣ ((n t + 1 : ℕ) : S) at hd
    rwa [Nat.cast_add, Nat.cast_one] at hd)
  have hαplus : π ∣ α t + 1 := by
    have he : α t - (n t : S) + ((n t : S) + 1) = α t + 1 := by ring
    exact he ▸ dvd_add (hαn t) hπnt
  have htwo : IsUnit (2 : S) := by
    have hu : IsUnit (2 : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr
      ((PadicInt.norm_natCast_eq_one_iff (n := 2)).mpr ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd))
    simpa only [map_ofNat] using hu.map (algebraMap ℤ_[ℓ] S)
  have htunit : IsUnit (α t - 1) := by
    by_contra hn
    have hminus := (hmax _).mp ((IsLocalRing.mem_maximalIdeal _).mpr hn)
    have he : α t + 1 - (α t - 1) = (2 : S) := by ring
    have h₂ : π ∣ (2 : S) := he ▸ dvd_sub hαplus hminus
    exact hπ.not_isUnit (isUnit_of_dvd_unit h₂ htwo)
  have hb := subOne_bijective_of_scalar T t (α t)
    (numberFieldSelmerSharedInverseTwist_ρ F ℓ i S ψ t) htunit
  exact rational_selmerKernel_subsingleton_of_residualCyclotomic Ω (hprime.odd_of_ne_two hodd) hζ η
    (fun g => hηact g ζ hζ.pow_eq_one) T π hπℓ htors P hPne hPℓ t ht ht₁ hb haway hρ

end SharedTwist

section Host

variable (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))
  [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O]

local notation "F" => selmerHostField target e q d
local notation "Ω" => AlgebraicClosure F
local notation "f" => selmerHostConductor target e q d
local instance : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d

set_option maxHeartbeats 600000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- The residual cyclotomic case of the arithmetic layer comparison
has length zero on the left of the Bernoulli bound. -/
theorem selmerSharedTwistArithmeticBernoulliBound_of_residualCyclotomic
    (hodd : ℓ ≠ 2) (hdegree : ¬ ℓ ∣ Module.finrank ℚ F)
    (ψ : Gal(F/ℚ) →* Oˣ)
    (hψ : (ψ (selmerHostConductorGalMap target e q d (-1)) : O) = (-1 : O) ^ (i + 1))
    (hres : ∀ g : Gal(Ω/ℚ), ¬ IsUnit (sharedTwistCyclotomicDifference F ℓ i O ψ g))
    (m : ℕ) : SelmerSharedTwistArithmeticBernoulliBound target e q d ℓ i O ψ m := by
  unfold SelmerSharedTwistArithmeticBernoulliBound
  dsimp only
  let T := numberFieldSelmerSharedInverseTwist F ℓ i O ψ
  let D := numberFieldSelmerRestrictionsIn ℚ Ω ℓ
  let δ := numberFieldTwistNormalizationElement F
  let _ : Subsingleton (T.selmerKernel D) :=
    sharedTwist_selmerKernel_subsingleton_of_residualCyclotomic F ℓ i O ψ hodd hdegree hres
  have hparity : (ψ (δ.restrictNormal F) : O) = (-1 : O) ^ (i + 1) := by
    change (ψ ((numberFieldTwistNormalizationElement F).restrictNormal F) : O) = _
    rw [numberFieldTwistNormalizationElement_restrictNormal_host target e q d]
    exact hψ
  let e₀ := normalizedSelmerCocyclesEquiv T D δ
    (numberFieldSelmerSharedTwist_normalization_bijective F ℓ i O ψ hodd hparity)
  let _ : Subsingleton (normalizedSelmerCocycles T D δ) :=
    ⟨fun a b => e₀.injective (Subsingleton.elim _ _)⟩
  let _ : Subsingleton (numberFieldSelmerSharedTwistArithmeticLayer F ℓ i O ψ m) := inferInstance
  rw [Module.length_eq_zero (R := O) (M := numberFieldSelmerSharedTwistArithmeticLayer F ℓ i O ψ m)]
  constructor
  · exact ENat.natCast_ne_top 0
  · simp only [ENat.toNat_zero, Nat.cast_zero, zero_mul]
    let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
    exact mul_nonneg (Nat.cast_nonneg _) (neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _)
      (norm_le_one_of_isIntegral_int (isIntegral_normalized_primitiveBernoulliValue _))))

end Host

/-- The remaining arithmetic comparison only needs the case where
some inverse-twist scalar differs from the cyclotomic scalar by a unit. -/
def HasSelmerSharedTwistNoncyclotomicArithmeticBernoulliComparison : Prop :=
  ∀ (target : BundledDirichletCharacter), target.character.IsPrimitive →
    ∀ (e : ℕ) (q d : ℕ+), 2 ≤ e → SelmerEstimatePrimePair target q d → ∀ i ≥ 1,
      let F := selmerHostField target e q d
      letI : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ¬ ℓ ∣ Module.finrank ℚ F →
        ∀ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))
          [IsDiscreteValuationRing O] [Module.Finite ℤ_[ℓ] O]
          [HasEnoughRootsOfUnity O (Monoid.exponent (F ≃ₐ[ℚ] F))],
          ∀ ψ : (F ≃ₐ[ℚ] F) →* Oˣ,
            (ψ (selmerHostConductorGalMap target e q d (-1)) : O) = (-1 : O) ^ (i + 1) →
            (∃ g, IsUnit (sharedTwistCyclotomicDifference F ℓ i O ψ g)) →
            ∀ m : ℕ, SelmerSharedTwistArithmeticBernoulliBound target e q d ℓ i O ψ m

theorem selmerSharedTwistArithmeticBernoulliComparison_of_noncyclotomic
    (h : HasSelmerSharedTwistNoncyclotomicArithmeticBernoulliComparison) :
    HasSelmerSharedTwistArithmeticBernoulliComparison := by
  intro target ht e q d he hp i hi
  dsimp only
  intro ℓ _ hodd hdegree O _ _ _ ψ hψ m
  let F := selmerHostField target e q d
  let _ : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  by_cases hunit : ∃ g, IsUnit (sharedTwistCyclotomicDifference F ℓ i O ψ g)
  · exact h target ht e q d he hp i hi ℓ hodd hdegree O ψ hψ hunit m
  · exact selmerSharedTwistArithmeticBernoulliBound_of_residualCyclotomic target e q d ℓ i O
      hodd hdegree ψ hψ (not_exists.mp hunit) m

end Riemann
