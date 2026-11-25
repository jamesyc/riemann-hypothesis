module

public import Riemann.SelmerEigenspaceLength
public import Utilities.KrullConjugation
public import Utilities.SelmerKernelAction
public import Utilities.NumberFieldTorsion

@[expose] public section

open Utilities
open scoped NumberField Pointwise

namespace Riemann

variable (F : Type) [Field F] [NumberField F] [Normal ℚ F]

local notation "L" => AlgebraicClosure F
local notation "G" => (L ≃ₐ[F] L)
local notation "H" => (L ≃ₐ[ℚ] L)

private theorem relativeGaloisConj_smul (τ : H) (σ : G) (x : 𝓞 L) :
    relativeGaloisConj ℚ F L τ σ • x = τ • (σ • (τ⁻¹ • x)) := by
  apply NumberField.RingOfIntegers.ext
  rfl

/-- The restriction conditions are invariant under conjugation by any
automorphism of the algebraic closure over `ℚ`. -/
theorem numberFieldSelmerRestrictions_map_conj (ℓ : ℕ) (τ : H)
    (D : Subgroup (Field.absoluteGaloisGroup F))
    (hD : D ∈ numberFieldSelmerRestrictions F ℓ) :
    D.map (relativeGaloisConj ℚ F L τ) ∈ numberFieldSelmerRestrictions F ℓ := by
  change D ∈ {D' | _} at hD
  obtain ⟨v, P, hprime, hcomap, hcase⟩ := hD
  let t := τ.restrictNormal F
  let V := t • v.maximalIdeal.asIdeal
  have hVprime : V.IsPrime := by
    exact (Ideal.IsPrime.smul_iff t).mpr (inferInstance : v.maximalIdeal.asIdeal.IsPrime)
  have hVne : V ≠ ⊥ := by
    intro h
    apply v.maximalIdeal.ne_bot
    have h' := congrArg (fun I : Ideal (𝓞 F) => t⁻¹ • I) h
    simpa only [V, inv_smul_smul, smul_bot] using h'
  let v' := NumberField.FinitePlace.mk ⟨V, hVprime, hVne⟩
  let P' := τ • P
  have hv' : v'.maximalIdeal.asIdeal = V := by
    simp [v', NumberField.FinitePlace.maximalIdeal_mk]
  have hmap_int (x : 𝓞 F) :
      τ⁻¹ • NumberField.RingOfIntegers.mapRingHom (algebraMap F L) x =
        NumberField.RingOfIntegers.mapRingHom (algebraMap F L) (t⁻¹ • x) := by
    apply NumberField.RingOfIntegers.ext
    change τ.symm (algebraMap F L (x : F)) = algebraMap F L (t.symm (x : F))
    have ht : τ.symm.restrictNormal F = t.symm := map_inv (AlgEquiv.restrictNormalHom F) τ
    rw [← ht]
    exact (τ.symm.restrictNormal_commutes F _).symm
  have hcomap' :
      P'.comap (NumberField.RingOfIntegers.mapRingHom (algebraMap F L)) = v'.maximalIdeal.asIdeal := by
    rw [hv']
    ext x
    change NumberField.RingOfIntegers.mapRingHom (algebraMap F L) x ∈ τ • P ↔ x ∈ V
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hmap_int]
    change t⁻¹ • x ∈ P.comap _ ↔ x ∈ t • v.maximalIdeal.asIdeal
    rw [hcomap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  let e := MulEquiv.ofBijective (relativeGaloisConj ℚ F L τ)
    (relativeGaloisConj_bijective ℚ F L τ)
  have hconj_smul (σ : G) (x : 𝓞 L) : e σ • (τ • x) = τ • (σ • x) := by
    change relativeGaloisConj ℚ F L τ σ • (τ • x) = _
    rw [relativeGaloisConj_smul, inv_smul_smul]
  have hI : (P.inertia G).map (relativeGaloisConj ℚ F L τ) = P'.inertia G := by
    ext z
    obtain ⟨σ, rfl⟩ := e.surjective z
    change e σ ∈ (P.inertia G).map e.toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv, e.symm_apply_apply]
    simp only [Ideal.mem_inertia]
    constructor
    · intro hz x
      obtain ⟨y, rfl⟩ := (MulAction.toPerm τ : Equiv (𝓞 L) (𝓞 L)).surjective x
      change e σ • (τ • y) - τ • y ∈ τ • P
      rw [hconj_smul, ← smul_sub, Ideal.smul_mem_pointwise_smul_iff]
      exact hz y
    · intro hz x
      specialize hz (τ • x)
      rw [hconj_smul, ← smul_sub, Ideal.smul_mem_pointwise_smul_iff] at hz
      exact hz
  have hStab : (MulAction.stabilizer G P).map (relativeGaloisConj ℚ F L τ) =
      MulAction.stabilizer G P' := by
    ext z
    obtain ⟨σ, rfl⟩ := e.surjective z
    change e σ ∈ (MulAction.stabilizer G P).map e.toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv, e.symm_apply_apply]
    have hconj_ideal : e σ • P' = τ • (σ • P) := by
      ext x
      obtain ⟨y, rfl⟩ := (MulAction.toPerm (e σ) : Equiv (𝓞 L) (𝓞 L)).surjective x
      obtain ⟨a, rfl⟩ := (MulAction.toPerm τ : Equiv (𝓞 L) (𝓞 L)).surjective y
      change e σ • (τ • a) ∈ e σ • (τ • P) ↔ e σ • (τ • a) ∈ τ • (σ • P)
      rw [Ideal.smul_mem_pointwise_smul_iff, Ideal.smul_mem_pointwise_smul_iff, hconj_smul,
        Ideal.smul_mem_pointwise_smul_iff, Ideal.smul_mem_pointwise_smul_iff]
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, hconj_ideal]
    exact ((MulAction.toPerm τ : Equiv (Ideal (𝓞 L)) (Ideal (𝓞 L))).injective.eq_iff).symm
  refine ⟨v', P', (Ideal.IsPrime.smul_iff τ).mpr hprime, hcomap', ?_⟩
  rcases hcase with hI' | ⟨hℓ, hS'⟩
  · exact Or.inl (hI' ▸ hI)
  · refine Or.inr ⟨?_, hS' ▸ hStab⟩
    rw [hv', Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulSemiringAction.toRingAut _ (𝓞 F) t⁻¹) (ℓ : 𝓞 F) ∈ v.maximalIdeal.asIdeal
    rwa [map_natCast]

theorem padicTateScalar_relativeGaloisConj (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)
    (τ : H) (σ : G) :
    padicTateScalar F ℓ i (relativeGaloisConj ℚ F L τ σ) = padicTateScalar F ℓ i σ := by
  let χ := padicTateScalarOnAut L ℓ i
  change χ (τ.toRingEquiv * σ.toRingEquiv * τ.toRingEquiv⁻¹) = χ σ.toRingEquiv
  rw [map_mul, map_mul, mul_comm (χ τ.toRingEquiv), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    mul_one]

local instance : IsAlgClosure ℚ L := IsAlgClosure.ofAlgebraic ℚ F L

/-- Complex conjugation acts on the actual continuous restriction kernel by
conjugating the absolute Galois group and acting on the Tate coefficient. -/
noncomputable def numberFieldSelmerConjugation (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)
    (ι : L →ₐ[ℚ] ℂ) :
    Module.End ℤ_[ℓ] ((padicTateTwist F ℓ i).selmerKernel (numberFieldSelmerRestrictions F ℓ)) := by
  let τ := algEquiv_complexConjugation L ι
  let φ : Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup F :=
    relativeGaloisConj ℚ F L τ
  let u : Module.End ℤ_[ℓ] (padicTateTwist F ℓ i).rep :=
    padicTateScalarOnAut L ℓ i τ.toRingEquiv • LinearMap.id
  refine (padicTateTwist F ℓ i).pullbackSelmerKernel (numberFieldSelmerRestrictions F ℓ)
    φ (relativeGaloisConj_continuous ℚ F L τ) u ?_ ?_
  · intro σ a
    have hscalar : padicTateScalar F ℓ i (φ σ) = padicTateScalar F ℓ i σ :=
      padicTateScalar_relativeGaloisConj F ℓ i τ σ
    rw [padicTateTwist_ρ_apply, padicTateTwist_ρ_apply, hscalar]
    exact u.map_smul _ _
  · exact numberFieldSelmerRestrictions_map_conj F ℓ τ

theorem numberFieldSelmerConjugation_involutive (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)
    (ι : L →ₐ[ℚ] ℂ) : Function.Involutive (numberFieldSelmerConjugation F ℓ i ι) := by
  unfold numberFieldSelmerConjugation
  refine (padicTateTwist F ℓ i).pullbackSelmerKernel_involutive _ _ _ _ _ _ ?_ ?_
  · let τ := algEquiv_complexConjugation L ι
    have hτ : τ.symm = τ := by
      apply AlgEquiv.ext
      intro x
      apply τ.injective
      exact (τ.apply_symm_apply x).trans ((algEquiv_complexConjugation_involutive L ι x).symm)
    have h := relativeGaloisConj_leftInverse ℚ F L τ
    rwa [hτ] at h
  · let τ := algEquiv_complexConjugation L ι
    have hτ : τ.toRingEquiv * τ.toRingEquiv = 1 := by
      apply RingEquiv.ext
      intro x
      exact algEquiv_complexConjugation_involutive L ι x
    let χ := padicTateScalarOnAut L ℓ i
    intro a
    change χ τ.toRingEquiv • (χ τ.toRingEquiv • a) = a
    rw [← mul_smul, ← map_mul, hτ, map_one, one_smul]

/-- The parity-adjusted sign component from Lemma 17.6 and Theorem 17.12. -/
noncomputable def numberFieldSelmerSignLength (positive : Bool) (ι : L →ₐ[ℚ] ℂ)
    (ℓ i : ℕ) : WithTop ℕ := by
  classical
  exact if hℓ : ℓ.Prime then
    letI : Fact ℓ.Prime := ⟨hℓ⟩
    let s : ℤ_[ℓ] := (-1) ^ i
    primaryCardLength ℓ ((numberFieldSelmerConjugation F ℓ i ι).eigenspace
      (if positive then s else -s))
  else ⊤

/-- Lemma 17.6 in logarithmic cardinality form, for the actual Selmer kernels. -/
theorem numberFieldSelmerLengths_eq_sign_add (ι : L →ₐ[ℚ] ℂ) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (i : ℕ) :
    numberFieldSelmerLengths F ℓ i =
      numberFieldSelmerSignLength F true ι ℓ i + numberFieldSelmerSignLength F false ι ℓ i := by
  let : Fact ℓ.Prime := ⟨hℓ⟩
  have hsplit := primaryCardLength_of_involution ℓ hodd
    (numberFieldSelmerConjugation F ℓ i ι) (numberFieldSelmerConjugation_involutive F ℓ i ι)
  by_cases he : Even i
  · simpa [numberFieldSelmerLengths, numberFieldSelmerSignLength, hℓ, he.neg_one_pow] using hsplit
  · have ho : Odd i := Nat.not_even_iff_odd.mp he
    simpa [numberFieldSelmerLengths, numberFieldSelmerSignLength, hℓ, ho.neg_one_pow, add_comm] using hsplit

end Riemann
