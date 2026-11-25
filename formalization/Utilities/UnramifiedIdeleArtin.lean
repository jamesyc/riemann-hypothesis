module

public import Utilities.ArtinIdeal
public import Utilities.IdeleIdeal

@[expose] public section

open NumberField IsDedekindDomain
open scoped AdeleRing NumberField IsMulCommutative

namespace Utilities

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The idele symbol obtained from the arithmetic Frobenius values on ideals. -/
noncomputable def numberFieldUnramifiedIdeleArtin : IdeleGroup (𝓞 K) K →* Gal(L/K) :=
  (numberFieldIdealArtin K L).comp ideleToFractionalIdeal

@[simp]
theorem numberFieldUnramifiedIdeleArtin_unitEmbedding (x : Kˣ) :
    numberFieldUnramifiedIdeleArtin K L (IdeleGroup.unitEmbedding (𝓞 K) K x) =
      numberFieldIdealArtin K L (toPrincipalIdeal (𝓞 K) K x) := by
  simp [numberFieldUnramifiedIdeleArtin]

@[simp]
theorem numberFieldUnramifiedIdeleArtin_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    numberFieldUnramifiedIdeleArtin K L (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) =
      numberFieldPrimeArtin K L v ^ (adicCompletionOrder v x).toAdd := by
  simp [numberFieldUnramifiedIdeleArtin]

@[simp]
theorem numberFieldUnramifiedIdeleArtin_ofCompletion (w : InfinitePlace K) (x : w.Completionˣ) :
    numberFieldUnramifiedIdeleArtin K L (IdeleGroup.ofCompletion (𝓞 K) K w x) = 1 := by
  simp [numberFieldUnramifiedIdeleArtin]

/-- The finite local values determine the idele symbol among homomorphisms
trivial on ideles of order zero at every finite place. -/
theorem numberFieldUnramifiedIdeleArtin_eq_of_local
    (q : IdeleGroup (𝓞 K) K →* Gal(L/K))
    (hLocal : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ),
      q (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) =
        numberFieldPrimeArtin K L v ^ (adicCompletionOrder v x).toAdd)
    (hUnit : ∀ (a : IdeleGroup (𝓞 K) K), (∀ v, idelePrimeExponent a v = 0) → q a = 1) :
    q = numberFieldUnramifiedIdeleArtin K L := by
  classical
  apply MonoidHom.ext
  intro a
  let η (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup (𝓞 K) K :=
    IdeleGroup.ofAdicCompletion (𝓞 K) K v (finiteIdeleComponent v a)
  let S := (eventually_idelePrimeExponent_eq_zero a).toFinset
  let b := ∏ v ∈ S, η v
  have hb : ideleToFractionalIdeal b = ideleToFractionalIdeal a :=
    ideleToFractionalIdeal_prod_localComponents a S (fun v hv => by
      by_contra hn
      exact hv ((eventually_idelePrimeExponent_eq_zero a).mem_toFinset.mpr hn))
  have hab : ideleToFractionalIdeal (b⁻¹ * a) = 1 := by rw [map_mul, map_inv, hb, inv_mul_cancel]
  have hq : q (b⁻¹ * a) = 1 :=
    hUnit _ fun v => by
      rw [← count_ideleToFractionalIdeal, hab, Units.val_one, FractionalIdeal.count_one]
  rw [map_mul, map_inv, inv_mul_eq_one] at hq
  have hqb : q b = numberFieldUnramifiedIdeleArtin K L b := by
    dsimp only [b]
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun v _ =>
      (hLocal v (finiteIdeleComponent v a)).trans (numberFieldUnramifiedIdeleArtin_ofAdicCompletion _ _ _ _).symm
  exact hq.symm.trans (hqb.trans (congrArg (numberFieldIdealArtin K L) hb))

/-- An idele class reciprocity map with the unramified local normalization
supplies principal-ideal reciprocity for the ideal Artin map. -/
theorem numberFieldIdealArtin_principal_eq_one_of_ideleClass
    (q : IdeleClassGroup (𝓞 K) K →* Gal(L/K))
    (hLocal : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ),
      q (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x) =
        numberFieldPrimeArtin K L v ^ (adicCompletionOrder v x).toAdd)
    (hUnit : ∀ (a : IdeleGroup (𝓞 K) K), (∀ v, idelePrimeExponent a v = 0) →
      q (QuotientGroup.mk a) = 1)
    (x : Kˣ) :
    numberFieldIdealArtin K L (toPrincipalIdeal (𝓞 K) K x) = 1 := by
  let q₀ := q.comp (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
  have hq : q₀ = numberFieldUnramifiedIdeleArtin K L :=
    numberFieldUnramifiedIdeleArtin_eq_of_local K L q₀ hLocal hUnit
  rw [← numberFieldUnramifiedIdeleArtin_unitEmbedding, ← hq]
  change q (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K x)) = 1
  have hx : IdeleGroup.unitEmbedding (𝓞 K) K x ∈ IdeleGroup.principalSubgroup (𝓞 K) K :=
    ⟨x, rfl⟩
  have h₁ : (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K x) : IdeleClassGroup (𝓞 K) K) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hx
  rw [h₁, map_one]

/-- The global Artin map on idele classes in the unramified case, with the
arithmetic Frobenius normalization at finite places. -/
theorem exists_totallyComplex_unramified_ideleClassReciprocity
    (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (hunramified : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
      ∀ t ∈ P.inertia Gal(L/K), t = 1) :
    ∃ q : IdeleClassGroup (𝓞 K) K →* Gal(L/K),
      (∀ (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ),
        q (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x) =
          numberFieldPrimeArtin K L v ^ (adicCompletionOrder v x).toAdd) ∧
      (∀ (a : IdeleGroup (𝓞 K) K), (∀ v, idelePrimeExponent a v = 0) →
        q (QuotientGroup.mk a) = 1) := by
  sorry

/-- Principal Artin symbols in a finite abelian extension unramified at every
finite prime of a totally complex number field. -/
theorem totallyComplex_unramified_principal_reciprocity :
    HasTotallyComplexUnramifiedPrincipalReciprocity := by
  intro E T _ _ _ _ _ _ _ _ hunramified x
  obtain ⟨q, hLocal, hUnit⟩ := exists_totallyComplex_unramified_ideleClassReciprocity E T hunramified
  exact numberFieldIdealArtin_principal_eq_one_of_ideleClass E T q hLocal hUnit x

end Utilities
