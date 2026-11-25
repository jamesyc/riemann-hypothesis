module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

@[expose] public section

open IsDedekindDomain NumberField
open scoped AdeleRing WithZero nonZeroDivisors

namespace Utilities

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The exponent of a prime in a principal ideal is the additive order of
its generator. Mathlib's multiplicative valuation uses the opposite sign. -/
theorem fractionalIdeal_count_toPrincipalIdeal (v : HeightOneSpectrum R) (x : Kˣ) :
    FractionalIdeal.count K v (toPrincipalIdeal R K x : FractionalIdeal R⁰ K) =
      -(v.valuationOfNeZero x).toAdd := by
  let z := IsLocalization.sec R⁰ (x : K)
  have hfrac : algebraMap R K z.1 / algebraMap R K (z.2 : R) = (x : K) :=
    (IsFractionRing.mk'_eq_div z.2).symm.trans (IsLocalization.mk'_sec _ _)
  have hI : (toPrincipalIdeal R K x : FractionalIdeal R⁰ K) =
      FractionalIdeal.spanSingleton R⁰ (algebraMap R K (z.2 : R))⁻¹ *
        (Ideal.span {z.1} : Ideal R) := by
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton, ← map_mul,
      mul_comm, ← div_eq_mul_inv, hfrac]
  rw [FractionalIdeal.count_well_defined K v (toPrincipalIdeal R K x).ne_zero hI]
  change _ = -(-((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {z.1})).factors : ℤ) -
    (-((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(z.2 : R)})).factors : ℤ)))
  omega

/-- The finite component of an idele, as a unit in the completion. -/
noncomputable def finiteIdeleComponent (v : HeightOneSpectrum R) : IdeleGroup R K →* (v.adicCompletion K)ˣ :=
  Units.map { toFun := fun a : AdeleRing R K => a.2 v, map_one' := rfl, map_mul' := fun _ _ => rfl }

@[simp]
theorem finiteIdeleComponent_ofAdicCompletion_same (v : HeightOneSpectrum R)
    (x : (v.adicCompletion K)ˣ) :
    finiteIdeleComponent v (IdeleGroup.ofAdicCompletion R K v x) = x := by
  classical
  apply Units.ext
  change FiniteAdeleRing.ofAdicCompletion K v (x : v.adicCompletion K) v = x
  exact RestrictedProduct.mulSingle_eq_same (fun w => w.adicCompletionIntegers K) v _

theorem finiteIdeleComponent_ofAdicCompletion_ne {v w : HeightOneSpectrum R} (h : v ≠ w)
    (x : (v.adicCompletion K)ˣ) :
    finiteIdeleComponent w (IdeleGroup.ofAdicCompletion R K v x) = 1 := by
  classical
  apply Units.ext
  change FiniteAdeleRing.ofAdicCompletion K v (x : v.adicCompletion K) w = 1
  exact RestrictedProduct.mulSingle_eq_of_ne' (fun w => w.adicCompletionIntegers K) _ h

@[simp]
theorem finiteIdeleComponent_ofCompletion (v : HeightOneSpectrum R) (w : InfinitePlace K)
    (x : w.Completionˣ) :
    finiteIdeleComponent v (IdeleGroup.ofCompletion R K w x) = 1 := by
  apply Units.ext
  rfl

/-- The additive order on a finite completion, written multiplicatively to
use the usual homomorphisms on units. -/
noncomputable def adicCompletionOrder (v : HeightOneSpectrum R) :
    (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
  (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).toMonoidWithZeroHom.toMonoidHom))⁻¹

theorem coe_adicCompletionOrder_inv (v : HeightOneSpectrum R) (x : (v.adicCompletion K)ˣ) :
    (↑((adicCompletionOrder v x)⁻¹) : ℤᵐ⁰) = Valued.v (x : v.adicCompletion K) := by
  rw [adicCompletionOrder, MonoidHom.inv_apply, inv_inv, MonoidHom.comp_apply]
  exact WithZero.coe_unitsWithZeroEquiv_eq_units_val _

theorem adicCompletionOrder_eq_one_iff (v : HeightOneSpectrum R) (x : (v.adicCompletion K)ˣ) :
    adicCompletionOrder v x = 1 ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  rw [← coe_adicCompletionOrder_inv v x, ← WithZero.coe_one, WithZero.coe_inj, inv_eq_one]

theorem adicCompletionOrder_algebraMap (v : HeightOneSpectrum R) (x : Kˣ) :
    adicCompletionOrder v (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) =
      (v.valuationOfNeZero x)⁻¹ := by
  rw [← inv_inj, inv_inv, ← WithZero.coe_inj, coe_adicCompletionOrder_inv, v.valuationOfNeZero_eq]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : K)

/-- The exponent of a finite prime in the ideal of an idele. -/
noncomputable def idelePrimeExponent (a : IdeleGroup R K) (v : HeightOneSpectrum R) : ℤ :=
  (adicCompletionOrder v (finiteIdeleComponent v a)).toAdd

theorem eventually_idelePrimeExponent_eq_zero (a : IdeleGroup R K) :
    ∀ᶠ v in Filter.cofinite, idelePrimeExponent a v = 0 := by
  filter_upwards [(AdeleRing.isUnit_iff.mp a.isUnit).2.2] with v hv
  have h : adicCompletionOrder v (finiteIdeleComponent v a) = 1 :=
    (adicCompletionOrder_eq_one_iff _ _).mpr hv
  exact congrArg Multiplicative.toAdd h
private noncomputable def primeFractionalIdeal (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩

private theorem hasFiniteMulSupport_primeFractionalIdeal (a : IdeleGroup R K) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R =>
      (primeFractionalIdeal (K := K) v) ^ idelePrimeExponent a v) :=
  (Filter.eventually_cofinite.mp (eventually_idelePrimeExponent_eq_zero a)).subset fun v hv h =>
    hv (by simp [h])

/-- The fractional ideal of an idele, formed from the orders of its finite
components. Infinite components and finite local units have order zero. -/
@[no_expose]
noncomputable def ideleToFractionalIdeal : IdeleGroup R K →* (FractionalIdeal R⁰ K)ˣ where
  toFun a := ∏ᶠ v, (primeFractionalIdeal v) ^ idelePrimeExponent a v
  map_one' := by simp [idelePrimeExponent]
  map_mul' a b := by
    simp only [idelePrimeExponent, map_mul]
    change (∏ᶠ v, primeFractionalIdeal (K := K) v ^ (idelePrimeExponent a v + idelePrimeExponent b v)) = _
    simp only [zpow_add]
    exact finprod_mul_distrib (hasFiniteMulSupport_primeFractionalIdeal a)
      (hasFiniteMulSupport_primeFractionalIdeal b)

theorem count_ideleToFractionalIdeal (a : IdeleGroup R K) (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (ideleToFractionalIdeal a : FractionalIdeal R⁰ K) = idelePrimeExponent a v := by
  change FractionalIdeal.count K v (Units.coeHom _ (∏ᶠ w, (primeFractionalIdeal w) ^
    idelePrimeExponent a w)) = _
  rw [map_finprod _ (hasFiniteMulSupport_primeFractionalIdeal a)]
  simp only [map_zpow, Units.coeHom_apply, primeFractionalIdeal, FractionalIdeal.coe_mk0]
  exact FractionalIdeal.count_finprod K v _ (eventually_idelePrimeExponent_eq_zero a)

/-- Equality of all prime exponents determines a nonzero fractional ideal. -/
theorem fractionalIdeal_unit_ext_count {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I.val = FractionalIdeal.count K v J.val) :
    I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.ne_zero]
  simp only [h]

@[simp]
theorem ideleToFractionalIdeal_unitEmbedding (x : Kˣ) :
    ideleToFractionalIdeal (IdeleGroup.unitEmbedding R K x) = toPrincipalIdeal R K x := by
  apply fractionalIdeal_unit_ext_count
  intro v
  rw [count_ideleToFractionalIdeal, fractionalIdeal_count_toPrincipalIdeal]
  have hx : finiteIdeleComponent v (IdeleGroup.unitEmbedding R K x) =
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x := by
    apply Units.ext
    exact AdeleRing.algebraMap_snd_apply R K (x : K) v
  rw [idelePrimeExponent, hx, adicCompletionOrder_algebraMap]
  rfl

@[simp]
theorem ideleToFractionalIdeal_ofAdicCompletion (v : HeightOneSpectrum R)
    (x : (v.adicCompletion K)ˣ) :
    ideleToFractionalIdeal (IdeleGroup.ofAdicCompletion R K v x) =
      FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ ^
        (adicCompletionOrder v x).toAdd := by
  classical
  change (∏ᶠ w, primeFractionalIdeal (K := K) w ^
    idelePrimeExponent (IdeleGroup.ofAdicCompletion R K v x) w) = _
  rw [finprod_eq_single _ v]
  · simp [primeFractionalIdeal, idelePrimeExponent]
  · intro w hw
    simp [idelePrimeExponent, finiteIdeleComponent_ofAdicCompletion_ne hw.symm]

@[simp]
theorem ideleToFractionalIdeal_ofCompletion (w : InfinitePlace K) (x : w.Completionˣ) :
    ideleToFractionalIdeal (IdeleGroup.ofCompletion R K w x) = 1 := by
  change (∏ᶠ v, primeFractionalIdeal (K := K) v ^
    idelePrimeExponent (IdeleGroup.ofCompletion R K w x) v) = 1
  simp [idelePrimeExponent]

/-- A finite product of the local components carrying the nonzero orders
has the same fractional ideal as the original idele. -/
theorem ideleToFractionalIdeal_prod_localComponents (a : IdeleGroup R K)
    (s : Finset (HeightOneSpectrum R)) (hs : ∀ v ∉ s, idelePrimeExponent a v = 0) :
    ideleToFractionalIdeal (∏ v ∈ s, IdeleGroup.ofAdicCompletion R K v (finiteIdeleComponent v a)) =
      ideleToFractionalIdeal a := by
  rw [map_prod]
  change _ = ∏ᶠ v, (primeFractionalIdeal v) ^ idelePrimeExponent a v
  rw [finprod_eq_finsetProd_of_mulSupport_subset _ (s := s) (fun v hv => by
    by_contra hn
    exact hv (by simp [hs v hn]))]
  simp [primeFractionalIdeal, idelePrimeExponent]

end Utilities
