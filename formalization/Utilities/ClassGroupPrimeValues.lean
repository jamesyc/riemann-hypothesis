module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace Utilities

variable {R K G : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommGroup G]

theorem hasFiniteMulSupport_primeValues_zpow (a : HeightOneSpectrum R → G) (I : FractionalIdeal R⁰ K) :
    Function.HasFiniteMulSupport (fun v => a v ^ FractionalIdeal.count K v I) := by
  refine (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).subset ?_
  intro v hv hn
  apply hv
  change a v ^ FractionalIdeal.count K v I = 1
  rw [hn, zpow_zero]

/-- Extend a value on each nonzero prime ideal to a homomorphism on
nonzero fractional ideals using their integer exponents. -/
noncomputable def fractionalIdealHomOfPrimeValues (a : HeightOneSpectrum R → G) :
    (FractionalIdeal R⁰ K)ˣ →* G where
  toFun I := ∏ᶠ v, a v ^ FractionalIdeal.count K v I.val
  map_one' := by simp [FractionalIdeal.count_one]
  map_mul' I J := by
    simp only [Units.val_mul, FractionalIdeal.count_mul K _ I.ne_zero J.ne_zero, zpow_add]
    exact finprod_mul_distrib (hasFiniteMulSupport_primeValues_zpow a I.val)
      (hasFiniteMulSupport_primeValues_zpow a J.val)

@[simp]
theorem fractionalIdealHomOfPrimeValues_mk0 (a : HeightOneSpectrum R → G) (v : HeightOneSpectrum R) :
    fractionalIdealHomOfPrimeValues (K := K) a
      (FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩) = a v := by
  classical
  change (∏ᶠ w, a w ^ FractionalIdeal.count K w _) = a v
  simp only [FractionalIdeal.coe_mk0, FractionalIdeal.count_maximal]
  rw [finprod_eq_single _ v]
  · simp
  · intro w hw
    simp [Ne.symm hw]

/-- Extending the prime values of a homomorphism on integral ideals recovers
that homomorphism on every nonzero integral ideal. -/
theorem fractionalIdealHomOfPrimeValues_mk0_integral (f : (Ideal R)⁰ →* G) (I : (Ideal R)⁰) :
    fractionalIdealHomOfPrimeValues (K := K)
      (fun v => f ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)
      (FractionalIdeal.mk0 K I) = f I := by
  let P (v : HeightOneSpectrum R) : (Ideal R)⁰ :=
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  let n (v : HeightOneSpectrum R) : ℕ :=
    (Associates.mk v.asIdeal).count (Associates.mk I.val).factors
  have hI := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hs : Function.HasFiniteMulSupport (fun v => P v ^ n v) := by
    refine (Ideal.hasFiniteMulSupport hI).subset ?_
    intro v hv he
    apply hv
    exact Subtype.ext he
  have hprod : (∏ᶠ v, P v ^ n v) = I := by
    apply Subtype.ext
    change (nonZeroDivisors (Ideal R)).subtype (∏ᶠ v, P v ^ n v) = I.val
    rw [map_finprod _ hs]
    simp only [map_pow]
    change (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I.val) = I.val
    exact Ideal.finprod_heightOneSpectrum_factorization hI
  change (∏ᶠ v, f (P v) ^ FractionalIdeal.count K v (FractionalIdeal.mk0 K I).val) = f I
  calc
    _ = ∏ᶠ v, f (P v ^ n v) := by
      apply finprod_congr
      intro v
      rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coeIdeal K v hI, map_pow, zpow_natCast]
    _ = f I := (map_finprod f hs).symm.trans (congrArg f hprod)

/-- A fractional-ideal homomorphism trivial on principal ideals descends
to the ordinary class group. -/
noncomputable def classGroupHomOfTrivialPrincipal (f : (FractionalIdeal R⁰ K)ˣ →* G)
    (h : ∀ x : Kˣ, f (toPrincipalIdeal R K x) = 1) : ClassGroup R →* G :=
  (QuotientGroup.lift (toPrincipalIdeal R K).range f (by
    rintro _ ⟨x, rfl⟩
    exact h x)).comp (ClassGroup.equiv K).toMonoidHom

@[simp]
theorem classGroupHomOfTrivialPrincipal_mk (f : (FractionalIdeal R⁰ K)ˣ →* G)
    (h : ∀ x : Kˣ, f (toPrincipalIdeal R K x) = 1) (I : (FractionalIdeal R⁰ K)ˣ) :
    classGroupHomOfTrivialPrincipal f h (ClassGroup.mk K I) = f I := by
  simp [classGroupHomOfTrivialPrincipal, FractionalIdeal.canonicalEquiv_self]
  exact congrArg f (Units.ext rfl)

/-- A homomorphism on fractional ideals is determined by its values on primes. -/
theorem fractionalIdealHom_ext_on_primes
    {f g : (FractionalIdeal R⁰ K)ˣ →* G}
    (h : ∀ v : HeightOneSpectrum R,
      f (FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩) =
      g (FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) :
    f = g := by
  ext I
  let P (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
    FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  have hs := hasFiniteMulSupport_primeValues_zpow P I.val
  have hI : (∏ᶠ v, P v ^ FractionalIdeal.count K v I.val) = I := by
    apply Units.ext
    change Units.coeHom _ (∏ᶠ v, P v ^ FractionalIdeal.count K v I.val) = I.val
    rw [map_finprod _ hs]
    simp only [map_zpow, Units.coeHom_apply, P, FractionalIdeal.coe_mk0]
    exact FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero
  rw [← hI, map_finprod f hs, map_finprod g hs]
  apply finprod_congr
  intro v
  rw [map_zpow, map_zpow, show f (P v) = g (P v) from h v]

/-- A class-group homomorphism is determined by its values on the prime classes. -/
theorem classGroupHom_ext_on_primeClasses {f g : ClassGroup R →* G}
    (h : ∀ v : HeightOneSpectrum R,
      f (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩) =
      g (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) :
    f = g := by
  have hcomp : f.comp (ClassGroup.mk (FractionRing R)) = g.comp (ClassGroup.mk (FractionRing R)) :=
    fractionalIdealHom_ext_on_primes fun v => by simpa only [MonoidHom.comp_apply, ClassGroup.mk_mk0] using h v
  ext I
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective I
  rw [← ClassGroup.mk_mk0 (K := FractionRing R)]
  exact DFunLike.congr_fun hcomp _

section RingEquiv

variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L]

variable (K L) in
/-- Transport of the class group along an isomorphism of Dedekind domains. -/
noncomputable def classGroupMulEquivOfRingEquiv (e : R ≃+* S) :
    ClassGroup R ≃* ClassGroup S :=
  (ClassGroup.equiv K).trans ((QuotientGroup.congr (toPrincipalIdeal R K).range
    (toPrincipalIdeal S L).range (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K L e))
      (FractionalIdeal.map_ringEquivOfRingEquiv_toPrincipalIdeal (K := K) (L := L) e)).trans
    (ClassGroup.equiv L).symm)

variable (K L) in
theorem fractionalIdeal_ringEquivOfRingEquiv_coeIdeal (e : R ≃+* S) (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K L e (I : FractionalIdeal R⁰ K) =
      (I.map e : FractionalIdeal S⁰ L) := by
  ext y
  change y ∈ ((FractionalIdeal.ringEquivOfRingEquiv K L e) (I : FractionalIdeal R⁰ K)).val ↔ _
  rw [FractionalIdeal.ringEquivOfRingEquiv_apply_val, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    change x ∈ (I : FractionalIdeal R⁰ K) at hx
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
    change IsFractionRing.ringEquivOfRingEquiv e (algebraMap R K a) = y at hxy
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap] at hxy
    exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨e a, Ideal.mem_map_of_mem _ ha, hxy⟩
  · intro hy
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_of_equiv e b).mp hb
    refine ⟨algebraMap R K a, (FractionalIdeal.mem_coeIdeal _).mpr ⟨a, ha, rfl⟩, ?_⟩
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap e a

variable (K L) in
theorem fractionalIdealUnits_mapEquiv_mk0 (e : R ≃+* S) (I : (Ideal R)⁰)
    (hI : (I.val.map e : Ideal S) ∈ (Ideal S)⁰) :
    Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K L e)
      (FractionalIdeal.mk0 K I) = FractionalIdeal.mk0 L ⟨I.val.map e, hI⟩ := by
  apply Units.ext
  simp only [FractionalIdeal.coe_mk0]
  exact fractionalIdeal_ringEquivOfRingEquiv_coeIdeal K L e I.val

variable (K L) in
theorem classGroupMulEquivOfRingEquiv_mk0 (e : R ≃+* S) (I : (Ideal R)⁰)
    (hI : (I.val.map e : Ideal S) ∈ (Ideal S)⁰) :
    classGroupMulEquivOfRingEquiv K L e (ClassGroup.mk0 I) = ClassGroup.mk0 ⟨I.val.map e, hI⟩ := by
  apply (ClassGroup.equiv L).injective
  simp only [classGroupMulEquivOfRingEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    ClassGroup.equiv_mk0]
  exact congrArg (QuotientGroup.mk' (toPrincipalIdeal S L).range)
    (fractionalIdealUnits_mapEquiv_mk0 K L e I hI)

end RingEquiv

end Utilities
