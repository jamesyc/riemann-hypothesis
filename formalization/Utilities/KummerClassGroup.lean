module

public import Utilities.NumberFieldUnitPowerClasses
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Utilities.NumberFieldClassBounds

@[expose] public section

open scoped NumberField nonZeroDivisors
open NumberField FractionalIdeal IsDedekindDomain

namespace Utilities

/-- The fractional ideal group modulo nth powers. -/
abbrev FractionalIdealPowerClass (K : Type*) [Field K] (n : ℕ) :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ (powMonoidHom n : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* _).range

/-- A nonzero fractional ideal is an nth power precisely when every prime
exponent is divisible by n. -/
theorem numberFieldFractionalIdeal_mem_pow_range_iff (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    I ∈ (powMonoidHom n : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* _).range ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (n : ℤ) ∣ count K v I.val := by
  constructor
  · rintro ⟨J, rfl⟩ v
    change (n : ℤ) ∣ count K v ((J : FractionalIdeal (𝓞 K)⁰ K) ^ n)
    rw [count_pow]
    exact dvd_mul_right _ _
  · intro h
    let e (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := count K v I.val / (n : ℤ)
    have he : ∀ᶠ v in Filter.cofinite, e v = 0 :=
      (finite_factors I.val).mono fun _ hv => by simp [e, hv]
    let J : FractionalIdeal (𝓞 K)⁰ K := ∏ᶠ v, (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ e v
    have hJ : J ≠ 0 := by
      apply finprod_induction (fun A : FractionalIdeal (𝓞 K)⁰ K => A ≠ 0) one_ne_zero
      · intro A B hA hB
        exact mul_ne_zero hA hB
      · intro v
        exact zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
    have hcount (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
        count K v (J ^ n) = count K v I.val := by
      rw [count_pow, show count K v J = e v from count_finprod K v e he]
      exact Int.mul_ediv_cancel' (h v)
    have hpow : J ^ n = I.val := by
      calc
        _ = ∏ᶠ v, (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ count K v (J ^ n) :=
          (finprod_heightOneSpectrum_factorization' K (pow_ne_zero _ hJ)).symm
        _ = ∏ᶠ v, (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ count K v I.val :=
          finprod_congr fun v => by rw [hcount]
        _ = _ := finprod_heightOneSpectrum_factorization' K I.ne_zero
    exact ⟨Units.mk0 J hJ, Units.ext hpow⟩

/-- Send the class of an element to the class of its principal fractional ideal. -/
noncomputable def numberFieldPrincipalPowerClass (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    KummerPowerClass K n →* FractionalIdealPowerClass K n := by
  apply QuotientGroup.map _ _ (toPrincipalIdeal (𝓞 K) K)
  rintro _ ⟨a, rfl⟩
  exact ⟨toPrincipalIdeal (𝓞 K) K a, (map_pow _ a n).symm⟩

/-- Prime-exponent residues of a principal ideal descend to power classes. -/
noncomputable def numberFieldPrincipalValuationResidue (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    KummerPowerClass K n →* Multiplicative (ZMod n) := by
  let p := toPrincipalIdeal (𝓞 K) K
  let f : Kˣ →* Multiplicative (ZMod n) :=
    { toFun := fun a => Multiplicative.ofAdd (count K v (p a).val : ZMod n)
      map_one' := by
        change (count K v (p 1).val : ZMod n) = 0
        rw [map_one, Units.val_one, count_one, Int.cast_zero]
      map_mul' := fun a b => by
        change (count K v (p (a * b)).val : ZMod n) =
          (count K v (p a).val : ZMod n) + (count K v (p b).val : ZMod n)
        rw [map_mul, Units.val_mul, count_mul K v (p a).ne_zero (p b).ne_zero, Int.cast_add] }
  refine QuotientGroup.lift _ f ?_
  rintro _ ⟨a, rfl⟩
  change (count K v (p (a ^ n)).val : ZMod n) = 0
  rw [map_pow, Units.val_pow_eq_pow_val, count_pow, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

@[simp]
theorem numberFieldPrincipalValuationResidue_mk (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    numberFieldPrincipalValuationResidue K n v (QuotientGroup.mk a) =
      Multiplicative.ofAdd (count K v (toPrincipalIdeal (𝓞 K) K a).val : ZMod n) := rfl

/-- The principal-ideal map kills exactly the classes with all prime
exponent residues zero. -/
theorem numberFieldPrincipalPowerClass_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (x : KummerPowerClass K n) :
    numberFieldPrincipalPowerClass K n x = 1 ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), numberFieldPrincipalValuationResidue K n v x = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  let I := toPrincipalIdeal (𝓞 K) K a
  change (QuotientGroup.mk I : FractionalIdealPowerClass K n) = 1 ↔
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (count K v I.val : ZMod n) = 0
  rw [QuotientGroup.eq_one_iff, numberFieldFractionalIdeal_mem_pow_range_iff]
  exact forall_congr' fun v => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm

/-- A field unit with trivial principal ideal comes from an integer unit. -/
theorem exists_unit_of_principal_eq_one (K : Type*) [Field K] [NumberField K]
    (a : Kˣ) (ha : toPrincipalIdeal (𝓞 K) K a = 1) :
    ∃ u : (𝓞 K)ˣ, Units.map (algebraMap (𝓞 K) K).toMonoidHom u = a := by
  have hai : toPrincipalIdeal (𝓞 K) K a⁻¹ = 1 := by rw [map_inv, ha, inv_one]
  have hval (b : Kˣ) (hb : toPrincipalIdeal (𝓞 K) K b = 1) :
      (b : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have heq := congrArg (fun I : (FractionalIdeal (𝓞 K)⁰ K)ˣ => I.val) hb
    rw [coe_toPrincipalIdeal, Units.val_one] at heq
    rw [← heq]
    exact mem_spanSingleton_self _ _
  obtain ⟨x, hx⟩ := (mem_one_iff (𝓞 K)⁰).mp (hval a ha)
  obtain ⟨y, hy⟩ := (mem_one_iff (𝓞 K)⁰).mp (hval a⁻¹ hai)
  have hxy : x * y = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_one, hx, hy]
    exact congrArg (fun z : Kˣ => (z : K)) (mul_inv_cancel a)
  exact ⟨⟨x, y, hxy, mul_comm x y ▸ hxy⟩, Units.ext hx⟩

/-- Power classes whose principal ideals are nth powers are bounded by the
ordinary unit contribution times the class number. -/
theorem finite_card_numberFieldPrincipalPowerClass_ker_le (K : Type*) [Field K] [NumberField K]
    (n : ℕ) [NeZero n] :
    Finite (numberFieldPrincipalPowerClass K n).ker ∧
      Nat.card (numberFieldPrincipalPowerClass K n).ker ≤ n ^ Module.finrank ℚ K * classNumber K := by
  classical
  let p := toPrincipalIdeal (𝓞 K) K
  let S := (numberFieldPrincipalPowerClass K n).ker
  let C := (FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ p.range
  have harep (x : S) : ∃ a : Kˣ, (QuotientGroup.mk a : KummerPowerClass K n) = x.val :=
    QuotientGroup.mk_surjective x.val
  choose a ha using harep
  have hbrep (x : S) : ∃ b : (FractionalIdeal (𝓞 K)⁰ K)ˣ, b ^ n = p (a x) := by
    have h := MonoidHom.mem_ker.mp x.property
    rw [← ha x] at h
    change (QuotientGroup.mk (p (a x)) : FractionalIdealPowerClass K n) = 1 at h
    exact (QuotientGroup.eq_one_iff _).mp h
  choose b hb using hbrep
  let c : S → C := fun x => QuotientGroup.mk (b x)
  let ci (x : S) : Set.range c := ⟨c x, Set.mem_range_self x⟩
  let base (d : Set.range c) : S := d.property.choose
  have hbase (d : Set.range c) : c (base d) = d.val := d.property.choose_spec
  let U := NumberFieldUnitPowerClasses K n
  let unitMap := numberFieldUnitPowerClassesToKummer K n
  have hunit (x : S) : ∃ u : U, unitMap u * (base (ci x)).val = x.val := by
    let y := base (ci x)
    have heq : c x = c y := (hbase (ci x)).symm
    obtain ⟨k, hk⟩ : ∃ k : Kˣ, p k = b x / b y := QuotientGroup.eq_iff_div_mem.mp heq
    have hprincipal : p (a x / (a y * k ^ n)) = 1 := by
      rw [map_div, map_mul, map_pow, ← hb x, ← hb y, hk, div_pow, mul_div_cancel]
      exact div_self' (b x ^ n)
    obtain ⟨u, hu⟩ := exists_unit_of_principal_eq_one K _ hprincipal
    refine ⟨QuotientGroup.mk u, ?_⟩
    change (QuotientGroup.mk (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) : KummerPowerClass K n) *
      y.val = x.val
    rw [hu, ← ha y, ← ha x, ← QuotientGroup.mk_mul]
    apply QuotientGroup.eq_iff_div_mem.mpr
    refine ⟨k⁻¹, ?_⟩
    change (k⁻¹) ^ n = (a x / (a y * k ^ n) * a y) / a x
    rw [inv_pow, div_mul_eq_div_mul_one_div, one_div, mul_comm (a x / a y), mul_assoc,
      div_mul_cancel, mul_div_cancel_right]
  choose u hu using hunit
  let f : S → U × C := fun x => (u x, c x)
  have hf : Function.Injective f := by
    intro x y h
    have hu' : u x = u y := congrArg Prod.fst h
    have hc' : ci x = ci y := Subtype.ext (congrArg Prod.snd h)
    apply Subtype.ext
    rw [← hu x, ← hu y, hu', hc']
  obtain ⟨hfU, hU⟩ := finite_card_numberFieldUnitPowerClasses_le_degree K n
  let _ : Finite U := hfU
  let ec : ClassGroup (𝓞 K) ≃* C := ClassGroup.equiv K
  let _ : Finite C := Finite.of_equiv _ ec.toEquiv
  have hC : Nat.card C = classNumber K := by
    rw [← Nat.card_congr ec.toEquiv, Nat.card_eq_fintype_card]
    rfl
  refine ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  rw [Nat.card_prod, hC]
  exact Nat.mul_le_mul_right _ hU

/-- The power classes with zero prime-exponent residues away from ℓ. -/
noncomputable def numberFieldValuationRestrictedPowerClasses (K : Type*) [Field K] [NumberField K]
    (ℓ : ℕ) : Subgroup (KummerPowerClass K ℓ) :=
  ⨅ v : {v : HeightOneSpectrum (𝓞 K) // (ℓ : 𝓞 K) ∉ v.asIdeal},
    (numberFieldPrincipalValuationResidue K ℓ v.val).ker

private theorem numberFieldPrimeDivisors_card_le_degree (K : Type*) [Field K] [NumberField K]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    let T := {v : HeightOneSpectrum (𝓞 K) // (ℓ : 𝓞 K) ∈ v.asIdeal}
    Finite T ∧ Nat.card T ≤ Module.finrank ℚ K := by
  let T := {v : HeightOneSpectrum (𝓞 K) // (ℓ : 𝓞 K) ∈ v.asIdeal}
  let p : Ideal ℤ := Ideal.span {(ℓ : ℤ)}
  have hp : ℓ.Prime := Fact.out
  have hp₀ : p ≠ ⊥ := by simpa [p] using hp.ne_zero
  let _ : p.IsPrime := Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp hp)
  let hpmax : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp₀
  let f : T → primesOverFinset p (𝓞 K) := fun v => by
    let _ : v.val.asIdeal.IsPrime := v.val.isPrime
    have hle : p ≤ v.val.asIdeal.under ℤ := by
      apply (Ideal.span_singleton_le_iff_mem (v.val.asIdeal.under ℤ)).mpr
      change algebraMap ℤ (𝓞 K) (ℓ : ℤ) ∈ v.val.asIdeal
      have hcast : algebraMap ℤ (𝓞 K) (ℓ : ℤ) = (ℓ : 𝓞 K) :=
        (map_intCast (algebraMap ℤ (𝓞 K)) (ℓ : ℤ)).trans (Int.cast_natCast ℓ)
      rw [hcast]
      exact v.property
    have hover : v.val.asIdeal.LiesOver p :=
      ⟨hpmax.eq_of_le (inferInstance : (v.val.asIdeal.under ℤ).IsPrime).ne_top hle⟩
    exact ⟨v.val.asIdeal, (mem_primesOverFinset_iff hp₀ _).mpr ⟨v.val.isPrime, hover⟩⟩
  have hf : Function.Injective f := fun x y h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  refine ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact card_primesOverFinset_le_numberField_degree K hp₀

/-- Counting the remaining valuation residues and then the all-zero kernel
bounds the valuation-restricted Kummer classes. -/
theorem finite_card_numberFieldValuationRestrictedPowerClasses_le (K : Type*) [Field K] [NumberField K]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Finite (numberFieldValuationRestrictedPowerClasses K ℓ) ∧
      Nat.card (numberFieldValuationRestrictedPowerClasses K ℓ) ≤
        ℓ ^ (2 * Module.finrank ℚ K) * classNumber K := by
  let _ : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let S := numberFieldValuationRestrictedPowerClasses K ℓ
  let T := {v : HeightOneSpectrum (𝓞 K) // (ℓ : 𝓞 K) ∈ v.asIdeal}
  obtain ⟨hfiniteT, hT⟩ := numberFieldPrimeDivisors_card_le_degree K ℓ
  let _ : Finite T := hfiniteT
  let f : S →* (T → Multiplicative (ZMod ℓ)) :=
    { toFun := fun x v => numberFieldPrincipalValuationResidue K ℓ v.val x.val
      map_one' := funext fun v => map_one (numberFieldPrincipalValuationResidue K ℓ v.val)
      map_mul' := fun x y => funext fun v => map_mul (numberFieldPrincipalValuationResidue K ℓ v.val) x.val y.val }
  let g : f.ker → (numberFieldPrincipalPowerClass K ℓ).ker := fun x => by
    refine ⟨x.val.val, (numberFieldPrincipalPowerClass_eq_one_iff K ℓ x.val.val).mpr ?_⟩
    intro v
    by_cases hv : (ℓ : 𝓞 K) ∈ v.asIdeal
    · exact congrFun (MonoidHom.mem_ker.mp x.property) ⟨v, hv⟩
    · exact (Subgroup.mem_iInf.mp x.val.property) ⟨v, hv⟩
  have hg : Function.Injective g := by
    intro x y h
    have heq : x.val.val = y.val.val :=
      congrArg (fun z : (numberFieldPrincipalPowerClass K ℓ).ker => z.val) h
    exact Subtype.ext (Subtype.ext heq)
  obtain ⟨hfiniteK, hK⟩ := finite_card_numberFieldPrincipalPowerClass_ker_le K ℓ
  let _ := hfiniteK
  have hker : Finite f.ker := Finite.of_injective g hg
  have hkerCard := (Nat.card_le_card_of_injective g hg).trans hK
  have hrange : Finite f.range := inferInstance
  have hrangeCard : Nat.card f.range ≤ ℓ ^ Module.finrank ℚ K := by
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans ?_
    rw [Nat.card_fun]
    change Nat.card (ZMod ℓ) ^ Nat.card T ≤ _
    rw [Nat.card_zmod]
    exact Nat.pow_le_pow_right (NeZero.pos ℓ) hT
  refine ⟨f.finite_iff_finite_ker_range.mpr ⟨hker, hrange⟩, ?_⟩
  rw [← Subgroup.card_ker_mul_card_range f]
  refine (Nat.mul_le_mul hkerCard hrangeCard).trans_eq ?_
  rw [two_mul, pow_add]
  ac_rfl

end Utilities
