module

public import Utilities.IdealPairCounting
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Utilities.RationalPrime
import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open Filter Ideal IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors Topology

namespace Utilities

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]

local notation:max "Primes" F:max => HeightOneSpectrum (𝓞 F)
local notation:max "Ideals" F:max => (Ideal (𝓞 F))⁰

/-- The prime exponents of a nonzero integral ideal, with finite support. -/
noncomputable def integralIdealPrimeExponents (I : Ideals K) : Primes K →₀ ℕ := by
  classical
  have hI : I.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  let n (v : Primes K) := (Associates.mk v.asIdeal).count (Associates.mk I.val).factors
  refine Finsupp.mk (Ideal.finite_factors hI).toFinset n fun v => ?_
  rw [Set.Finite.mem_toFinset]
  exact (Associates.count_ne_zero_iff_dvd hI v.irreducible).symm

theorem integralIdealPrimeExponents_prod (I : Ideals K) :
    (integralIdealPrimeExponents K I).prod (fun v n => heightOnePrimeIdeal K v ^ n) = I := by
  classical
  let n := integralIdealPrimeExponents K I
  have hI : I.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  apply Subtype.ext
  change (nonZeroDivisors (Ideal (𝓞 K))).subtype (∏ v ∈ n.support, heightOnePrimeIdeal K v ^ n v) = I.val
  rw [map_prod]
  simp only [map_pow]
  have hfac := Ideal.finprod_heightOneSpectrum_factorization hI
  rw [finprod_eq_finsetProd_of_mulSupport_subset _ (s := n.support)] at hfac
  · exact hfac
  · intro v hv
    change v ∈ n.support
    rw [Finsupp.mem_support_iff]
    intro hzero
    apply hv
    change v.asIdeal ^ n v = 1
    rw [hzero, pow_zero]

theorem integralIdealPrimeExponents_support_subset_of_avoids
    {s : Set (Primes K)} {I : Ideals K} (h : integralIdealAvoids K s I) :
    ((integralIdealPrimeExponents K I).support : Set (Primes K)) ⊆ sᶜ := by
  classical
  intro v hv hs
  have hI : I.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hv' : integralIdealPrimeExponents K I v ≠ 0 := Finsupp.mem_support_iff.mp hv
  change (Associates.mk v.asIdeal).count (Associates.mk I.val).factors ≠ 0 at hv'
  exact h v hs (nonZeroDivisors_dvd_iff_dvd_coe.mpr
    ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hv'))

/-- Transport the prime powers of an ideal along a map of the prime sets. -/
noncomputable def transportIntegralIdealPrimes (e : Primes K → Primes L) (I : Ideals K) : Ideals L :=
  (integralIdealPrimeExponents K I).prod (fun v n => heightOnePrimeIdeal L (e v) ^ n)

theorem transportIntegralIdealPrimes_absNorm_of_support (e : Primes K → Primes L)
    (I : Ideals K) (he : ∀ v ∈ (integralIdealPrimeExponents K I).support,
      absNorm (e v).asIdeal = absNorm v.asIdeal) :
    absNorm (transportIntegralIdealPrimes K L e I).val = absNorm I.val := by
  let n := integralIdealPrimeExponents K I
  have hI := congrArg (fun J : Ideals K => absNorm J.val) (integralIdealPrimeExponents_prod K I)
  change (absNorm.toMonoidHom.comp (nonZeroDivisors (Ideal (𝓞 K))).subtype)
    (∏ v ∈ n.support, heightOnePrimeIdeal K v ^ n v) = _ at hI
  change (absNorm.toMonoidHom.comp (nonZeroDivisors (Ideal (𝓞 L))).subtype)
    (∏ v ∈ n.support, heightOnePrimeIdeal L (e v) ^ n v) = _
  rw [map_prod] at hI ⊢
  rw [← hI]
  apply Finset.prod_congr rfl
  intro v hv
  rw [map_pow, map_pow]
  exact congrArg (· ^ n v) (he v hv)

theorem transportIntegralIdealPrimes_absNorm (e : Primes K → Primes L)
    (he : ∀ v, absNorm (e v).asIdeal = absNorm v.asIdeal) (I : Ideals K) :
    absNorm (transportIntegralIdealPrimes K L e I).val = absNorm I.val :=
  transportIntegralIdealPrimes_absNorm_of_support K L e I (fun v _ => he v)

open scoped Classical in
private theorem count_transportIntegralIdealPrimes (e : Primes K → Primes L)
    (I : Ideals K) (w : Primes L) :
    FractionalIdeal.count L w ((transportIntegralIdealPrimes K L e I).val :
      FractionalIdeal (𝓞 L)⁰ L) =
      ∑ v ∈ (integralIdealPrimeExponents K I).support,
        if e v = w then ((integralIdealPrimeExponents K I v : ℕ) : ℤ) else 0 := by
  classical
  let n := integralIdealPrimeExponents K I
  let castIdeal : Ideals L →* FractionalIdeal (𝓞 L)⁰ L :=
    (FractionalIdeal.coeIdealHom (𝓞 L)⁰ L).toMonoidHom.comp (nonZeroDivisors (Ideal (𝓞 L))).subtype
  change FractionalIdeal.count L w (castIdeal (∏ v ∈ n.support, heightOnePrimeIdeal L (e v) ^ n v)) = _
  rw [map_prod, FractionalIdeal.count_prod]
  · apply Finset.sum_congr rfl
    intro v _
    rw [map_pow, FractionalIdeal.count_pow]
    change (n v : ℤ) * FractionalIdeal.count L w ((e v).asIdeal : FractionalIdeal (𝓞 L)⁰ L) = _
    rw [FractionalIdeal.count_maximal]
    split_ifs <;> simp [n]
  · intro v _
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp
      (heightOnePrimeIdeal L (e v) ^ n v).property)

/-- Two disjoint norm-preserving copies of all primes outside a summable
exceptional set would give a norm-preserving injection of ideal pairs. -/
theorem not_disjoint_normPreserving_primeMaps_off_summable
    (s : Set (Primes K)) (hs : Summable (fun v : s => (absNorm v.val.asIdeal : ℝ)⁻¹))
    (e₀ e₁ : Primes K → Primes L)
    (hi₀ : Set.InjOn e₀ sᶜ) (hi₁ : Set.InjOn e₁ sᶜ)
    (hdis : Disjoint (e₀ '' sᶜ) (e₁ '' sᶜ))
    (hn₀ : ∀ v ∉ s, absNorm (e₀ v).asIdeal = absNorm v.asIdeal)
    (hn₁ : ∀ v ∉ s, absNorm (e₁ v).asIdeal = absNorm v.asIdeal) : False := by
  classical
  let A := {I : Ideals K // integralIdealAvoids K s I}
  let norm (I : A) := absNorm I.val.val
  have hf (x : ℝ) (hx : 0 ≤ x) : Finite {I : A // (norm I : ℝ) ≤ x} := by
    let _ := finite_nonzeroIntegralIdeals_norm_le K x hx
    exact Finite.of_injective
      (fun I : {I : A // (norm I : ℝ) ≤ x} =>
        (⟨I.val.val, I.property⟩ : {I : Ideals K // (absNorm I.val : ℝ) ≤ x}))
      (fun _ _ h => Subtype.ext (Subtype.ext
        (congrArg (fun I : {I : Ideals K // (absNorm I.val : ℝ) ≤ x} => I.val) h)))
  obtain ⟨d, hd, hcount⟩ := eventually_card_boundedClassIdealsAvoiding_div_ge K s hs 1
  have hA : ∀ᶠ x : ℝ in atTop, d ≤ (Nat.card {I : A // (norm I : ℝ) ≤ x} : ℝ) / x := by
    filter_upwards [hcount, eventually_gt_atTop (0 : ℝ)] with x hx hx₀
    let _ := hf x hx₀.le
    have hcard : Nat.card (boundedClassIdealsAvoiding K s 1 x) ≤ Nat.card {I : A // (norm I : ℝ) ≤ x} :=
      Nat.card_le_card_of_injective
        (fun I : boundedClassIdealsAvoiding K s 1 x =>
          (⟨⟨I.val, I.property.2.2⟩, I.property.1⟩ : {I : A // (norm I : ℝ) ≤ x}))
        (fun _ _ h => Subtype.ext (congrArg (fun I : {I : A // (norm I : ℝ) ≤ x} => I.val.val) h))
    exact hx.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hcard) hx₀.le)
  let T (e : Primes K → Primes L) (I : A) := transportIntegralIdealPrimes K L e I.val
  let f (P : A × A) := T e₀ P.1 * T e₁ P.2
  have hsupp (I : A) : ((integralIdealPrimeExponents K I.val).support : Set (Primes K)) ⊆ sᶜ :=
    integralIdealPrimeExponents_support_subset_of_avoids K I.property
  have hn (I J : A) : absNorm (f (I, J)).val = norm I * norm J := by
    change absNorm ((T e₀ I).val * (T e₁ J).val) = _
    rw [map_mul, transportIntegralIdealPrimes_absNorm_of_support K L e₀ I.val (fun v hv => hn₀ v (hsupp I hv)),
      transportIntegralIdealPrimes_absNorm_of_support K L e₁ J.val (fun v hv => hn₁ v (hsupp J hv))]
  apply not_injective_pair_of_norm_mul_of_eventually_linear_lower_count norm
    (fun I => absNorm_pos_of_nonZeroDivisors I.val) hf hd hA L f hn
  have hself (e : Primes K → Primes L) (he : Set.InjOn e sᶜ) (I : A) (v : Primes K) (hv : v ∉ s) :
      FractionalIdeal.count L (e v) ((T e I).val : FractionalIdeal (𝓞 L)⁰ L) =
        (integralIdealPrimeExponents K I.val v : ℤ) := by
    change FractionalIdeal.count L (e v) ((transportIntegralIdealPrimes K L e I.val).val :
      FractionalIdeal (𝓞 L)⁰ L) = _
    rw [count_transportIntegralIdealPrimes]
    have hh (w : Primes K) (hw : w ∈ (integralIdealPrimeExponents K I.val).support) :
        e w = e v ↔ w = v := ⟨he (hsupp I hw) hv, congrArg e⟩
    calc
      _ = ∑ w ∈ (integralIdealPrimeExponents K I.val).support,
          if w = v then ((integralIdealPrimeExponents K I.val w : ℕ) : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [hh w hw]
      _ = _ := by
        by_cases hv' : integralIdealPrimeExponents K I.val v = 0 <;>
          simp [Finset.sum_ite_eq', Finsupp.mem_support_iff, hv']
  have hcross {e e' : Primes K → Primes L} (h : Disjoint (e '' sᶜ) (e' '' sᶜ))
      (I : A) (v : Primes K) (hv : v ∉ s) :
      FractionalIdeal.count L (e' v) ((T e I).val : FractionalIdeal (𝓞 L)⁰ L) = 0 := by
    change FractionalIdeal.count L (e' v) ((transportIntegralIdealPrimes K L e I.val).val :
      FractionalIdeal (𝓞 L)⁰ L) = _
    rw [count_transportIntegralIdealPrimes]
    apply Finset.sum_eq_zero
    intro w hw
    have hne : e w ≠ e' v := fun he =>
      (Set.disjoint_left.mp h ⟨w, hsupp I hw, rfl⟩) ⟨v, hv, he.symm⟩
    rw [ite_eq_right hne]
  have hread (P : A × A) (w : Primes L) :
      FractionalIdeal.count L w ((f P).val : FractionalIdeal (𝓞 L)⁰ L) =
        FractionalIdeal.count L w ((T e₀ P.1).val : FractionalIdeal (𝓞 L)⁰ L) +
        FractionalIdeal.count L w ((T e₁ P.2).val : FractionalIdeal (𝓞 L)⁰ L) := by
    change FractionalIdeal.count L w (((T e₀ P.1).val * (T e₁ P.2).val : Ideal (𝓞 L)) :
      FractionalIdeal (𝓞 L)⁰ L) = _
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul]
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp (T e₀ P.1).property)
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp (T e₁ P.2).property)
  intro P Q he
  have hcounts (w : Primes L) :
      FractionalIdeal.count L w ((f P).val : FractionalIdeal (𝓞 L)⁰ L) =
      FractionalIdeal.count L w ((f Q).val : FractionalIdeal (𝓞 L)⁰ L) := by
    rw [he]
  have hoff (I : A) (v : Primes K) (hv : v ∈ s) : integralIdealPrimeExponents K I.val v = 0 :=
    Finsupp.notMem_support_iff.mp (fun h => hsupp I h hv)
  have h₀ : integralIdealPrimeExponents K P.1.val = integralIdealPrimeExponents K Q.1.val := by
    ext v
    by_cases hv : v ∈ s
    · rw [hoff _ _ hv, hoff _ _ hv]
    · have h := hcounts (e₀ v)
      rw [hread, hread] at h
      simpa only [hself e₀ hi₀ _ _ hv, hcross hdis.symm _ _ hv, add_zero, Int.natCast_inj] using h
  have h₁ : integralIdealPrimeExponents K P.2.val = integralIdealPrimeExponents K Q.2.val := by
    ext v
    by_cases hv : v ∈ s
    · rw [hoff _ _ hv, hoff _ _ hv]
    · have h := hcounts (e₁ v)
      rw [hread, hread] at h
      simpa only [hself e₁ hi₁ _ _ hv, hcross hdis _ _ hv, zero_add, Int.natCast_inj] using h
  apply Prod.ext <;> apply Subtype.ext
  · simpa only [integralIdealPrimeExponents_prod] using congrArg
      (fun n : Primes K →₀ ℕ => n.prod fun v e => heightOnePrimeIdeal K v ^ e) h₀
  · simpa only [integralIdealPrimeExponents_prod] using congrArg
      (fun n : Primes K →₀ ℕ => n.prod fun v e => heightOnePrimeIdeal K v ^ e) h₁

/-- Two disjoint norm-preserving copies of the prime ideals of one number
field cannot both occur in the prime ideals of another. -/
theorem not_disjoint_normPreserving_primeEmbeddings (e₀ e₁ : Primes K ↪ Primes L)
    (hdis : Disjoint (Set.range e₀) (Set.range e₁))
    (hn₀ : ∀ v, absNorm (e₀ v).asIdeal = absNorm v.asIdeal)
    (hn₁ : ∀ v, absNorm (e₁ v).asIdeal = absNorm v.asIdeal) : False := by
  let _ : Finite (↥(∅ : Set (Primes K))) := Set.finite_empty.to_subtype
  exact not_disjoint_normPreserving_primeMaps_off_summable K L ∅ Summable.of_finite
    e₀ e₁ e₀.injective.injOn e₁.injective.injOn (by simpa using hdis)
    (fun v _ => hn₀ v) (fun v _ => hn₁ v)

/-- A set of primes with summable inverse norms cannot contain all
exceptions to the existence of two norm-preserving primes above a base prime. -/
theorem not_forall_two_normPreserving_primesOver_off_summable [Algebra K L]
    (s : Set (Primes K)) (hs : Summable (fun v : s => (absNorm v.val.asIdeal : ℝ)⁻¹))
    (h : ∀ v : Primes K, v ∉ s → ∃ w₀ w₁ : Primes L,
      w₀ ≠ w₁ ∧ w₀.asIdeal.under (𝓞 K) = v.asIdeal ∧ w₁.asIdeal.under (𝓞 K) = v.asIdeal ∧
      absNorm w₀.asIdeal = absNorm v.asIdeal ∧ absNorm w₁.asIdeal = absNorm v.asIdeal) : False := by
  classical
  choose w₀ w₁ hne hu₀ hu₁ hn₀ hn₁ using h
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : p.IsMaximal := rationalPrime_isMaximal 2
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral p (S := 𝓞 L)
  let _ : Q.LiesOver p := hQp
  have hp₀ : p ≠ ⊥ := by simp [p]
  let w : Primes L := ⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot hp₀ Q⟩
  let e₀ (v : Primes K) := if hv : v ∈ s then w else w₀ v hv
  let e₁ (v : Primes K) := if hv : v ∈ s then w else w₁ v hv
  have he₀ (v : Primes K) (hv : v ∉ s) : e₀ v = w₀ v hv := dite_eq_right hv
  have he₁ (v : Primes K) (hv : v ∉ s) : e₁ v = w₁ v hv := dite_eq_right hv
  have hmap_inj (e : Primes K → Primes L)
      (he : ∀ v ∉ s, (e v).asIdeal.under (𝓞 K) = v.asIdeal) : Set.InjOn e sᶜ := by
    intro v hv u hu eq
    exact HeightOneSpectrum.ext ((he v hv).symm.trans
      ((congrArg (fun w : Primes L => w.asIdeal.under (𝓞 K)) eq).trans (he u hu)))
  have hdis : Disjoint (e₀ '' sᶜ) (e₁ '' sᶜ) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ ⟨u, hu, he⟩
    rw [he₁ u hu, he₀ v hv] at he
    have huv : u = v := HeightOneSpectrum.ext ((hu₁ u hu).symm.trans
      ((congrArg (fun w : Primes L => w.asIdeal.under (𝓞 K)) he).trans (hu₀ v hv)))
    subst u
    exact hne v hv he.symm
  refine not_disjoint_normPreserving_primeMaps_off_summable K L s hs e₀ e₁ ?_ ?_ hdis ?_ ?_
  · exact hmap_inj e₀ (fun v hv => by rw [he₀ v hv]; exact hu₀ v hv)
  · exact hmap_inj e₁ (fun v hv => by rw [he₁ v hv]; exact hu₁ v hv)
  · exact fun v hv => by rw [he₀ v hv]; exact hn₀ v hv
  · exact fun v hv => by rw [he₁ v hv]; exact hn₁ v hv

/-- In an extension of number fields there cannot be two distinct primes of
unchanged norm above every prime of the base field. -/
theorem not_forall_two_normPreserving_primesOver [Algebra K L]
    (h : ∀ v : Primes K, ∃ w₀ w₁ : Primes L,
      w₀ ≠ w₁ ∧ w₀.asIdeal.under (𝓞 K) = v.asIdeal ∧ w₁.asIdeal.under (𝓞 K) = v.asIdeal ∧
      absNorm w₀.asIdeal = absNorm v.asIdeal ∧ absNorm w₁.asIdeal = absNorm v.asIdeal) : False := by
  let _ : Finite (↥(∅ : Set (Primes K))) := Set.finite_empty.to_subtype
  exact not_forall_two_normPreserving_primesOver_off_summable K L ∅
    Summable.of_finite (fun v _ => h v)

end Utilities
