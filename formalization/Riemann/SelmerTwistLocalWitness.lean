module

public import Riemann.SelmerTwistNormalization
import Riemann.SelmerStickelbergerReciprocity
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Utilities.SelmerBoundedLocalWitness
import Utilities.AbsoluteCyclotomicInertia
import Utilities.InertiaRestriction
import Utilities.RationalPrime
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

open NumberField Utilities DiscreteGaloisModule groupCohomology
open scoped NumberField Pointwise TensorProduct

namespace Riemann

private theorem isUnit_sub_one_of_primeToResidueOrder {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S]
    {n : ℕ} (hn : IsUnit (n : S)) {z : S} (hz : z ^ n = 1) (hne : z ≠ 1) :
    IsUnit (z - 1) := by
  by_contra hnu
  have hmem : z - 1 ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hnp : (n : S) ∉ IsLocalRing.maximalIdeal S := fun h =>
    (IsLocalRing.mem_maximalIdeal _).mp h hn
  exact hne (eq_of_pow_eq_one_of_sub_mem_prime (IsLocalRing.maximalIdeal S) hnp hz (one_pow _) hmem)

section SharedTwist

variable (F : Type) [Field F] [NumberField F] [IsAbelianGalois ℚ F]
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S]
  (ψ : Gal(F/ℚ) →* Sˣ)

local notation "Ω" => AlgebraicClosure F
local notation "G" => Gal(Ω/ℚ)
local notation "T" => numberFieldSelmerSharedInverseTwist F ℓ i S ψ
local notation "D" => numberFieldSelmerRestrictionsIn ℚ Ω ℓ
local notation "δ" => numberFieldTwistNormalizationElement F
local notation "C" => normalizedSelmerCocycles T D δ
local notation "ρ" => Rep.ρ (DiscreteGaloisModule.rep T)
local instance : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω

/-- Away from ℓ, the inertia action of the shared Tate twist is just the
inverse finite character. -/
theorem sharedTwist_inertia_scalar {P : Ideal (𝓞 Ω)} [P.IsPrime]
    (hP : (ℓ : 𝓞 Ω) ∉ P) {s : G} (hs : s ∈ P.inertia G) :
    ρ s = (((ψ (s.restrictNormal F))⁻¹ : Sˣ) : S) • (1 : Module.End S (T).rep) := by
  rw [numberFieldSelmerSharedInverseTwist_ρ F ℓ i S ψ s,
    padicTateScalarIn_eq_one_of_mem_inertia ℚ Ω ℓ i hP hs, map_one, mul_one]

/-- A locally trivial cocycle vanishes on inertia wherever both the
cyclotomic and the host character actions are trivial. -/
theorem sharedTwistCocycle_eq_zero_on_unramified_inertia
    (c : C) {P : Ideal (𝓞 Ω)} [P.IsPrime] (hne : P ≠ ⊥)
    (hP : (ℓ : 𝓞 Ω) ∉ P)
    (hψ : ∀ s ∈ P.inertia G, ψ (s.restrictNormal F) = 1)
    {s : G} (hs : s ∈ P.inertia G) : c.val s = 0 := by
  obtain ⟨a, ha⟩ := c.property.1.2 (P.inertia G) ⟨P, inferInstance, hne, Or.inl rfl⟩
  have hρ : ρ s = 1 := by
    rw [sharedTwist_inertia_scalar F ℓ i S ψ hP hs, hψ s hs, inv_one, Units.val_one, one_smul]
  rw [ha s hs, hρ, one_apply_eq_self, sub_self]

/-- Decomposition at ℓ and at primes of nontrivial host inertia are the
local groups requiring bounded witnesses in the arithmetic layers. -/
def numberFieldSelmerSharedTwistBadDecompositions : Set (Subgroup G) :=
  { J | ∃ P : Ideal (𝓞 Ω), P.IsPrime ∧ P ≠ ⊥ ∧
      ((ℓ : 𝓞 Ω) ∈ P ∨ ∃ s ∈ P.inertia G, ψ (s.restrictNormal F) ≠ 1) ∧
      J = MulAction.stabilizer G P }

/-- The normalized exponent layer with bounded witnesses at the bad decomposition groups. -/
noncomputable def numberFieldSelmerSharedTwistArithmeticLayer (r : ℕ) : Submodule S C :=
  numberFieldSelmerSharedTwistLayer F ℓ i S ψ r ⊓
    ((T).boundedLocalWitnesses (numberFieldSelmerSharedTwistBadDecompositions F ℓ S ψ)
      ((ℓ : S) ^ r)).comap (Submodule.subtype C)

variable [IsDomain S] [IsLocalRing S]

/-- The inverse host character has unit difference from one at any
nontrivial value when the host degree is prime to the Tate prime. -/
theorem sharedTwist_hostInverse_subOne_isUnit
    (hdegree : ¬ ℓ ∣ Module.finrank ℚ F) {s : G}
    (hψ : ψ (s.restrictNormal F) ≠ 1) :
    IsUnit ((((ψ (s.restrictNormal F))⁻¹ : Sˣ) : S) - 1) := by
  have hp : ℓ.Prime := Fact.out
  let d := Module.finrank ℚ F
  let u := (ψ (s.restrictNormal F))⁻¹
  have hdu : IsUnit (d : S) := by
    have h : IsUnit (d : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr (hp.coprime_iff_not_dvd.mpr hdegree))
    simpa only [map_natCast] using h.map (algebraMap ℤ_[ℓ] S)
  have hsPow : (s.restrictNormal F) ^ d = 1 := by
    change (s.restrictNormal F) ^ Module.finrank ℚ F = 1
    rw [← IsGalois.card_aut_eq_finrank ℚ F]
    exact pow_card_eq_one'
  have hpow : (u : S) ^ d = 1 := by
    change (((ψ (s.restrictNormal F))⁻¹ : Sˣ) : S) ^ d = 1
    rw [← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, hsPow, map_one, inv_one, Units.val_one]
  have hu : (u : S) ≠ 1 := by
    intro hu
    have h := Units.ext (hu.trans (Units.val_one : ((1 : Sˣ) : S) = 1).symm)
    exact hψ (inv_eq_one.mp h)
  exact isUnit_sub_one_of_primeToResidueOrder hdu hpow hu

/-- Nontrivial tame inertia has invertible action minus identity when
the host degree is prime to ℓ. -/
theorem sharedTwist_inertia_subOne_bijective_of_nontrivial
    (hdegree : ¬ ℓ ∣ Module.finrank ℚ F) {P : Ideal (𝓞 Ω)} [P.IsPrime]
    (hℓ : (ℓ : 𝓞 Ω) ∉ P) {s : G} (hs : s ∈ P.inertia G)
    (hψ : ψ (s.restrictNormal F) ≠ 1) :
    Function.Bijective (ρ s - 1 : Module.End S (T).rep) := by
  exact subOne_bijective_of_scalar T s _
    (sharedTwist_inertia_scalar F ℓ i S ψ hℓ hs)
    (sharedTwist_hostInverse_subOne_isUnit F ℓ S ψ hdegree hψ)

/-- Each normalized twist cocycle lies in an exponent layer with uniformly
bounded witnesses at the bad decomposition groups. -/
theorem exists_numberFieldSelmerSharedTwistArithmeticLayer
    (hdegree : ¬ ℓ ∣ Module.finrank ℚ F) (c : C) :
    ∃ r : ℕ, c ∈ numberFieldSelmerSharedTwistArithmeticLayer F ℓ i S ψ r := by
  let _ : IsGalois ℚ Ω := inferInstance
  have hcTate : ∀ x : (T).rep, ∃ n : ℕ, (ℓ : S) ^ n • x = 0 :=
    exists_pow_smul_eq_zero_extendedPadicTate ℓ S
  obtain ⟨m, hm⟩ := normalizedSelmerCocycles_powTorsion T D δ (ℓ : S) hcTate c
  let L := Ideal.span {(ℓ : ℤ)}
  let _ : L.IsMaximal := rationalPrime_isMaximal ℓ
  obtain ⟨P₀, hP₀, hP₀L⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral L (S := 𝓞 Ω)
  let _ : P₀.IsPrime := hP₀.isPrime
  let _ : P₀.LiesOver L := hP₀L
  have hp : ℓ.Prime := Fact.out
  have hL : L ≠ ⊥ := by simpa only [L, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.prime_iff_prime_int.mp hp).ne_zero
  have hP₀ne : P₀ ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hL P₀
  have hℓ₀ : (ℓ : 𝓞 Ω) ∈ P₀ :=
    (natCast_mem_iff_dvd_of_liesOver_rationalPrime P₀ ℓ ℓ).mpr (dvd_refl ℓ)
  obtain ⟨a₀, ha₀⟩ := c.property.1.2 (MulAction.stabilizer G P₀)
    ⟨P₀, hP₀.isPrime, hP₀ne, Or.inr ⟨hℓ₀, rfl⟩⟩
  obtain ⟨n, hn⟩ := hcTate a₀
  let r := max m n
  have hc : (ℓ : S) ^ r • c = 0 := pow_smul_eq_zero_of_le (le_max_left _ _) hm
  have hk (g : G) : (ℓ : S) ^ r • c.val g = 0 :=
    congrArg (fun x : C => x.val g) hc
  have hka : (ℓ : S) ^ r • a₀ = 0 := pow_smul_eq_zero_of_le (le_max_right _ _) hn
  refine ⟨r, ⟨hc, ?_⟩⟩
  rintro _ ⟨P, hprime, hne, hbad, rfl⟩
  let _ : P.IsPrime := hprime
  by_cases hℓ : (ℓ : 𝓞 Ω) ∈ P
  · obtain ⟨s, hs⟩ := exists_galois_smul_prime_eq_of_under_eq P₀ P
      (under_ratPrime_eq_of_mem ℓ P₀ P hℓ₀ hℓ)
    let b := ρ s a₀ - c.val s
    have hb : (ℓ : S) ^ r • b = 0 := by
      change (ℓ : S) ^ r • (ρ s a₀ - c.val s) = 0
      rw [smul_sub, ← map_smul, hka, hk, map_zero, sub_self]
    refine ⟨b, hb, ?_⟩
    let f : cocycles₁ (T).rep := ⟨c.val, c.property.1.1.1⟩
    have hw := (T).coboundary_on_conjugate_subgroup f (MulAction.stabilizer G P₀) s a₀ ha₀
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hs] at hw
    exact hw
  · obtain ⟨s, hs, hψ⟩ := hbad.resolve_left hℓ
    have hinj :=
      (sharedTwist_inertia_subOne_bijective_of_nontrivial F ℓ i S ψ hdegree hℓ hs hψ).injective
    exact (T).exists_bounded_witness_on_stabilizer_of_inertia P c.property.1.1 ((ℓ : S) ^ r) hk
      (c.property.1.2 (P.inertia G) ⟨P, hprime, hne, Or.inl rfl⟩) s hs hinj

omit [IsDomain S] [IsLocalRing S] in
theorem numberFieldSelmerSharedTwistArithmeticLayer_mono :
    Monotone (numberFieldSelmerSharedTwistArithmeticLayer F ℓ i S ψ) := by
  intro m n h
  exact inf_le_inf
    (Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow (ℓ : S) h))
    (Submodule.comap_mono ((T).boundedLocalWitnesses_mono (pow_dvd_pow (ℓ : S) h)))

/-- A uniform valuation bound on the layers with bounded decomposition
witnesses controls the full inverse-twist Selmer length. -/
theorem numberFieldSelmerSharedTwist_log_bound_of_arithmeticLayers
    (hodd : ℓ ≠ 2) (hdegree : ¬ ℓ ∣ Module.finrank ℚ F)
    (hψ : (ψ ((δ).restrictNormal F) : S) = (-1 : S) ^ (i + 1))
    (K : ℝ)
    (h : ∀ r : ℕ,
      let n := Module.length S (numberFieldSelmerSharedTwistArithmeticLayer F ℓ i S ψ r)
      n ≠ ⊤ ∧ (ENat.toNat n : ℝ) * Real.log ℓ ≤ K) :
    Module.length S ((T).selmerKernel D) ≠ ⊤ ∧
      ((Module.length S ((T).selmerKernel D)).toNat : ℝ) * Real.log ℓ ≤ K := by
  have hδ := numberFieldSelmerSharedTwist_normalization_bijective F ℓ i S ψ hodd hψ
  rw [← (normalizedSelmerCocyclesEquiv T D δ hδ).length_eq]
  have hlog : 0 < Real.log (ℓ : ℝ) :=
    Real.log_pos (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt)
  exact length_log_bound_of_uniform_layers _ _ (fun N hN => module_length_le_of_covering_monotone
    (numberFieldSelmerSharedTwistArithmeticLayer F ℓ i S ψ)
    (numberFieldSelmerSharedTwistArithmeticLayer_mono F ℓ i S ψ)
    (exists_numberFieldSelmerSharedTwistArithmeticLayer F ℓ i S ψ hdegree) N hN) hlog K h

end SharedTwist
/-- The conductor embedding makes the host action trivial on inertia away
from that conductor on the common closure. -/
theorem selmerHost_restrictNormal_eq_one_of_inertia_away_conductor
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+) :
    let F := selmerHostField target e q d
    letI : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
    let Ω := AlgebraicClosure F
    ∀ (P : Ideal (𝓞 Ω)) [P.IsPrime],
      (selmerHostConductor target e q d : 𝓞 Ω) ∉ P →
      ∀ s ∈ P.inertia Gal(Ω/ℚ), s.restrictNormal F = 1 := by
  dsimp only
  intro P _ hP s hs
  let F := selmerHostField target e q d
  let Ω := AlgebraicClosure F
  let _ : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  let f := selmerHostConductor target e q d
  let _ : NeZero f := ⟨(selmerHostConductor_pos target e q d).ne'⟩
  obtain ⟨E, hE, -⟩ := exists_selmerHostCyclotomicLayer target e q d f (dvd_refl f)
  let _ : IsCyclotomicExtension {f} ℚ E := hE
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {f} ℚ E
  let ζ := IsCyclotomicExtension.zeta f ℚ E
  have hζ : IsPrimitiveRoot ζ f := IsCyclotomicExtension.zeta_spec f ℚ E
  have he : s.restrictNormal E = 1 := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    change s.restrictNormal E ζ = ζ
    apply (algebraMap E Ω).injective
    rw [s.restrictNormal_commutes E]
    exact inertia_fixes_root_of_order_away ℚ Ω hP hs
      (by rw [← map_pow, hζ.pow_eq_one, map_one])
  change (AlgEquiv.restrictNormalHom F) s = 1
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F E s]
  change (AlgEquiv.restrictNormalHom F) (s.restrictNormal E) = 1
  rw [he, map_one]

/-- The normalized inverse twist vanishes on finite inertia away from the
conductor times the Tate prime. -/
theorem sharedTwistCocycle_eq_zero_away_conductorPrime
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+) (ℓ : ℕ) [Fact ℓ.Prime]
    (i : ℕ) (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S] :
    let F := selmerHostField target e q d
    letI : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
    let Ω := AlgebraicClosure F
    ∀ (ψ : Gal(F/ℚ) →* Sˣ) (c : normalizedSelmerCocycles (numberFieldSelmerSharedInverseTwist F ℓ i S ψ)
      (numberFieldSelmerRestrictionsIn ℚ Ω ℓ) (numberFieldTwistNormalizationElement F))
      (P : Ideal (𝓞 Ω)) [P.IsPrime], P ≠ ⊥ →
        ((selmerHostConductor target e q d * ℓ : ℕ) : 𝓞 Ω) ∉ P →
        ∀ s ∈ P.inertia Gal(Ω/ℚ), c.val s = 0 := by
  dsimp only
  intro ψ c P _ hne hP s hs
  let F := selmerHostField target e q d
  let Ω := AlgebraicClosure F
  let _ : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  let f := selmerHostConductor target e q d
  have hℓ : (ℓ : 𝓞 Ω) ∉ P := fun h =>
    hP (by rw [Nat.cast_mul]; exact P.mul_mem_left (f : 𝓞 Ω) h)
  have hf : (f : 𝓞 Ω) ∉ P := fun h =>
    hP (by rw [Nat.cast_mul]; exact P.mul_mem_right (ℓ : 𝓞 Ω) h)
  refine sharedTwistCocycle_eq_zero_on_unramified_inertia F ℓ i S ψ c hne hℓ ?_ hs
  intro g hg
  rw [selmerHost_restrictNormal_eq_one_of_inertia_away_conductor target e q d P hf g hg, map_one]

/-- The normalized Bernoulli length bound for a single arithmetic layer. -/
def SelmerSharedTwistArithmeticBernoulliBound
    (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))
    (ψ : Gal((selmerHostField target e q d)/ℚ) →* Oˣ) (m : ℕ) : Prop :=
  let F := selmerHostField target e q d
  letI : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  let f := selmerHostConductor target e q d
  let n := Module.length O (numberFieldSelmerSharedTwistArithmeticLayer F ℓ i O ψ m)
  let r := Module.length O (O ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] O))
  n ≠ ⊤ ∧ (ENat.toNat n : ℝ) * Real.log ℓ ≤ (ENat.toNat r : ℝ) *
    (-Real.log ‖(generalizedBernoulliDenominator f (i + 1) : PadicAlgCl ℓ) *
      primitiveBernoulliValue (i + 1) (selmerDirichletOfCharacter target e q d ℓ O O.val.toRingHom ψ)‖)

/-- The uniform arithmetic bound with bounded witnesses in the decomposition
groups at the Tate prime and at the primes of nontrivial host inertia. -/
def HasSelmerSharedTwistArithmeticBernoulliComparison : Prop :=
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
            ∀ m : ℕ, SelmerSharedTwistArithmeticBernoulliBound target e q d ℓ i O ψ m

/-- A bound on the layers with bounded local witnesses gives the exact
Bernoulli comparison required for the inverse twists. -/
theorem selmerSharedTwistBernoulliComparison_of_arithmeticLayers
    (h : HasSelmerSharedTwistArithmeticBernoulliComparison) : HasSelmerSharedTwistBernoulliComparison := by
  intro target ht e q d he hp i hi
  dsimp only
  intro ℓ _ hodd hdegree O _ _ _ ψ hψ
  let F := selmerHostField target e q d
  let _ : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
  have hδ := numberFieldTwistNormalizationElement_restrictNormal_host target e q d
  apply numberFieldSelmerSharedTwist_log_bound_of_arithmeticLayers F ℓ i O ψ hodd hdegree
  · rw [hδ]
    exact hψ
  · exact h target ht e q d he hp i hi ℓ hodd hdegree O ψ hψ

end Riemann
