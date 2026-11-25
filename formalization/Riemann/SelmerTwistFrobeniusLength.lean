module

public import Riemann.SelmerTwistConductor
public import Utilities.PadicTateCoefficientLength
import Utilities.SelmerDecomposition

@[expose] public section

open NumberField Utilities DiscreteGaloisModule IsDiscreteValuationRing
open scoped NumberField Pointwise TensorProduct

namespace Riemann

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 500000

variable (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
  (ℓ : ℕ) [Fact ℓ.Prime] (i r : ℕ) (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ))

local notation "F" => selmerHostField target e q d
local notation "Ω" => AlgebraicClosure F
local notation "G" => Gal(Ω/ℚ)
local instance : IsAbelianGalois ℚ F := selmerHostField_isAbelianGalois target e q d
local instance : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω

variable (ψ : Gal((selmerHostField target e q d)/ℚ) →* Oˣ)
local notation "T" => numberFieldSelmerSharedInverseTwist F ℓ i O ψ
local notation "C" => normalizedSelmerCocycles T (numberFieldSelmerRestrictionsIn ℚ Ω ℓ)
  (numberFieldTwistNormalizationElement F)
local notation "cnd" => DirichletCharacter.conductor
  (selmerDirichletOfCharacter target e q d ℓ O (AlgHom.toRingHom (Subalgebra.val O)) ψ)

/-- Evaluation as a linear map on normalized cocycles. -/
noncomputable def sharedTwistNormalizedCocycles_eval (g : G) : C →ₗ[O] (T).rep :=
  (LinearMap.proj g).comp (Submodule.subtype C)

local notation "ev" => sharedTwistNormalizedCocycles_eval target e q d ℓ i O ψ

/-- The submodule of normalized cocycles vanishing on a subgroup. -/
noncomputable def sharedTwistNormalizedCocycles_vanishingOn (J : Subgroup G) : Submodule O C :=
  ⨅ g : J, LinearMap.ker (ev g.val)

local notation "van" => sharedTwistNormalizedCocycles_vanishingOn target e q d ℓ i O ψ
local notation "Dec" => MulAction.stabilizer G

/-- At a prime away from the conductor and Tate prime, testing a normalized
cocycle on a Frobenius generator is equivalent to vanishing on decomposition. -/
theorem sharedTwistNormalizedCocycles_mem_vanishingOn_iff
    (c : C) (P : Ideal (𝓞 Ω)) [P.IsPrime] (hne : P ≠ ⊥)
    (haway : ((cnd * ℓ : ℕ) : 𝓞 Ω) ∉ P) (φ : Dec P)
    (hdense : Dense (Subgroup.zpowers (QuotientGroup.mk' (P.inertia (Dec P)) φ) :
      Set (Dec P ⧸ P.inertia (Dec P)))) :
    c ∈ van (Dec P) ↔ c.val φ.val = 0 := by
  constructor
  · intro hc
    exact (iInf_le (fun g : Dec P => (ev g.val).ker) φ) hc
  · intro hc
    rw [sharedTwistNormalizedCocycles_vanishingOn, Submodule.mem_iInf]
    intro g
    change c.val g.val = 0
    have hcoc := (T).restrict_mem_continuousCocycles₁ (Dec P) c.property.1.1
    refine ((T).restrictToSubgroup (Dec P)).cocycle_eq_zero_of_vanishes_on_dense_generators
      hcoc (P.inertia (Dec P)) φ (dense_sup_zpowers_of_dense_quotient _ _ hdense) ?_ hc g
    intro s hs
    exact sharedTwistCocycle_eq_zero_away_primitiveConductorPrime target e q d ℓ O i ψ c P
      hne haway (P.coe_mem_inertia.mpr hs)

/-- An annihilator of evaluation bounds the length lost when imposing
conditions satisfied by every cocycle in the evaluation kernel. -/
theorem sharedTwist_eval_length_step
    [IsDiscreteValuationRing O] [Module.Flat ℤ_[ℓ] O] {V U : Submodule O C}
    (hU : U ≤ V) (g : G) (hker : ∀ c : V, ev g c.val = 0 → c.val ∈ U)
    (a b : O) (hb : b ∣ (ℓ : O) ^ r)
    (hkill : ∀ c : V, b • ev g c.val = 0) (hdetect : ∃ c : V, ev g c.val ≠ 0) :
    0 < IsDiscreteValuationRing.addVal O b ∧
      Module.length O V + IsDiscreteValuationRing.addVal O a ≤
        Module.length O U + IsDiscreteValuationRing.addVal O (a * b) := by
  let f := (ev g).comp V.subtype
  let u : U →ₗ[O] V := Submodule.inclusion hU
  have hk : f.ker ≤ u.range := by
    intro c hc
    exact ⟨⟨c.val, hker c hc⟩, Subtype.ext rfl⟩
  have hℓ : (ℓ : O) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have ht : Module.length O (Submodule.torsionBy O (T).rep b) = IsDiscreteValuationRing.addVal O b :=
    extendedPadicTate_length_torsionBy_of_dvd_pow ℓ O hℓ r hb
  exact dvr_length_add_addVal_le_of_evaluation f u hk ht.le hkill hdetect

/-- The local length step for Frobenius counting. An annihilator of the
evaluation controls the loss in length when adding a decomposition condition. -/
theorem sharedTwist_frobenius_length_step
    [IsDiscreteValuationRing O] [Module.Flat ℤ_[ℓ] O]
    (V : Submodule O C) (P : Ideal (𝓞 Ω)) [P.IsPrime] (hne : P ≠ ⊥)
    (haway : ((cnd * ℓ : ℕ) : 𝓞 Ω) ∉ P) (φ : Dec P)
    (hdense : Dense (Subgroup.zpowers (QuotientGroup.mk' (P.inertia (Dec P)) φ) :
      Set (Dec P ⧸ P.inertia (Dec P))))
    (a b : O) (hb : b ∣ (ℓ : O) ^ r)
    (hkill : ∀ c : V, b • ev φ.val c.val = 0) (hdetect : ∃ c : V, ev φ.val c.val ≠ 0) :
    0 < IsDiscreteValuationRing.addVal O b ∧
      Module.length O V + IsDiscreteValuationRing.addVal O a ≤
        Module.length O (V ⊓ van (Dec P) : Submodule O C) + IsDiscreteValuationRing.addVal O (a * b) := by
  apply sharedTwist_eval_length_step target e q d ℓ i r O ψ inf_le_left φ.val ?_ a b hb hkill hdetect
  intro c hc
  exact ⟨c.property,
    (sharedTwistNormalizedCocycles_mem_vanishingOn_iff target e q d ℓ i O ψ c.val P
      hne haway φ hdense).mpr hc⟩

/-- One permitted arithmetic transition cuts by a new decomposition group.
The coefficient annihilates evaluation at a Frobenius generator and the
evaluation detects a nonzero class. -/
def SharedTwistFrobeniusStep (V W : Submodule O C) (b : O) : Prop :=
  ∃ (P : Ideal (𝓞 Ω)) (_ : P.IsPrime) (φ : Dec P), P ≠ ⊥ ∧
    ((cnd * ℓ : ℕ) : 𝓞 Ω) ∉ P ∧
    Dense (Subgroup.zpowers (QuotientGroup.mk' (P.inertia (Dec P)) φ) :
      Set (Dec P ⧸ P.inertia (Dec P))) ∧
    W = V ⊓ van (Dec P) ∧ b ∣ (ℓ : O) ^ r ∧
    (∀ x : V, b • ev φ.val x.val = 0) ∧ (∃ x : V, ev φ.val x.val ≠ 0)

theorem SharedTwistFrobeniusStep.length_step
    [IsDiscreteValuationRing O] [Module.Flat ℤ_[ℓ] O]
    {V W : Submodule O C} {b : O}
    (h : SharedTwistFrobeniusStep target e q d ℓ i r O ψ V W b) (a : O) :
    0 < addVal O b ∧ Module.length O V + addVal O a ≤ Module.length O W + addVal O (a * b) := by
  obtain ⟨P, hP, φ, hP₀, haway, hdense, hW, hb, hkill, hdetect⟩ := h
  have : P.IsPrime := hP
  obtain ⟨hpos, hlen⟩ := sharedTwist_frobenius_length_step target e q d ℓ i r O ψ
    V P hP₀ haway φ hdense a b hb hkill hdetect
  have he := congrArg (fun U : Submodule O C => Module.length O U + addVal O (a * b)) hW.symm
  exact ⟨hpos, hlen.trans he.le⟩

/-- A family of reachable Frobenius steps starting at the arithmetic layer.
The product of the successive evaluation annihilators divides a common
coefficient, which bounds the total length lost. -/
def HasSharedTwistFrobeniusBudget (bound : O) : Prop :=
  ∃ (I : Type) (V : I → Submodule O C) (a : I → O) (start : I),
    V start = numberFieldSelmerSharedTwistArithmeticLayer F ℓ i O ψ r ∧
    a start = 1 ∧ (∀ j, a j ∣ bound) ∧
    ∀ j, V j ≠ ⊥ → ∃ k b, a k = a j * b ∧
      SharedTwistFrobeniusStep target e q d ℓ i r O ψ (V j) (V k) b

/-- Every permitted stage either has length zero or increases the bounded
valuation. The initial length is therefore bounded by the final budget. -/
theorem sharedTwist_arithmeticLayer_length_le_of_frobeniusBudget
    [IsDiscreteValuationRing O] [Module.Flat ℤ_[ℓ] O]
    (bound : O) (hbound : bound ≠ 0)
    (h : HasSharedTwistFrobeniusBudget target e q d ℓ i r O ψ bound) :
    Module.length O (numberFieldSelmerSharedTwistArithmeticLayer F ℓ i O ψ r) ≤
      IsDiscreteValuationRing.addVal O bound := by
  obtain ⟨I, V, a, start, hstart, hunit, hdiv, hstep⟩ := h
  have hind := module_length_add_rank_le_of_bounded_steps V (fun j => addVal O (a j))
    (addVal O bound) (addVal_eq_top_iff.not.mpr hbound)
    (fun j => addVal_le_iff_dvd.mpr (hdiv j)) (fun j hj => ?_) start
  · rwa [hstart, hunit, addVal_one, add_zero] at hind
  · obtain ⟨k, b, hk, hs⟩ := hstep j hj
    obtain ⟨hpos, hlen⟩ := SharedTwistFrobeniusStep.length_step target e q d ℓ i r O ψ hs (a j)
    refine ⟨k, ?_, ?_⟩
    · have h₀ : addVal O (a j) ≠ ⊤ :=
        ne_top_of_le_ne_top (addVal_eq_top_iff.not.mpr hbound) (addVal_le_iff_dvd.mpr (hdiv j))
      rw [hk, addVal_mul]
      have hh : addVal O (a j) + (0 : ℕ∞) < addVal O (a j) + addVal O b :=
        WithTop.add_lt_add_left h₀ hpos
      rwa [add_zero] at hh
    · have he := congrArg (fun z : O => Module.length O (V k) + addVal O z) hk.symm
      exact hlen.trans he.le

end Riemann
