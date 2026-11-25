module

public import Riemann.SelmerTwistFrobeniusLength
public import Riemann.SelmerTwistFiniteDescent
public import Utilities.FrobeniusGeneration
import Utilities.SplitPrimeRoots

@[expose] public section

open NumberField Utilities DiscreteGaloisModule groupCohomology
open scoped NumberField Pointwise

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
local notation "ev" => sharedTwistNormalizedCocycles_eval target e q d ℓ i O ψ
local notation "van" => sharedTwistNormalizedCocycles_vanishingOn target e q d ℓ i O ψ
local notation "Dec" => MulAction.stabilizer G

/-- At a prime splitting the finite coefficient field, the decomposition
group acts trivially on the bounded Tate coefficients. -/
theorem sharedTwist_action_eq_self_at_splitPrime {p : ℕ} [Fact p.Prime]
    (hp : p ≡ 1 [MOD cnd * ℓ ^ r]) (P : Ideal (𝓞 Ω)) [P.IsPrime]
    (hP : (p : 𝓞 Ω) ∈ P) {g : G} (hg : g ∈ Dec P)
    (x : (T).rep) (hx : (ℓ : O) ^ r • x = 0) :
    (T).rep.ρ g x = x := by
  let _ : P.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_rationalPrime_of_mem P p hP
  have hfix {n : ℕ} (hn : n ∣ cnd * ℓ ^ r) {z : Ω} (hz : z ^ n = 1) : g z = z :=
    stabilizer_fixes_root_of_modEq_one P (hp.of_dvd hn) hg hz
  exact sharedTwist_action_eq_self_of_fixes_roots F ℓ i O ψ r g
    (selmerHostCharacter_eq_one_of_fixes_conductor_roots target e q d ℓ O ψ g
      (fun _ => hfix (dvd_mul_right _ _)))
    (fun _ => hfix (dvd_mul_left _ _)) x hx

/-- Impose vanishing on the decomposition groups of every prime above a
given rational prime. -/
noncomputable def sharedTwistNormalizedCocycles_vanishingAtRationalPrime (p : ℕ) : Submodule O C :=
  ⨅ P : {P : Ideal (𝓞 Ω) // P.IsPrime ∧ (p : 𝓞 Ω) ∈ P}, van (Dec P.val)

local notation "vanRat" => sharedTwistNormalizedCocycles_vanishingAtRationalPrime target e q d ℓ i O ψ

/-- For a bounded cocycle and a split prime, vanishing on the decomposition
group at one prime propagates to all primes over the same rational prime. -/
theorem sharedTwistNormalizedCocycles_mem_vanishingAtRationalPrime_iff {p : ℕ} [Fact p.Prime]
    (hp : p ≡ 1 [MOD cnd * ℓ ^ r])
    (c : C) (hc : (ℓ : O) ^ r • c = 0)
    (P : Ideal (𝓞 Ω)) [P.IsPrime] (hP : (p : 𝓞 Ω) ∈ P) :
    c ∈ vanRat p ↔ c ∈ van (Dec P) := by
  constructor
  · intro h
    exact (iInf_le (fun Q : {Q : Ideal (𝓞 Ω) // Q.IsPrime ∧ (p : 𝓞 Ω) ∈ Q} =>
      van (Dec Q.val)) ⟨P, inferInstance, hP⟩) h
  · intro h
    rw [sharedTwistNormalizedCocycles_vanishingOn, Submodule.mem_iInf] at h
    rw [sharedTwistNormalizedCocycles_vanishingAtRationalPrime, Submodule.mem_iInf]
    intro Q
    let _ : Q.val.IsPrime := Q.property.1
    obtain ⟨s, hs⟩ := exists_galois_smul_prime_eq_of_under_eq P Q.val
      (under_ratPrime_eq_of_mem p P Q.val hP Q.property.2)
    let f : cocycles₁ (T).rep := ⟨c.val, c.property.1.1.1⟩
    have hz : ∀ g ∈ Dec P, f.val g = (T).rep.ρ g 0 - 0 := by
      intro g hg
      have hgz : c.val g = 0 := h ⟨g, hg⟩
      simpa only [map_zero, sub_zero] using hgz
    have hw := (T).coboundary_on_conjugate_subgroup f (Dec P) s 0 hz
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hs] at hw
    rw [sharedTwistNormalizedCocycles_vanishingOn, Submodule.mem_iInf]
    intro g
    change c.val g.val = 0
    have ht : (ℓ : O) ^ r • c.val s = 0 := congrArg (fun x : C => x.val s) hc
    have hact := sharedTwist_action_eq_self_at_splitPrime target e q d ℓ i r O ψ hp Q.val Q.property.2
      g.property _ ht
    simpa only [f, map_zero, zero_sub, map_neg, hact, sub_self] using hw g.val g.property

/-- One Frobenius evaluation controls the length lost on imposing the
decomposition conditions at every place above a split auxiliary prime. -/
theorem sharedTwist_frobenius_length_step_at_splitPrime
    [IsDiscreteValuationRing O] [Module.Flat ℤ_[ℓ] O]
    {p : ℕ} [Fact p.Prime] (hp : p ≡ 1 [MOD cnd * ℓ ^ r]) (hpℓ : p ≠ ℓ)
    (V : Submodule O C) (hV : V ≤ numberFieldSelmerSharedTwistArithmeticLayer F ℓ i O ψ r)
    (P : Ideal (𝓞 Ω)) [P.IsPrime] (hP : (p : 𝓞 Ω) ∈ P) (φ : Dec P)
    (hφ : IsArithFrobAt ℤ φ.val P)
    (a b : O) (hb : b ∣ (ℓ : O) ^ r)
    (hkill : ∀ c : V, b • ev φ.val c.val = 0) (hdetect : ∃ c : V, ev φ.val c.val ≠ 0) :
    0 < IsDiscreteValuationRing.addVal O b ∧
      Module.length O V + IsDiscreteValuationRing.addVal O a ≤
        Module.length O (V ⊓ vanRat p : Submodule O C) + IsDiscreteValuationRing.addVal O (a * b) := by
  have hp₀ : p.Prime := Fact.out
  have hne : P ≠ ⊥ := by
    intro h
    have he : (p : 𝓞 Ω) = 0 := Ideal.mem_bot.mp (h ▸ hP)
    exact hp₀.ne_zero (Nat.cast_eq_zero.mp he)
  let _ : P.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_rationalPrime_of_mem P p hP
  have hpc : ¬ p ∣ cnd := hp₀.coprime_iff_not_dvd.mp
    (Nat.coprime_of_mul_modEq_one 1 (by simpa using hp.of_dvd (dvd_mul_right cnd (ℓ ^ r))))
  have haway : ((cnd * ℓ : ℕ) : 𝓞 Ω) ∉ P := by
    rw [natCast_mem_iff_dvd_of_liesOver_rationalPrime P p, hp₀.dvd_mul]
    exact not_or.mpr ⟨hpc, fun hd =>
      hpℓ (((Nat.dvd_prime (Fact.out : ℓ.Prime)).mp hd).resolve_left hp₀.ne_one)⟩
  have hdense := numberField_dense_zpowers_quotient_inertia_of_isArithFrobAt (p := p) P φ hφ
  apply sharedTwist_eval_length_step target e q d ℓ i r O ψ inf_le_left φ.val ?_ a b hb hkill hdetect
  intro c hc
  have h := hV c.property
  have ht : (ℓ : O) ^ r • c.val = 0 := h.1
  have hv := (sharedTwistNormalizedCocycles_mem_vanishingOn_iff target e q d ℓ i O ψ c.val P
    hne haway φ hdense).mpr hc
  exact ⟨c.property, (sharedTwistNormalizedCocycles_mem_vanishingAtRationalPrime_iff
    target e q d ℓ i r O ψ hp c.val ht P hP).mpr hv⟩

end Riemann
