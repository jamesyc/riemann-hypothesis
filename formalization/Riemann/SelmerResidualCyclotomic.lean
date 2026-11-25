module

public import Riemann.SelmerRestrictionFamilies
public import Utilities.SelmerNormalizedLayers
import Utilities.RationalKummerVanishing
import Utilities.RationalPrime
import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open NumberField IsDedekindDomain Utilities DiscreteGaloisModule groupCohomology
open scoped NumberField Pointwise

namespace Riemann

/-- A rational Selmer kernel with residual cyclotomic action vanishes
when normalization is possible at a cyclotomic inertia element. -/
theorem rational_selmerKernel_subsingleton_of_residualCyclotomic
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] {ℓ : ℕ} [Fact ℓ.Prime]
    (hodd : Odd ℓ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ ℓ)
    (η : Gal(Ω/ℚ) → ZMod ℓ) (hη : ∀ g, g ζ = ζ ^ (η g).val)
    {S : Type} [CommRing S] (A : DiscreteGaloisModule S Gal(Ω/ℚ))
    (π : S) (hπ : π ∣ (ℓ : S)) (htors : ∀ x : A.rep, ∃ n : ℕ, π ^ n • x = 0)
    (Pℓ : Ideal (𝓞 Ω)) [Pℓ.IsPrime] (hPℓne : Pℓ ≠ ⊥) (hPℓ : (ℓ : 𝓞 Ω) ∈ Pℓ)
    (t : Gal(Ω/ℚ)) (ht : t ∈ Pℓ.inertia Gal(Ω/ℚ)) (hηt : η t ≠ 1)
    (hbij : Function.Bijective (A.rep.ρ t - 1 : Module.End S A.rep))
    (haway : ∀ (P : Ideal (𝓞 Ω)) [P.IsPrime], (ℓ : 𝓞 Ω) ∉ P →
      ∀ g ∈ P.inertia Gal(Ω/ℚ), A.rep.ρ g = 1)
    (hρ : ∀ g (x : A.rep), π • x = 0 → A.rep.ρ g x = (η g).val • x) :
    Subsingleton (A.selmerKernel (numberFieldSelmerRestrictionsIn ℚ Ω ℓ)) := by
  let D := numberFieldSelmerRestrictionsIn ℚ Ω ℓ
  let C := normalizedSelmerCocycles A D t
  have hI (c : C) (v : HeightOneSpectrum (𝓞 ℚ)) :
      ∃ P : Ideal (𝓞 Ω), P.IsPrime ∧ P.LiesOver v.asIdeal ∧ ∀ g ∈ P.inertia Gal(Ω/ℚ), c.val g = 0 := by
    let _ : v.asIdeal.IsMaximal := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.asIdeal (S := 𝓞 Ω)
    let _ : Q.IsPrime := hQ.isPrime
    let _ : Q.LiesOver v.asIdeal := hQv
    have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    by_cases h : (ℓ : 𝓞 Ω) ∈ Q
    · have hPv : Pℓ.LiesOver v.asIdeal :=
        ⟨(Ideal.over_def Q v.asIdeal).trans (under_ratPrime_eq_of_mem ℓ Q Pℓ h hPℓ)⟩
      obtain ⟨b, hb⟩ := c.property.1.2 (MulAction.stabilizer Gal(Ω/ℚ) Pℓ)
        ⟨Pℓ, inferInstance, hPℓne, Or.inr ⟨hPℓ, rfl⟩⟩
      have hbt : (A.rep.ρ t - 1 : Module.End S A.rep) b = 0 :=
        (hb t (Pℓ.inertia_le_stabilizer ht)).symm.trans c.property.2
      have hb₀ := hbij.injective (hbt.trans (map_zero _).symm)
      refine ⟨Pℓ, inferInstance, hPv, fun g hg => ?_⟩
      rw [hb g (Pℓ.inertia_le_stabilizer hg), hb₀, map_zero, sub_self]
    · obtain ⟨b, hb⟩ := c.property.1.2 (Q.inertia Gal(Ω/ℚ))
        ⟨Q, inferInstance, hQne, Or.inl rfl⟩
      exact ⟨Q, inferInstance, hQv, fun g hg => by rw [hb g hg, haway Q h g hg, one_apply_eq_self, sub_self]⟩
  have hfirst (c : C) (hc : π • c = 0) : c = 0 := by
    let V := Submodule.torsionBy S A.rep π
    let f (g : Gal(Ω/ℚ)) : V := ⟨c.val g, congrArg (fun x : C => x.val g) hc⟩
    have hV (v : V) : ℓ • v = 0 := by
      apply Subtype.ext
      change ℓ • v.val = 0
      obtain ⟨d, hd⟩ := hπ
      have hv : π • v.val = 0 := v.property
      rw [← Nat.cast_smul_eq_nsmul S, hd, mul_comm, mul_smul, hv, smul_zero]
    have hloc : IsLocallyConstant f :=
      IsLocallyConstant.desc f Subtype.val c.property.1.1.2 Subtype.val_injective
    have hf (g h : Gal(Ω/ℚ)) : f (g * h) = (η g).val • f h + f g := by
      apply Subtype.ext
      change c.val (g * h) = (η g).val • c.val h + c.val g
      rw [(mem_cocycles₁_iff _).mp c.property.1.1.1, hρ g (c.val h) (f h).property]
    have hIv (v : HeightOneSpectrum (𝓞 ℚ)) :
        ∃ P : Ideal (𝓞 Ω), P.IsPrime ∧ P.LiesOver v.asIdeal ∧ ∀ g ∈ P.inertia Gal(Ω/ℚ), f g = 0 := by
      obtain ⟨P, hP, hPv, hcz⟩ := hI c v
      exact ⟨P, hP, hPv, fun g hg => Subtype.ext (hcz g hg)⟩
    have hz := rational_cyclotomic_nsmul_cocycle_eq_zero hodd hζ η hη hV f hloc hf hIv t hηt
      (Subtype.ext c.property.2)
    apply Subtype.ext
    funext g
    exact congrArg Subtype.val (congrFun hz g)
  have hzero : ∀ n : ℕ, ∀ c : C, π ^ n • c = 0 → c = 0 := by
    intro n
    induction n with
    | zero =>
      intro c hc
      simpa only [pow_zero, one_smul] using hc
    | succ n ih =>
      intro c hc
      apply ih
      apply hfirst
      rw [← mul_smul, ← pow_succ']
      exact hc
  have hall (c : C) : c = 0 := by
    obtain ⟨n, hn⟩ := normalizedSelmerCocycles_powTorsion A D t π htors c
    exact hzero n c hn
  let e := normalizedSelmerCocyclesEquiv A D t hbij
  refine ⟨fun x y => e.symm.injective ?_⟩
  rw [hall (e.symm x), hall (e.symm y)]

end Riemann
