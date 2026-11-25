module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Utilities.NumberFieldTorsion
public import Riemann.HostBaseGroup
public import Riemann.NodeConstruction
public import Riemann.SelmerCohomology
public import Riemann.SmoothedCharacters
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic.FinCases
import Utilities.CyclotomicCharacter
public import Utilities.CyclotomicFrobenius
import Utilities.CyclotomicInertia
import Utilities.QuadraticResidue
import Utilities.RootDiscriminant

@[expose] public section

open Utilities
open scoped BigOperators Classical NumberField

namespace Riemann

/-! The host-field inputs to Theorem A and the extraction of the excess
witness use a common field and character identification at each scale. -/

abbrev ExcessHost (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+) : Type :=
  ↥(selmerHostField target e q d)

/-- At `d`, inertia in the host has exactly the `d` square-class factor. -/
theorem selmerHostGalCRT_exceptional_inertia (target : BundledDirichletCharacter) (e : ℕ)
    (q d : ℕ+) [Fact (d : ℕ).Prime]
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
    (Q : Ideal (𝓞 (ExcessHost target e q d))) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {((d : ℕ) : ℤ)})]
    (σ : ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d) :
    σ ∈ Q.inertia (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d) ↔
      (selmerHostGalCRT target e q d hq hd σ).1 = 1 := by
  let E := selmerHostField target e q d
  let N := selmerHostModulus target e q d
  let K := CyclotomicField N ℚ
  let m := selmerBaseModulus target e * (q : ℕ)
  have hdp : (d : ℕ).Prime := Fact.out
  have hprimeTo : ¬ (d : ℕ) ∣ m := hdp.coprime_iff_not_dvd.mp hd.symm
  have hn : N = (d : ℕ) ^ (0 + 1) * m := by
    rw [zero_add, pow_one, mul_comm (d : ℕ) m]
    exact selmerHostModulus_eq_mul target e q d hq hd
  have hmn : m ∣ N := hn ▸ dvd_mul_left m ((d : ℕ) ^ (0 + 1))
  let localN : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let localM : NeZero m := ⟨fun h => hprimeTo (h ▸ dvd_zero _)⟩
  let localNQ : NeZero (N : ℚ) := ⟨by exact_mod_cast (NeZero.ne N)⟩
  let localCyclotomic : IsCyclotomicExtension {N} ℚ K :=
    CyclotomicField.isCyclotomicExtension N ℚ
  let localAmbient := selmerCyclotomic_isAbelianGalois target e q d
  let localHost := selmerHostField_isAbelianGalois target e q d
  let localMaximal : Q.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {((d : ℕ) : ℤ)})
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral Q (S := 𝓞 K)
  let localPrime : P.IsPrime := hP.isPrime
  let localOver : P.LiesOver (Ideal.span {((d : ℕ) : ℤ)}) :=
    Ideal.LiesOver.trans P Q _
  let γ := selmerCyclotomicUnitsEquiv target e q d
  let units := selmerHostUnitsCRT target e q d hq hd
  let crt := selmerHostGalCRT target e q d hq hd
  let f : (K ≃ₐ[ℚ] K) →* (E ≃ₐ[ℚ] E) := AlgEquiv.restrictNormalHom E
  have hImage : (P.inertia (K ≃ₐ[ℚ] K)).map f = Q.inertia (E ≃ₐ[ℚ] E) :=
    numberField_inertia_map_restrictNormal E Q P
  have hKernel : (P.inertia (K ≃ₐ[ℚ] K)).map γ.toMonoidHom = (ZMod.unitsMap hmn).ker :=
    cyclotomic_inertia_map_eq_unitsMap_ker K P hn hprimeTo
  have hcoords (τ : K ≃ₐ[ℚ] K) :
      crt (f τ) = ((QuotientGroup.mk (units (γ τ)).1.1, QuotientGroup.mk (units (γ τ)).1.2),
        QuotientGroup.mk (units (γ τ)).2) :=
    selmerHostGalCRT_restrictNormal target e q d hq hd τ
  have hfst (u : (ZMod N)ˣ) : (units u).1 = 1 ↔ u ∈ (ZMod.unitsMap hmn).ker :=
    selmerHostUnitsCRT_fst_eq_one target e q d hq hd hmn u
  change σ ∈ Q.inertia (E ≃ₐ[ℚ] E) ↔ (crt σ).1 = 1
  rw [← hImage]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have hγ : γ τ ∈ (ZMod.unitsMap hmn).ker := hKernel ▸ Subgroup.mem_map_of_mem γ.toMonoidHom hτ
    have hh := (hfst (γ τ)).mpr hγ
    rw [hcoords]
    exact Prod.ext ((congrArg QuotientGroup.mk (congrArg Prod.fst hh)).trans (QuotientGroup.mk_one _))
      ((congrArg QuotientGroup.mk (congrArg Prod.snd hh)).trans (QuotientGroup.mk_one _))
  · intro hσ
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (crt σ).2
    let τ := γ.symm (units.symm (1, w))
    have hτcrt : units (γ τ) = (1, w) := by
      simp only [τ, MulEquiv.apply_symm_apply]
    have hτunits : γ τ ∈ (ZMod.unitsMap hmn).ker := (hfst (γ τ)).mp (congrArg Prod.fst hτcrt)
    rw [← hKernel] at hτunits
    obtain ⟨τ', hτ', heq⟩ := Subgroup.mem_map.mp hτunits
    have hτ : τ ∈ P.inertia (K ≃ₐ[ℚ] K) := γ.injective heq ▸ hτ'
    refine Subgroup.mem_map.mpr ⟨τ, hτ, crt.injective ?_⟩
    rw [hcoords, hτcrt]
    exact Prod.ext ((Prod.ext (QuotientGroup.mk_one _) (QuotientGroup.mk_one _)).trans hσ.symm) hw

/-- At any prime other than `d`, the last CRT coordinate of the restricted
Frobenius is the square class of that rational prime modulo `d`. -/
theorem selmerHostGalCRT_frobenius_last (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d) {p : ℕ} [Fact p.Prime]
    (hp : p.Coprime (d : ℕ))
    (P : Ideal (𝓞 (CyclotomicField (selmerHostModulus target e q d) ℚ)))
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    {τ : CyclotomicField (selmerHostModulus target e q d) ℚ ≃ₐ[ℚ]
      CyclotomicField (selmerHostModulus target e q d) ℚ} (hτ : IsArithFrobAt ℤ τ P) :
    letI := selmerHostField_isAbelianGalois target e q d
    (selmerHostGalCRT target e q d hq hd (τ.restrictNormal (selmerHostField target e q d))).2 =
      QuotientGroup.mk (ZMod.unitOfCoprime p hp) := by
  let N := selmerHostModulus target e q d
  let K := CyclotomicField N ℚ
  let _ : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let _ : NeZero (N : ℚ) := ⟨by exact_mod_cast (NeZero.ne N)⟩
  let _ : NeZero (d : ℕ) := ⟨d.pos.ne'⟩
  let _ : IsCyclotomicExtension {N} ℚ K := CyclotomicField.isCyclotomicExtension N ℚ
  have hdvd : (d : ℕ) ∣ N := Nat.dvd_lcm_right _ _
  have hunit : ZMod.unitsMap hdvd (selmerCyclotomicUnitsEquiv target e q d τ) =
      ZMod.unitOfCoprime p hp :=
    cyclotomic_frobenius_unitsMap_eq K P hτ hdvd hp
  rw [selmerHostGalCRT_restrictNormal, selmerHostUnitsCRT_apply]
  exact congrArg QuotientGroup.mk hunit

section HostCoordinates

variable (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
  [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime]
  (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3)
  (hq : (selmerBaseModulus target e).Coprime q)
  (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)

/-- The host's coordinates `(e₁, e₂, h)` from §5.7, with the `d` sign first. -/
noncomputable def selmerHostGalCoordinates :
    (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d) ≃*
      Multiplicative (ExcessGroup (SelmerHostBaseGroup target e)) := by
  let crt := selmerHostGalCRT target e q d hq hd
  let sq := selmerSquareClassSign hq₄
  let sd := selmerSquareClassSign hd₄
  refine { toFun := fun σ => Multiplicative.ofAdd
             ((sd (crt σ).2).toAdd, (sq (crt σ).1.2).toAdd, Additive.ofMul (crt σ).1.1)
           invFun := fun c => crt.symm
             ((c.toAdd.2.2.toMul, sq.symm (Multiplicative.ofAdd c.toAdd.2.1)),
               sd.symm (Multiplicative.ofAdd c.toAdd.1))
           left_inv := ?_
           right_inv := ?_
           map_mul' := ?_ }
  · intro σ
    simp
  · intro c
    simp
  · intro σ τ
    simp only [map_mul, Prod.fst_mul, Prod.snd_mul]
    rfl

/-- If `p` is a square modulo `d`, every Frobenius lift at `p` has first
additive coordinate zero after restriction to the host. -/
theorem selmerHostGalCoordinates_frobenius_first_eq_zero {p : ℕ} [Fact p.Prime]
    (hp : p.Coprime (d : ℕ)) (hsq : IsSquare (p : ZMod (d : ℕ)))
    (P : Ideal (𝓞 (CyclotomicField (selmerHostModulus target e q d) ℚ)))
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    {τ : CyclotomicField (selmerHostModulus target e q d) ℚ ≃ₐ[ℚ]
      CyclotomicField (selmerHostModulus target e q d) ℚ} (hτ : IsArithFrobAt ℤ τ P) :
    letI := selmerHostField_isAbelianGalois target e q d
    (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd
      (τ.restrictNormal (selmerHostField target e q d))).toAdd.1 = 0 := by
  let _ := selmerHostField_isAbelianGalois target e q d
  change (selmerSquareClassSign hd₄
    (selmerHostGalCRT target e q d hq hd (τ.restrictNormal (selmerHostField target e q d))).2).toAdd = 0
  rw [selmerHostGalCRT_frobenius_last target e q d hq hd hp P hτ]
  let u := ZMod.unitOfCoprime p hp
  have hu : IsSquare u := isSquare_zmodUnit_of_isSquare_coe (by
    simpa only [u, ZMod.coe_unitOfCoprime] using hsq)
  have hclass : (QuotientGroup.mk u : (ZMod (d : ℕ))ˣ ⧸ selmerSquareUnits d) = 1 := by
    apply (QuotientGroup.eq_one_iff u).mpr
    obtain ⟨v, hv⟩ := hu
    refine Subgroup.mem_map.mpr ⟨v, Subgroup.mem_top v, ?_⟩
    change v ^ 2 = u
    simpa only [pow_two] using hv.symm
  change (selmerSquareClassSign hd₄ (QuotientGroup.mk u)).toAdd = 0
  rw [hclass, map_one]
  rfl

/-- At a prime away from `d`, the inertia in the cyclotomic field is
trivial on the first additive coordinate of the host. -/
theorem selmerHostGalCoordinates_inertia_first_eq_zero {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ (d : ℕ))
    (P : Ideal (𝓞 (CyclotomicField (selmerHostModulus target e q d) ℚ)))
    [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    {τ : CyclotomicField (selmerHostModulus target e q d) ℚ ≃ₐ[ℚ]
      CyclotomicField (selmerHostModulus target e q d) ℚ} (hτ : τ ∈ P.inertia _) :
    letI := selmerHostField_isAbelianGalois target e q d
    (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd
      (τ.restrictNormal (selmerHostField target e q d))).toAdd.1 = 0 := by
  let N := selmerHostModulus target e q d
  let K := CyclotomicField N ℚ
  let _ : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let _ : NeZero (N : ℚ) := ⟨by exact_mod_cast (NeZero.ne N)⟩
  let _ : NeZero (d : ℕ) := ⟨d.pos.ne'⟩
  let _ : IsCyclotomicExtension {N} ℚ K := CyclotomicField.isCyclotomicExtension N ℚ
  let _ := selmerHostField_isAbelianGalois target e q d
  have hdvd : (d : ℕ) ∣ N := Nat.dvd_lcm_right _ _
  have hunit : ZMod.unitsMap hdvd (selmerCyclotomicUnitsEquiv target e q d τ) = 1 :=
    cyclotomic_inertia_map_le_unitsMap_ker K P hdvd hp
      (Subgroup.mem_map_of_mem (selmerCyclotomicUnitsEquiv target e q d).toMonoidHom hτ)
  change (selmerSquareClassSign hd₄
    (selmerHostGalCRT target e q d hq hd (τ.restrictNormal (selmerHostField target e q d))).2).toAdd = 0
  rw [selmerHostGalCRT_restrictNormal, selmerHostUnitsCRT_apply]
  change (selmerSquareClassSign hd₄
    (QuotientGroup.mk (ZMod.unitsMap hdvd (selmerCyclotomicUnitsEquiv target e q d τ)))).toAdd = 0
  rw [hunit, QuotientGroup.mk_one, map_one]
  rfl

theorem selmerHostGalCoordinates_conjugation
    (ι : ExcessHost target e q d →ₐ[ℚ] ℂ)
    (σ : ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)
    (hσ : ∀ z, ι (σ z) = star (ι z)) :
    let c := (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd σ).toAdd
    c.1 = 1 ∧ c.2.1 = 1 := by
  change (selmerSquareClassSign hd₄ (selmerHostGalCRT target e q d hq hd σ).2).toAdd = 1 ∧
    (selmerSquareClassSign hq₄ (selmerHostGalCRT target e q d hq hd σ).1.2).toAdd = 1
  rw [selmerHostGalCRT_conjugation target e q d hq hd ι σ hσ]
  simp only [selmerSquareClassSign_neg_one, and_self]
  rfl

/-- The two inertia elements for Lemma 18.6 and Proposition 3.3. -/
theorem selmerHostGalCoordinates_exceptional_inertia
    (Q : Ideal (𝓞 (ExcessHost target e q d))) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {((d : ℕ) : ℤ)})]
    (g : ExcessGroup (SelmerHostBaseGroup target e)) :
    (selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd).symm (Multiplicative.ofAdd g) ∈
      Q.inertia (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d) ↔
        g = 0 ∨ g = (1, 0, 0) := by
  let crt := selmerHostGalCRT target e q d hq hd
  let sq := selmerSquareClassSign hq₄
  let sd := selmerSquareClassSign hd₄
  rw [selmerHostGalCRT_exceptional_inertia target e q d hq hd Q]
  change (crt (crt.symm ((g.2.2.toMul, sq.symm (Multiplicative.ofAdd g.2.1)),
    sd.symm (Multiplicative.ofAdd g.1)))).1 = 1 ↔ _
  rw [crt.apply_symm_apply]
  constructor
  · intro hg
    have hbase : g.2.2 = 0 := congrArg Prod.fst hg
    have hqZero : g.2.1 = 0 := (sq.symm.map_eq_one_iff).mp (congrArg Prod.snd hg)
    have hbinary (s : ZMod 2) : s = 0 ∨ s = 1 := by
      fin_cases s
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hbinary g.1 with h₀ | h₁
    · exact Or.inl (Prod.ext h₀ (Prod.ext hqZero hbase))
    · exact Or.inr (Prod.ext h₁ (Prod.ext hqZero hbase))
  · rintro (rfl | rfl) <;> exact Prod.ext rfl (map_one sq.symm)

end HostCoordinates

/-- The host coordinates for the primes supplied by a window pair. -/
noncomputable def SelmerWindowPair.hostCoordinates {ε base : ℝ} {q d : ℕ+}
    (hpair : SelmerWindowPair ε base q d) (target : BundledDirichletCharacter) (e : ℕ)
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d) :
    (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d) ≃*
      Multiplicative (ExcessGroup (SelmerHostBaseGroup target e)) := by
  let _ : Fact (q : ℕ).Prime := ⟨hpair.q_prime⟩
  let _ : Fact (d : ℕ).Prime := ⟨hpair.d_prime⟩
  exact selmerHostGalCoordinates target e q d (by have := hpair.q_residue; omega)
    (by have := hpair.d_residue; omega) hq hd

/-- The prime data on the host, shared by the character identifications and
the arithmetic chain construction. -/
structure HostPrimeConditions {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H]
    (prime : PrimeExcessData H)
    (galoisEquiv : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d))
    (primeIdeal : ℕ → Ideal (𝓞 (ExcessHost target e q d))) : Prop where
  exceptional_eq : prime.exceptional = (d : ℕ)
  excluded_eq : ∀ p : ℕ, p ∈ prime.excluded ↔
    p.Prime ∧ p ∣ 2 * (q : ℕ) * (target.modulus : ℕ)
  prime_hypotheses : PrimeExcessHypotheses prime
  prime_over : ∀ p : ℕ, p.Prime →
    (primeIdeal p).IsPrime ∧
      (primeIdeal p).comap (algebraMap ℤ (𝓞 (ExcessHost target e q d))) = Ideal.span {(p : ℤ)}
  inertia_eq : ∀ p : ℕ, p.Prime → ∀ g : ExcessGroup H,
    g ∈ prime.inertia p ↔ galoisEquiv (Multiplicative.ofAdd g) ∈ (primeIdeal p).inertia _
  frobenius_congruence : ∀ p : ℕ, p.Prime →
    ∀ z : 𝓞 (ExcessHost target e q d),
      galoisEquiv (Multiplicative.ofAdd (prime.frobenius p)) • z - z ^ p ∈ primeIdeal p
  conjugation_signs : ∀ (ι : ExcessHost target e q d →ₐ[ℚ] ℂ)
    (σ : ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d),
    (∀ y, ι (σ y) = star (ι y)) →
      (galoisEquiv.symm σ).toAdd.1 = 1 ∧ (galoisEquiv.symm σ).toAdd.2.1 = 1

set_option maxHeartbeats 400000 in
/-- Choose primes and Frobenius lifts in the cyclotomic field and restrict
them to the host. The logarithmic derivatives are supplied by the inducing
characters, independently of those choices. -/
theorem exists_selmerHostPrimeConditions (target : BundledDirichletCharacter) (e : ℕ)
    {ε base : ℝ} {q d : ℕ+} (hpair : SelmerWindowPair ε base q d)
    (hsize : ((target.modulus : ℕ) : ℝ) ≤ base ^ (ε / 5))
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d)
    (logDerivative : ExcessCharacter (SelmerHostBaseGroup target e) → ℂ) :
    ∃ (prime : PrimeExcessData (SelmerHostBaseGroup target e))
      (primeIdeal : ℕ → Ideal (𝓞 (ExcessHost target e q d))),
      HostPrimeConditions (target := target) (e := e) (q := q) (d := d)
        prime (hpair.hostCoordinates target e hq hd).symm primeIdeal ∧
          prime.logDerivativeAtOne = logDerivative := by
  classical
  let H := SelmerHostBaseGroup target e
  let n := selmerHostModulus target e q d
  let K := CyclotomicField n ℚ
  let E := selmerHostField target e q d
  let _ : NeZero n := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let _ : NeZero (n : ℚ) := ⟨by exact_mod_cast (NeZero.ne n)⟩
  let _ : IsCyclotomicExtension {n} ℚ K := CyclotomicField.isCyclotomicExtension n ℚ
  let _ := selmerCyclotomic_isAbelianGalois target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : Fact (q : ℕ).Prime := ⟨hpair.q_prime⟩
  let _ : Fact (d : ℕ).Prime := ⟨hpair.d_prime⟩
  have hq₄ : (q : ℕ) % 4 = 3 := by have := hpair.q_residue; omega
  have hd₄ : (d : ℕ) % 4 = 3 := by have := hpair.d_residue; omega
  let coord := selmerHostGalCoordinates target e q d hq₄ hd₄ hq hd
  have hlocal (p : ℕ) : ∃ (P : Ideal (𝓞 K)) (τ : K ≃ₐ[ℚ] K), p.Prime →
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧ IsArithFrobAt ℤ τ P := by
    by_cases hp : p.Prime
    · let _ : Fact p.Prime := ⟨hp⟩
      let P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) := Classical.choice inferInstance
      obtain ⟨τ, hτ⟩ := numberField_exists_isArithFrobAt hp P.1
      exact ⟨P.1, τ, fun _ => ⟨inferInstance, inferInstance, hτ⟩⟩
    · exact ⟨⊥, 1, fun hp' => (hp hp').elim⟩
  choose P τ hPt using hlocal
  let Q (p : ℕ) := (P p).under (𝓞 E)
  let restrict : (K ≃ₐ[ℚ] K) →* (E ≃ₐ[ℚ] E) := AlgEquiv.restrictNormalHom E
  have hQprime (p : ℕ) (hp : p.Prime) : (Q p).IsPrime :=
    (hPt p hp).1.comap (algebraMap (𝓞 E) (𝓞 K))
  have hQover (p : ℕ) (hp : p.Prime) : (Q p).LiesOver (Ideal.span {(p : ℤ)}) := by
    let _ := (hPt p hp).2.1
    refine ⟨?_⟩
    change Ideal.span {(p : ℤ)} = ((P p).under (𝓞 E)).under ℤ
    rw [Ideal.under_under, ← (P p).over_def (Ideal.span {(p : ℤ)})]
  have himage (p : ℕ) (hp : p.Prime) :
      ((P p).inertia (K ≃ₐ[ℚ] K)).map restrict = (Q p).inertia (E ≃ₐ[ℚ] E) := by
    let _ := (hPt p hp).1
    let _ : (P p).LiesOver (Q p) := Ideal.over_under (A := 𝓞 E) (P p)
    exact numberField_inertia_map_restrictNormal E (Q p) (P p)
  let excludedModulus := 2 * (q : ℕ) * (target.modulus : ℕ)
  have hmod₀ : excludedModulus ≠ 0 := by
    dsimp only [excludedModulus]
    positivity [q.pos, target.modulus.pos]
  have hexcluded (p : ℕ) : p ∈ excludedModulus.primeFactors ↔ p.Prime ∧ p ∣ excludedModulus :=
    Nat.mem_primeFactors_of_ne_zero hmod₀
  have hdExcluded : ¬ (d : ℕ) ∣ excludedModulus := by
    have hnot := hpair.d_prime.coprime_iff_not_dvd.mp hd.symm
    intro hdiv
    rcases hpair.d_prime.dvd_mul.mp hdiv with hleft | hright
    · rcases hpair.d_prime.dvd_mul.mp hleft with htwo | hq'
      · have heq := (Nat.prime_dvd_prime_iff_eq hpair.d_prime Nat.prime_two).mp htwo
        omega
      · exact hnot (hq'.trans (dvd_mul_left _ _))
    · have hbase : (target.modulus : ℕ) ∣ selmerBaseModulus target e := Nat.dvd_lcm_right _ _
      exact hnot (hright.trans (hbase.trans (dvd_mul_right _ _)))
  have hnotConductor (p : ℕ) (hp : p.Prime) (hex : p ∉ excludedModulus.primeFactors)
      (hpd : p ≠ (d : ℕ)) : ¬ p ∣ n := by
    intro hdiv
    change p ∣ Nat.lcm (Nat.lcm (selmerBaseModulus target e) q) d at hdiv
    have hnot : ¬ p ∣ excludedModulus := fun h => hex ((hexcluded p).mpr ⟨hp, h⟩)
    rcases hp.dvd_lcm.mp hdiv with hbase | hdvd
    · rcases hp.dvd_lcm.mp hbase with hbase | hq'
      · change p ∣ Nat.lcm (2 ^ (e + 2)) (target.modulus : ℕ) at hbase
        rcases hp.dvd_lcm.mp hbase with htwo | hf
        · exact hnot (((hp.dvd_of_dvd_pow htwo).trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _))
        · exact hnot (hf.trans (dvd_mul_left _ _))
      · exact hnot ((hq'.trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _))
    · exact hpd ((Nat.prime_dvd_prime_iff_eq hp hpair.d_prime).mp hdvd)
  have haway (p : ℕ) (hp : p.Prime) (hex : p ∈ excludedModulus.primeFactors) : ¬ p ∣ (d : ℕ) := by
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq hp hpair.d_prime).mp h
    exact hdExcluded (heq ▸ ((hexcluded p).mp hex).2)
  let inertia (p : ℕ) : AddSubgroup (ExcessGroup H) :=
    Subgroup.toAddSubgroup' (A := ExcessGroup H)
      (((Q p).inertia (E ≃ₐ[ℚ] E)).comap coord.symm.toMonoidHom)
  let prime : PrimeExcessData H :=
    { exceptional := d
      excluded := excludedModulus.primeFactors
      frobenius := fun p => (coord (restrict (τ p))).toAdd
      inertia := inertia
      quadratic := zmodTwoSign.compAddMonoidHom (AddMonoidHom.fst _ _)
      logDerivativeAtOne := logDerivative }
  have hprime : PrimeExcessHypotheses prime := by
    refine ⟨hpair.d_prime, fun hex => hdExcluded ((hexcluded d).mp hex).2, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp hex hpd
      let _ : Fact p.Prime := ⟨hp⟩
      let _ := (hPt p hp).1
      let _ := (hPt p hp).2.1
      have hPbot := cyclotomic_inertia_eq_bot_of_not_dvd K (P p) (hnotConductor p hp hex hpd)
      have hQbot : (Q p).inertia (E ≃ₐ[ℚ] E) = ⊥ := by
        rw [← himage p hp, hPbot, Subgroup.map_bot]
      show inertia p = ⊥
      apply AddSubgroup.ext
      intro g
      simp only [inertia, Subgroup.mem_toAddSubgroup', Subgroup.mem_comap, hQbot,
        MulEquiv.coe_toMonoidHom, Subgroup.mem_bot, AddSubgroup.mem_bot]
      have hone : coord.symm (1 : Multiplicative (ExcessGroup H)) = 1 := by
        let hom : Multiplicative (ExcessGroup H) →* (E ≃ₐ[ℚ] E) := coord.symm.toMonoidHom
        exact hom.map_one
      rw [← hone, coord.symm.injective.eq_iff, ofAdd_eq_one]
    · intro p hex hp g hg
      let _ : Fact p.Prime := ⟨hp⟩
      let _ := (hPt p hp).1
      let _ := (hPt p hp).2.1
      change coord.symm (Multiplicative.ofAdd g) ∈ (Q p).inertia (E ≃ₐ[ℚ] E) at hg
      rw [← himage p hp] at hg
      obtain ⟨σ, hσ, heq⟩ := Subgroup.mem_map.mp hg
      have hg' : (coord (restrict σ)).toAdd = g := by
        rw [heq, MulEquiv.apply_symm_apply]
        rfl
      rw [← hg']
      exact selmerHostGalCoordinates_inertia_first_eq_zero target e q d hq₄ hd₄ hq hd
        (haway p hp hex) (P p) hσ
    · intro p hex hp
      let _ : Fact p.Prime := ⟨hp⟩
      let _ := (hPt p hp).2.1
      exact selmerHostGalCoordinates_frobenius_first_eq_zero target e q d hq₄ hd₄ hq hd
        (hp.coprime_iff_not_dvd.mpr (haway p hp hex))
        (hpair.isSquare_excluded target.modulus.pos hsize hp ((hexcluded p).mp hex).2)
        (P p) (hPt p hp).2.2
    · intro g
      let _ := hQprime d hpair.d_prime
      let _ := hQover d hpair.d_prime
      exact selmerHostGalCoordinates_exceptional_inertia target e q d hq₄ hd₄ hq hd (Q d) g
    · intro g
      exact zmodTwoSign_apply g.1
  refine ⟨prime, Q, ⟨rfl, hexcluded, hprime, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro p hp
    exact ⟨hQprime p hp, (hQover p hp).over.symm⟩
  · intro p _ g
    rfl
  · intro p hp z
    let _ := hQover p hp
    let _ : (P p).LiesOver (Q p) := Ideal.over_under (A := 𝓞 E) (P p)
    have hfrob := numberField_isArithFrobAt_restrictNormal E (p := p) (Q p) (P p) (hPt p hp).2.2
    change coord.symm (coord (restrict (τ p))) • z - z ^ p ∈ Q p
    rw [MulEquiv.symm_apply_apply]
    exact (numberField_isArithFrobAt_iff (p := p) (Q p) _).mp hfrob z
  · intro ι σ hσ
    exact selmerHostGalCoordinates_conjugation target e q d hq₄ hd₄ hq hd ι σ hσ

/-- Pull a host character back through the cyclotomic Artin map at the full level. -/
noncomputable def selmerHostDirichlet {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H]
    (galoisEquiv : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d))
    (ψ : ExcessCharacter H) : DirichletCharacter ℂ (selmerHostModulus target e q d) := by
  let E := selmerHostField target e q d
  let K := CyclotomicField (selmerHostModulus target e q d) ℚ
  let _ := selmerHostField_isAbelianGalois target e q d
  let γ : (ZMod (selmerHostModulus target e q d))ˣ →* (K ≃ₐ[ℚ] K) :=
    (selmerCyclotomicUnitsEquiv target e q d).symm.toMonoidHom
  let restrict : (K ≃ₐ[ℚ] K) →* (E ≃ₐ[ℚ] E) := AlgEquiv.restrictNormalHom E
  let coordinates : (E ≃ₐ[ℚ] E) →* Multiplicative (ExcessGroup H) :=
    galoisEquiv.symm.toMonoidHom
  exact MulChar.ofUnitHom (ψ.toMonoidHom.comp (coordinates.comp (restrict.comp γ))).toHomUnits

theorem selmerHostDirichlet_apply_gal {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H]
    (galoisEquiv : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d))
    (ψ : ExcessCharacter H) (σ : CyclotomicField (selmerHostModulus target e q d) ℚ ≃ₐ[ℚ]
      CyclotomicField (selmerHostModulus target e q d) ℚ) :
    letI := selmerHostField_isAbelianGalois target e q d
    selmerHostDirichlet (target := target) (e := e) (q := q) (d := d)
      galoisEquiv ψ (selmerCyclotomicUnitsEquiv target e q d σ) =
      ψ (galoisEquiv.symm (σ.restrictNormal (selmerHostField target e q d))).toAdd := by
  let _ := selmerHostField_isAbelianGalois target e q d
  simp only [selmerHostDirichlet, MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, AddChar.toMonoidHom_apply]
  rfl

/-- The inducing primitive character of a host character, with its conductor. -/
noncomputable def selmerHostInducingCharacter {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H]
    (galoisEquiv : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d))
    (ψ : ExcessCharacter H) : BundledDirichletCharacter := by
  let χ := selmerHostDirichlet (target := target) (e := e) (q := q) (d := d) galoisEquiv ψ
  let _ : NeZero (selmerHostModulus target e q d) := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  exact BundledDirichletCharacter.primitiveOf χ

theorem selmerHostInducingCharacter_isPrimitive {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H]
    (galoisEquiv : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d))
    (ψ : ExcessCharacter H) :
    (selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
      galoisEquiv ψ).character.IsPrimitive :=
  (selmerHostDirichlet (target := target) (e := e) (q := q) (d := d)
    galoisEquiv ψ).primitiveCharacter_isPrimitive

/-- The primitive induction preserves nontriviality of host characters. -/
theorem selmerHostInducingCharacter_ne_one {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H]
    (galoisEquiv : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d))
    {ψ : ExcessCharacter H} (hψ : ψ ≠ 0) :
    (selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
      galoisEquiv ψ).character ≠ 1 := by
  let χ := selmerHostDirichlet (target := target) (e := e) (q := q) (d := d) galoisEquiv ψ
  intro hχ
  change χ.primitiveCharacter = 1 at hχ
  have hfull : χ = 1 := by rw [← χ.changeLevel_primitiveCharacter, hχ, map_one]
  apply hψ
  apply DFunLike.ext
  intro g
  change ψ g = 1
  let K := CyclotomicField (selmerHostModulus target e q d) ℚ
  let E := selmerHostField target e q d
  let _ := selmerCyclotomic_isAbelianGalois target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let σ := galoisEquiv (Multiplicative.ofAdd g)
  let τ := σ.liftNormal K
  have hvalue := selmerHostDirichlet_apply_gal
    (target := target) (e := e) (q := q) (d := d) galoisEquiv ψ τ
  change χ (selmerCyclotomicUnitsEquiv target e q d τ) =
    ψ (galoisEquiv.symm (τ.restrictNormal E)).toAdd at hvalue
  have hrestrict : τ.restrictNormal E = σ := σ.restrict_liftNormal K
  rw [hfull, MulChar.one_apply_coe, hrestrict] at hvalue
  simpa only [σ, MulEquiv.symm_apply_apply, toAdd_ofAdd] using hvalue.symm

/-- Evaluating the lifted character on cyclotomic inertia detects exactly
whether the original character is trivial on host inertia. -/
theorem HostPrimeConditions.trivialOnInertia_iff {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H]
    {prime : PrimeExcessData H}
    {galoisEquiv : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)}
    {primeIdeal : ℕ → Ideal (𝓞 (ExcessHost target e q d))}
    (hc : HostPrimeConditions (target := target) (e := e) (q := q) (d := d)
      prime galoisEquiv primeIdeal) {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 (CyclotomicField (selmerHostModulus target e q d) ℚ)))
    [P.IsPrime] [P.LiesOver (primeIdeal p)] (ψ : ExcessCharacter H) :
    (∀ g ∈ prime.inertia p, ψ g = 1) ↔
      ∀ σ ∈ P.inertia _, selmerHostDirichlet (target := target) (e := e) (q := q) (d := d)
        galoisEquiv ψ (selmerCyclotomicUnitsEquiv target e q d σ) = 1 := by
  let E := selmerHostField target e q d
  let K := CyclotomicField (selmerHostModulus target e q d) ℚ
  let _ := selmerCyclotomic_isAbelianGalois target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let restrict : (K ≃ₐ[ℚ] K) →* (E ≃ₐ[ℚ] E) := AlgEquiv.restrictNormalHom E
  have hmap : (P.inertia (K ≃ₐ[ℚ] K)).map restrict = (primeIdeal p).inertia (E ≃ₐ[ℚ] E) :=
    numberField_inertia_map_restrictNormal E (primeIdeal p) P
  have heval (σ : K ≃ₐ[ℚ] K) :
      selmerHostDirichlet (target := target) (e := e) (q := q) (d := d)
        galoisEquiv ψ (selmerCyclotomicUnitsEquiv target e q d σ) =
        ψ (galoisEquiv.symm (restrict σ)).toAdd :=
    selmerHostDirichlet_apply_gal (target := target) (e := e) (q := q) (d := d) galoisEquiv ψ σ
  simp only [heval]
  constructor
  · intro h σ hσ
    apply h
    apply (hc.inertia_eq p hp _).mpr
    change galoisEquiv (galoisEquiv.symm (restrict σ)) ∈ (primeIdeal p).inertia (E ≃ₐ[ℚ] E)
    rw [MulEquiv.apply_symm_apply, ← hmap]
    exact Subgroup.mem_map_of_mem _ hσ
  · intro h g hg
    have hmem := (hc.inertia_eq p hp g).mp hg
    rw [← hmap] at hmem
    obtain ⟨σ, hσ, heq⟩ := Subgroup.mem_map.mp hmem
    have hvalue := h σ hσ
    rw [heq, MulEquiv.symm_apply_apply] at hvalue
    exact hvalue

set_option maxHeartbeats 500000 in
/-- The inertia-coset coefficient of Proposition 3.3 agrees with the
primitive Dirichlet coefficient for every prime power, including those
whose base prime divides the full cyclotomic level. -/
theorem HostPrimeConditions.coefficient_eq_inducing
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H] {prime : PrimeExcessData H}
    {galoisEquiv : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)}
    {primeIdeal : ℕ → Ideal (𝓞 (ExcessHost target e q d))}
    (hc : HostPrimeConditions (target := target) (e := e) (q := q) (d := d)
      prime galoisEquiv primeIdeal) (ψ : ExcessCharacter H) {m : ℕ} (hm : IsPrimePow m) :
    let χ := selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) galoisEquiv ψ
    prime.coefficient ψ m = χ.character (m : ZMod (χ.modulus : ℕ)) := by
  classical
  let p := m.minFac
  let k := m.factorization p
  have hp : p.Prime := Nat.minFac_prime hm.ne_one
  have hk : 0 < k := Nat.pos_of_ne_zero (Nat.factorization_minFac_ne_zero hm.one_lt)
  have hpower : p ^ k = m := hm.minFac_pow_factorization_eq
  let n := selmerHostModulus target e q d
  let K := CyclotomicField n ℚ
  let E := selmerHostField target e q d
  let _ : NeZero n := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let _ : NeZero (n : ℚ) := ⟨by exact_mod_cast (NeZero.ne n)⟩
  let _ : IsCyclotomicExtension {n} ℚ K := CyclotomicField.isCyclotomicExtension n ℚ
  let _ := selmerCyclotomic_isAbelianGalois target e q d
  let _ := selmerHostField_isAbelianGalois target e q d
  let _ : Fact p.Prime := ⟨hp⟩
  let Q := primeIdeal p
  let _ : Q.IsPrime := (hc.prime_over p hp).1
  let _ : Q.LiesOver (Ideal.span {(p : ℤ)}) := ⟨(hc.prime_over p hp).2.symm⟩
  let _ : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {(p : ℤ)})
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral Q (S := 𝓞 K)
  let _ : P.IsPrime := hP.isPrime
  let _ : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P Q _
  obtain ⟨τ, hτ⟩ := numberField_exists_isArithFrobAt hp P
  let γ := selmerCyclotomicUnitsEquiv target e q d
  let χ := selmerHostDirichlet (target := target) (e := e) (q := q) (d := d) galoisEquiv ψ
  have hprim : χ.primitiveCharacter (m : ZMod χ.conductor) =
      if ∀ ρ ∈ P.inertia (K ≃ₐ[ℚ] K), χ (γ ρ) = 1 then χ (γ τ) ^ k else 0 := by
    rw [← hpower]
    exact cyclotomic_primitiveCharacter_primePow K P χ hτ hk
  have htriv : (∀ g ∈ prime.inertia p, ψ g = 1) ↔
      ∀ ρ ∈ P.inertia (K ≃ₐ[ℚ] K), χ (γ ρ) = 1 :=
    hc.trivialOnInertia_iff hp P ψ
  change prime.coefficient ψ m = χ.primitiveCharacter (m : ZMod χ.conductor)
  simp only [PrimeExcessData.coefficient, ite_eq_left hm]
  change characterCosetAverage (prime.inertia p) (k • prime.frobenius p) ψ = _
  rw [characterCosetAverage_eq_ite, hprim]
  simp only [← htriv]
  by_cases hψ : ∀ g ∈ prime.inertia p, ψ g = 1
  · let σ := galoisEquiv (Multiplicative.ofAdd (prime.frobenius p))
    let τ' := τ.restrictNormal E
    have hfrob : IsArithFrobAt ℤ σ Q :=
      (numberField_isArithFrobAt_iff (p := p) Q σ).mpr (hc.frobenius_congruence p hp)
    have hfrob' : IsArithFrobAt ℤ τ' Q :=
      numberField_isArithFrobAt_restrictNormal E (p := p) Q P hτ
    have hinertia : τ' * σ⁻¹ ∈ Q.inertia (E ≃ₐ[ℚ] E) :=
      IsArithFrobAt.mul_inv_mem_inertia hfrob' hfrob
    have hcoord : (galoisEquiv.symm (τ' * σ⁻¹)).toAdd ∈ prime.inertia p := by
      apply (hc.inertia_eq p hp _).mpr
      change galoisEquiv (galoisEquiv.symm (τ' * σ⁻¹)) ∈ Q.inertia (E ≃ₐ[ℚ] E)
      rwa [MulEquiv.apply_symm_apply]
    let coords : (E ≃ₐ[ℚ] E) →* Multiplicative (ExcessGroup H) :=
      galoisEquiv.symm.toMonoidHom
    let eval := ψ.toMonoidHom.comp coords
    have hquotient : eval (τ' * σ⁻¹) = 1 := hψ _ hcoord
    have hvalue : χ (γ τ) = ψ (prime.frobenius p) := by
      calc
        _ = eval τ' :=
          selmerHostDirichlet_apply_gal (target := target) (e := e) (q := q) (d := d)
            galoisEquiv ψ τ
        _ = eval ((τ' * σ⁻¹) * σ) := congrArg eval (by simp [mul_assoc])
        _ = eval σ := by rw [map_mul, hquotient, one_mul]
        _ = _ := by
          change ψ (galoisEquiv.symm (galoisEquiv (Multiplicative.ofAdd (prime.frobenius p)))).toAdd = _
          rw [MulEquiv.symm_apply_apply]
          rfl
    simp only [ite_eq_left hψ, ψ.map_nsmul_eq_pow, hvalue]
  · simp only [ite_eq_right hψ]

/-- The primitive characters and logarithmic derivatives paired with the
host's prime-power coefficients. -/
structure HostInducingConditions {H : Type} [AddCommGroup H] [Fintype H]
    (prime : PrimeExcessData H) (inducing : ExcessCharacter H → BundledDirichletCharacter) : Prop where
  inducing_primitive : ∀ ψ, (inducing ψ).character.IsPrimitive
  inducing_coefficient : ∀ ψ n, IsPrimePow n →
    prime.coefficient ψ n = (inducing ψ).character (n : ZMod ((inducing ψ).modulus : ℕ))
  inducing_logDerivative : ∀ ψ, ψ ≠ 0 →
    prime.logDerivativeAtOne ψ = logDeriv (DirichletCharacter.LFunction (inducing ψ).character) 1

theorem HostInducingConditions.smoothed_eq_inducing {H : Type} [AddCommGroup H] [Fintype H]
    {prime : PrimeExcessData H} {inducing : ExcessCharacter H → BundledDirichletCharacter}
    (h : HostInducingConditions prime inducing) {ψ : ExcessCharacter H} (hψ : ψ ≠ 0) (y : ℝ) :
    prime.smoothed ψ y = complexSmoothedCharacterSum (inducing ψ) y := by
  unfold PrimeExcessData.smoothed complexSmoothedCharacterSum
  rw [ite_eq_right hψ, h.inducing_logDerivative ψ hψ]
  unfold smoothedTwist
  rw [smoothedMangoldt_congr_on_primePowers (h.inducing_coefficient ψ) y]

theorem HostPrimeConditions.toInducingConditions
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H] {prime : PrimeExcessData H}
    {galoisEquiv : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)}
    {primeIdeal : ℕ → Ideal (𝓞 (ExcessHost target e q d))}
    (hprime : HostPrimeConditions (target := target) (e := e) (q := q) (d := d)
      prime galoisEquiv primeIdeal)
    (hlog : prime.logDerivativeAtOne = fun ψ =>
      logDeriv (DirichletCharacter.LFunction
        (selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
          galoisEquiv ψ).character) 1) :
    HostInducingConditions prime
      (selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) galoisEquiv) :=
  ⟨selmerHostInducingCharacter_isPrimitive (target := target) (e := e) (q := q) (d := d) galoisEquiv,
    fun ψ _ hm => hprime.coefficient_eq_inducing ψ hm, fun ψ _ => congrFun hlog ψ⟩

/-- The canonical prime data and its primitive inducing characters at a fixed host. -/
theorem exists_selmerHostInducingConditions (target : BundledDirichletCharacter) (e : ℕ)
    {ε base : ℝ} {q d : ℕ+} (hpair : SelmerWindowPair ε base q d)
    (hsize : ((target.modulus : ℕ) : ℝ) ≤ base ^ (ε / 5))
    (hq : (selmerBaseModulus target e).Coprime q)
    (hd : (selmerBaseModulus target e * (q : ℕ)).Coprime d) :
    letI := selmerHostBaseGroupFintype target e
    let coord := hpair.hostCoordinates target e hq hd
    let inducing (ψ : ExcessCharacter (SelmerHostBaseGroup target e)) :=
      selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) coord.symm ψ
    ∃ (prime : PrimeExcessData (SelmerHostBaseGroup target e))
      (primeIdeal : ℕ → Ideal (𝓞 (ExcessHost target e q d))),
      HostPrimeConditions (target := target) (e := e) (q := q) (d := d) prime coord.symm primeIdeal ∧
        HostInducingConditions prime inducing := by
  let _ := selmerHostBaseGroupFintype target e
  let coord := hpair.hostCoordinates target e hq hd
  let inducing (ψ : ExcessCharacter (SelmerHostBaseGroup target e)) :=
    selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) coord.symm ψ
  obtain ⟨prime, P, hprime, hlog⟩ := exists_selmerHostPrimeConditions target e hpair hsize hq hd
    (fun ψ => logDeriv (DirichletCharacter.LFunction (inducing ψ).character) 1)
  exact ⟨prime, P, hprime, hprime.toInducingConditions hlog⟩

structure AdmissibleExcessData (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (H : Type) [AddCommGroup H] where
  averaging : ExcessAverageData H
  prime : PrimeExcessData H
  galoisEquiv : Multiplicative (ExcessGroup H) ≃*
    (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)
  primeIdeal : ℕ → Ideal (𝓞 (ExcessHost target e q d))
  inducing : ExcessCharacter H → BundledDirichletCharacter
  levelPrime₀ : ℕ
  levelPrime₁ : ℕ

namespace AdmissibleExcessData

variable {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
  {H : Type} [AddCommGroup H]

noncomputable def localLog (a : AdmissibleExcessData target e q d H) : ℝ :=
  Real.log ((a.levelPrime₀ : ℝ) * a.levelPrime₁)

noncomputable def localInertia (a : AdmissibleExcessData target e q d H) (p : ℕ) :
    Subgroup (Multiplicative (ExcessGroup H)) :=
  ((a.primeIdeal p).inertia
    (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)).comap
      a.galoisEquiv.toMonoidHom

noncomputable def hostTorsionCharacter (a : AdmissibleExcessData target e q d H) :
    Multiplicative (ExcessGroup H) →*
      (ZMod (NumberField.Units.torsionOrder (ExcessHost target e q d)))ˣ :=
  (numberFieldTorsionCharacter (ExcessHost target e q d)).comp a.galoisEquiv.toMonoidHom

noncomputable def nodeTorsionWeights (a : AdmissibleExcessData target e q d H)
    (ρ : ExcessNode H) : (ZMod (NumberField.Units.torsionOrder (ExcessHost target e q d)))ˣ :=
  a.hostTorsionCharacter (Multiplicative.ofAdd (0, ρ))

/-- The zero-sum relation in Lemma 18.6 after finding the CM-type element
that acts by inversion on the roots of unity. -/
theorem sum_nodeTorsionWeights_eq_zero [Fintype H] (a : AdmissibleExcessData target e q d H)
    (h₀ : H) (hinv : a.hostTorsionCharacter
      (Multiplicative.ofAdd ((0, 1, h₀) : ExcessGroup H)) = -1) :
    (∑ ρ : ExcessNode H, (a.nodeTorsionWeights ρ :
      ZMod (NumberField.Units.torsionOrder (ExcessHost target e q d)))) = 0 := by
  apply sum_nodeWeights_eq_zero_of_pairing _ h₀
  intro h
  have htag : Multiplicative.ofAdd ((0, 0, h) : ExcessGroup H) *
      Multiplicative.ofAdd ((0, 1, h₀) : ExcessGroup H) =
      Multiplicative.ofAdd ((0, 1, h + h₀) : ExcessGroup H) := by
    change ((0, 0, h) : ExcessGroup H) + (0, 1, h₀) = (0, 1, h + h₀)
    simp
  have hmul := (a.hostTorsionCharacter.map_mul
    (Multiplicative.ofAdd ((0, 0, h) : ExcessGroup H))
    (Multiplicative.ofAdd ((0, 1, h₀) : ExcessGroup H))).symm
  rw [htag, hinv] at hmul
  change (a.nodeTorsionWeights (0, h)) * (-1) = a.nodeTorsionWeights (1, h + h₀) at hmul
  have heq := congrArg (fun z : (ZMod (NumberField.Units.torsionOrder (ExcessHost target e q d)))ˣ =>
    (z : ZMod (NumberField.Units.torsionOrder (ExcessHost target e q d)))) hmul
  simpa using heq.symm

end AdmissibleExcessData

/-- Host, scale, and character data of §5 and Definition 18.1 at one point,
before producing the theta-lattice chains. -/
structure AdmissibleExcessConditions {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H] [Fintype H]
    (a : AdmissibleExcessData target e q d H) (x ε C main auxiliary : ℝ) : Prop
    extends HostPrimeConditions (target := target) (e := e) (q := q) (d := d)
      a.prime a.galoisEquiv a.primeIdeal, HostInducingConditions a.prime a.inducing where
  level_prime₀ : a.levelPrime₀.Prime
  level_prime₁ : a.levelPrime₁.Prime
  level_primes_distinct : a.levelPrime₀ ≠ a.levelPrime₁
  level_prime_bounds : ∀ p ∈ ({a.levelPrime₀, a.levelPrime₁} : Finset ℕ),
    (a.averaging.k * a.averaging.b) ^ (8 : ℕ) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ 2 * (a.averaging.k * a.averaging.b) ^ (8 : ℕ)
  b_eq : a.averaging.b = Real.exp (x ^ ε)
  a_eq : a.averaging.a = x * a.averaging.b
  cutoff_eq : a.averaging.thinCutoff = Real.exp (x ^ (ε / 3))
  thin_eq : a.averaging.thinScale = a.averaging.a / a.averaging.thinCutoff
  ambient_bounds : x ^ (2 + 8 * ε) ≤ (Fintype.card H : ℝ) ∧
    (Fintype.card H : ℝ) ≤ 2 * x ^ (2 + 8 * ε)
  selmer_D6 : SelmerLengthBound (numberFieldSelmerLengths (ExcessHost target e q d))
    (Nat.floor (x ^ (400 : ℕ))) (Real.exp (x ^ ε / 2))
  average : ExcessAverageHypotheses a.averaging a.prime.smoothed x
  sizes : ExcessSizeBounds a.averaging.budget x ε
  main_eq : a.averaging.mainValue a.prime.smoothed x = main
  auxiliary_eq : a.averaging.auxiliaryValue a.prime.smoothed x = auxiliary
  corrections : a.averaging.edgeLoss x / a.averaging.budget.normalization +
    a.averaging.correction a.prime.smoothed x ≤ (3 / 13 : ℝ) * x ^ (1 / 2 + (C + 3) * ε)

theorem AdmissibleExcessConditions.smoothed_eq_inducing {target : BundledDirichletCharacter}
    {e : ℕ} {q d : ℕ+} {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary)
    {ψ : ExcessCharacter H} (hψ : ψ ≠ 0) (y : ℝ) :
    a.prime.smoothed ψ y = complexSmoothedCharacterSum (a.inducing ψ) y :=
  ha.toHostInducingConditions.smoothed_eq_inducing hψ y

theorem AdmissibleExcessConditions.auxiliaryValue_eq_inducing_sum
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary) (y : ℝ) :
    a.averaging.auxiliaryValue a.prime.smoothed y =
      ∑ ψ ∈ a.averaging.survivors \ a.averaging.kept,
        ‖complexSmoothedCharacterSum (a.inducing ψ) y‖ := by
  unfold ExcessAverageData.auxiliaryValue
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  have hne : ψ ≠ 0 := by
    intro heq
    subst ψ
    exact (Finset.mem_sdiff.mp hψ).2 ha.average.kept_zero
  rw [ha.smoothed_eq_inducing hne y]

theorem AdmissibleExcessConditions.exceptionalInertia_mem
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary)
    (hd : (d : ℕ).Prime) :
    a.galoisEquiv (Multiplicative.ofAdd ((1, 0, 0) : ExcessGroup H)) ∈
      (a.primeIdeal (d : ℕ)).inertia (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d) := by
  have hinertia : ((1, 0, 0) : ExcessGroup H) ∈ a.prime.inertia (d : ℕ) := by
    rw [← ha.exceptional_eq]
    exact (ha.prime_hypotheses.exceptional_inertia _).mpr (Or.inr rfl)
  exact (ha.inertia_eq d hd ((1, 0, 0) : ExcessGroup H)).mp hinertia

theorem AdmissibleExcessConditions.exceptionalInertia_card
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary) (hd : (d : ℕ).Prime) :
    Nat.card ((a.primeIdeal (d : ℕ)).inertia
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)) = 2 := by
  let E := ExcessHost target e q d
  let G := E ≃ₐ[ℚ] E
  let P := a.primeIdeal (d : ℕ)
  let δ : G := a.galoisEquiv (Multiplicative.ofAdd ((1, 0, 0) : ExcessGroup H))
  have hδ : δ ∈ P.inertia G := ha.exceptionalInertia_mem hd
  have hne : (1 : G) ≠ δ := by
    intro h
    have htag := a.galoisEquiv.injective ((map_one a.galoisEquiv).trans h)
    have hcoord := congrArg (fun t : Multiplicative (ExcessGroup H) => t.toAdd.1) htag
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1) hcoord
  have hset : (P.inertia G : Set G) = {1, δ} := by
    ext σ
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hσ
      let h : ExcessGroup H := (a.galoisEquiv.symm σ).toAdd
      have hmap : a.galoisEquiv (Multiplicative.ofAdd h) = σ := a.galoisEquiv.apply_symm_apply σ
      have hinertia : h ∈ a.prime.inertia (d : ℕ) := by
        apply (ha.inertia_eq d hd h).mpr
        change a.galoisEquiv (Multiplicative.ofAdd h) ∈ P.inertia G
        exact hmap.symm ▸ hσ
      rw [← ha.exceptional_eq] at hinertia
      rcases (ha.prime_hypotheses.exceptional_inertia h).mp hinertia with hzero | hδ'
      · left
        rw [← hmap, hzero]
        exact map_one a.galoisEquiv
      · right
        rw [← hmap, hδ']
    · rintro (rfl | rfl)
      · exact (P.inertia G).one_mem
      · exact hδ
  change (P.inertia G : Set G).ncard = 2
  rw [hset, Set.ncard_pair hne]

/-- A prime greater than three with exceptional inertia of order two
cannot divide the torsion order of the host. -/
theorem AdmissibleExcessConditions.exceptionalPrime_not_dvd_torsionOrder
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary)
    (hd : (d : ℕ).Prime) (hd₃ : 3 < (d : ℕ)) :
    ¬(d : ℕ) ∣ NumberField.Units.torsionOrder (ExcessHost target e q d) := by
  intro hdiv
  let E := ExcessHost target e q d
  let P := a.primeIdeal (d : ℕ)
  let localPrime : P.IsPrime := (ha.prime_over d hd).1
  let localLiesOver : P.LiesOver (Ideal.span {((d : ℕ) : ℤ)}) :=
    ⟨(ha.prime_over d hd).2.symm⟩
  let localRationalPrime : Fact (d : ℕ).Prime := ⟨hd⟩
  let localAbelian : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
  have hr := prime_sub_one_le_ramificationIdx_of_dvd_torsionOrder E (d : ℕ) P hdiv
  rw [numberField_ramificationIdx_eq_inertia_card E (d : ℕ) hd P] at hr
  change (d : ℕ) - 1 ≤ Nat.card ((a.primeIdeal (d : ℕ)).inertia (E ≃ₐ[ℚ] E)) at hr
  rw [ha.exceptionalInertia_card hd] at hr
  omega

/-- The exceptional inertia element fixes the host's roots of unity. -/
theorem AdmissibleExcessConditions.exceptionalInertia_fixes_torsion
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary)
    (hd : (d : ℕ).Prime) (hd₃ : 3 < (d : ℕ))
    (z : NumberField.Units.torsion (ExcessHost target e q d)) :
    numberFieldTorsionAut (ExcessHost target e q d)
      (a.galoisEquiv (Multiplicative.ofAdd ((1, 0, 0) : ExcessGroup H))) z = z := by
  let E := ExcessHost target e q d
  let P := a.primeIdeal (d : ℕ)
  let localPrime : P.IsPrime := (ha.prime_over d hd).1
  let localOver : P.LiesOver (Ideal.span {((d : ℕ) : ℤ)}) :=
    ⟨(ha.prime_over d hd).2.symm⟩
  have hn : P.absNorm ≠ 1 := fun h => localPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hcoprime : P.absNorm.Coprime (NumberField.Units.torsionOrder E) := by
    rw [← Ideal.pow_inertiaDeg (d : ℕ) P]
    exact Nat.Coprime.pow_left _ (hd.coprime_iff_not_dvd.mpr (ha.exceptionalPrime_not_dvd_torsionOrder hd hd₃))
  exact numberFieldTorsionAut_eq_self_of_mem_inertia E (ha.exceptionalInertia_mem hd) hn hcoprime z

/-- The product of complex conjugation and exceptional inertia is the
inversion element of the CM type in Lemma 18.6. -/
theorem AdmissibleExcessConditions.torsion_inversion_of_conjugation
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary)
    (hd : (d : ℕ).Prime) (hd₃ : 3 < (d : ℕ))
    (ι : ExcessHost target e q d →ₐ[ℚ] ℂ) (h₀ : H)
    (hconj : ∀ y, ι (a.galoisEquiv (Multiplicative.ofAdd ((1, 1, h₀) : ExcessGroup H)) y) =
      star (ι y)) :
    ∀ z, numberFieldTorsionAut (ExcessHost target e q d)
      (a.galoisEquiv (Multiplicative.ofAdd ((0, 1, h₀) : ExcessGroup H))) z = z⁻¹ := by
  let E := ExcessHost target e q d
  let τ := Multiplicative.ofAdd ((1, 1, h₀) : ExcessGroup H)
  let δ := Multiplicative.ofAdd ((1, 0, 0) : ExcessGroup H)
  have htag : τ * δ = Multiplicative.ofAdd ((0, 1, h₀) : ExcessGroup H) := by
    change ((1, 1, h₀) : ExcessGroup H) + (1, 0, 0) = (0, 1, h₀)
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    simp [htwo]
  intro z
  change numberFieldTorsionAction E
    (a.galoisEquiv (Multiplicative.ofAdd ((0, 1, h₀) : ExcessGroup H))) z = z⁻¹
  rw [← htag, map_mul, map_mul]
  change numberFieldTorsionAut E (a.galoisEquiv τ)
    (numberFieldTorsionAut E (a.galoisEquiv δ) z) = z⁻¹
  rw [ha.exceptionalInertia_fixes_torsion hd hd₃ z]
  exact numberFieldTorsionAut_eq_inv_of_embedding_conj E ι (a.galoisEquiv τ) hconj z

/-- Proposition 18.7 at the arithmetic host, given the character of the
Galois action on its roots of unity and the zero-sum relation of Lemma 18.6. -/
theorem AdmissibleExcessConditions.exists_hostNodeBases
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary)
    (u : H) (thinWeight : H → ℤ)
    (κ : ExcessNode H → (ZMod (NumberField.Units.torsionOrder (ExcessHost target e q d)))ˣ)
    (hκ : (∑ ρ : ExcessNode H, (κ ρ : ZMod
      (NumberField.Units.torsionOrder (ExcessHost target e q d)))) = 0) :
    ∃ base : ExcessNode H → ℤ, a.averaging.CanonicalNodeBases u κ
      (fun t => thinWeight t + Int.floor (a.averaging.thinScale / x))
      (Int.ceil a.averaging.b) (Int.ceil (a.averaging.thinScale / (x * Fintype.card H)))
      (Int.ceil (x ^ (402 : ℕ))) base := by
  let localNonzero : NeZero (NumberField.Units.torsionOrder (ExcessHost target e q d)) :=
    ⟨NumberField.Units.torsionOrder_ne_zero (ExcessHost target e q d)⟩
  exact a.averaging.exists_canonicalNodeBases u κ hκ _ _ _ _ ha.average.thick_nonempty

theorem AdmissibleExcessConditions.exists_hostNodeBases_of_conjugation
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary)
    (u : H) (thinWeight : H → ℤ) (hd : (d : ℕ).Prime) (hd₃ : 3 < (d : ℕ))
    (ι : ExcessHost target e q d →ₐ[ℚ] ℂ) (h₀ : H)
    (hconj : ∀ y, ι (a.galoisEquiv (Multiplicative.ofAdd ((1, 1, h₀) : ExcessGroup H)) y) =
      star (ι y)) :
    ∃ base : ExcessNode H → ℤ, a.averaging.CanonicalNodeBases u a.nodeTorsionWeights
      (fun t => thinWeight t + Int.floor (a.averaging.thinScale / x))
      (Int.ceil a.averaging.b) (Int.ceil (a.averaging.thinScale / (x * Fintype.card H)))
      (Int.ceil (x ^ (402 : ℕ))) base := by
  have hinv := ha.torsion_inversion_of_conjugation hd hd₃ ι h₀ hconj
  have hneg : a.hostTorsionCharacter (Multiplicative.ofAdd ((0, 1, h₀) : ExcessGroup H)) = -1 :=
    numberFieldTorsionCharacter_eq_neg_one_of_inv _ _ hinv
  exact ha.exists_hostNodeBases u thinWeight a.nodeTorsionWeights
    (a.sum_nodeTorsionWeights_eq_zero h₀ hneg)

/-- The canonical node bases require only the two conjugation signs in the
admissible Galois coordinates and the exceptional-prime conditions. -/
theorem AdmissibleExcessConditions.exists_hostNodeBases_of_windowPair
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {base x ε C main auxiliary : ℝ}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary)
    (hpair : SelmerWindowPair ε base q d) (ι : ExcessHost target e q d →ₐ[ℚ] ℂ)
    (u : H) (thinWeight : H → ℤ) :
    ∃ nodes : ExcessNode H → ℤ, a.averaging.CanonicalNodeBases u a.nodeTorsionWeights
      (fun t => thinWeight t + Int.floor (a.averaging.thinScale / x))
      (Int.ceil a.averaging.b) (Int.ceil (a.averaging.thinScale / (x * Fintype.card H)))
      (Int.ceil (x ^ (402 : ℕ))) nodes := by
  let E := ExcessHost target e q d
  let localAbelian : IsAbelianGalois ℚ E := selmerHostField_isAbelianGalois target e q d
  obtain ⟨σ, hσ, _⟩ := existsUnique_numberFieldConjugation E ι
  have hsign := ha.conjugation_signs ι σ hσ
  let h := (a.galoisEquiv.symm σ).toAdd
  have hcoords : ((1, 1, h.2.2) : ExcessGroup H) = h :=
    Prod.ext hsign.1.symm (Prod.ext hsign.2.symm rfl)
  have hσcoord : a.galoisEquiv (Multiplicative.ofAdd ((1, 1, h.2.2) : ExcessGroup H)) = σ := by
    rw [hcoords]
    exact a.galoisEquiv.apply_symm_apply σ
  have hd₃ : 3 < (d : ℕ) := by
    have hmod := Nat.mod_le (d : ℕ) 16
    rw [hpair.d_residue] at hmod
    omega
  exact ha.exists_hostNodeBases_of_conjugation u thinWeight hpair.d_prime hd₃ ι h.2.2
    (fun y => hσcoord ▸ hσ y)

def HasAdmissibleHostPoint (target : BundledDirichletCharacter) (e : ℕ) (q d : ℕ+)
    (x ε C main auxiliary : ℝ) : Prop :=
  ∃ (H : Type) (group : AddCommGroup H) (finite : Fintype H),
    letI : AddCommGroup H := group
    letI : Fintype H := finite
    ∃ a : AdmissibleExcessData target e q d H,
      AdmissibleExcessConditions a x ε C main auxiliary

/-- Chain records on the same field as the admissible host, using its root discriminant. -/
def HasAdmissibleHostChainRecords {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H] [Fintype H] (a : AdmissibleExcessData target e q d H)
    (x ε : ℝ) (c : ChainConstants) : Prop :=
  ∀ u ∈ a.averaging.subgroup,
    let p := a.averaging.chainInputs a.prime u x ε
      (NumberField.rootDiscr (ExcessHost target e q d)) a.localLog
    ∃ (U : Type) (r : ChainRecord U p.budget.steps),
      ChainConditions p c r ∧ ChainErrorSizes p c r.indices.card

theorem admissibleExcess_of_hostChainRecords {target : BundledDirichletCharacter} {e : ℕ}
    {q d : ℕ+} {H : Type} [AddCommGroup H] [Fintype H]
    {a : AdmissibleExcessData target e q d H} {x ε C main auxiliary : ℝ} {c : ChainConstants}
    (ha : AdmissibleExcessConditions a x ε C main auxiliary) (hc : c.Valid)
    (hC : c.errorExponent ≤ C) (hchain : HasAdmissibleHostChainRecords a x ε c) :
    HasFiniteExcessWitness x ε C main auxiliary := by
  have hroot : 0 < NumberField.rootDiscr (ExcessHost target e q d) :=
    zero_lt_one.trans_le (one_le_rootDiscr _)
  exact ⟨H, inferInstance, inferInstance, a.averaging, a.prime.smoothed,
    ha.average, ha.sizes, ha.main_eq, ha.auxiliary_eq,
    ⟨a.prime, NumberField.rootDiscr (ExcessHost target e q d), a.localLog,
      c, ha.prime_hypotheses, rfl, hroot, hc, hC, hchain⟩, ha.corrections⟩

/-- Cohomologically admissible windows with one auxiliary prime pair per window,
and the fixed positive combination from §6.3. -/
def HasPreparedExcessWindows (C : ℝ) : Prop :=
  ∀ target : BundledDirichletCharacter, target.character.IsPrimitive →
    ∃ (n : ℕ) (family : Fin n → BundledDirichletCharacter) (weight : Fin n → ℝ),
      (∀ i, (family i).character ≠ 1) ∧ (∀ i, 0 < weight i) ∧
      (target.character ≠ 1 → ∃ i, family i = target) ∧
      ∃ ε₀ K : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 52 ∧ 0 ≤ K ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∃ J : ℝ, 2 ≤ J ∧ ∀ lower : ℝ,
            ∃ (base Y : ℝ) (q d : ℕ+) (e : ℝ → ℕ) (nAux : ℕ)
              (aux : Fin nAux → BundledDirichletCharacter),
              max 1 lower ≤ Y ∧ 3 ≤ base ∧ base ≤ Y ∧ Y ^ (2 : ℕ) ≤ base ^ J ∧
              SelmerWindowPair ε base q d ∧ (nAux : ℝ) ≤ K ∧
              (∀ i, (aux i).character.IsPrimitive ∧ (aux i).character ≠ 1) ∧
              ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)),
                (∀ i, ‖complexSmoothedCharacterSum (aux i) x‖ ≤ x ^ (1 / 2 + ε)) ∧
                HasAdmissibleHostPoint target (e x) q d x ε C
                  (smoothedCombination family weight x)
                  (∑ i, ‖complexSmoothedCharacterSum (aux i) x‖)

end Riemann
