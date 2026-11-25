module

public import Riemann.SelmerWindowBound
public import Riemann.SelmerCyclotomicTowerBounds
import Utilities.CyclotomicLayerDiscriminant
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Utilities.ExponentialGrowth

@[expose] public section

open Filter Asymptotics Utilities
open scoped BigOperators

namespace Riemann

/-- The common dyadic and twist range for the small-prime estimates. -/
def SelmerSmallPrimeAdmissible (e t : ℝ → ℕ) : Prop :=
  ∀ x ≥ 2, 2 ≤ e x ∧ (2 : ℝ) ^ e x ≤ x ^ (4 : ℕ) ∧
    2 ≤ t x ∧ (t x : ℝ) ≤ x ^ (401 : ℕ)

/-- The bound on any fixed-depth cyclotomic layer over the odd-prime auxiliary field. -/
def SelmerOddLayerBound (target : BundledDirichletCharacter) (ℓ j t : ℕ) (B : ℝ) : Prop :=
  let F := CyclotomicField (ℓ * (target.modulus : ℕ)) ℚ
  ∀ (L : Type) [Field L] [NumberField L] [Algebra F L],
    IsPrimePowerCyclotomicLayer ℓ j F L →
    SelmerPrimeLengthBound (numberFieldSelmerLengths L) ℓ t B

/-- Uniform arithmetic data on the dyadic base, including the comparison
between the host and a deeper layer over this base. -/
theorem selmerTwo_cyclotomicBaseData
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive) :
    ∃ R nBase : ℕ,
      ∀ (q d : ℕ+), SelmerEstimatePrimePair target q d →
        ∃ (F : Type) (_ : Field F) (_ : NumberField F) (c : ℕ),
          (∃ z : F, IsPrimitiveRoot z (2 ^ c)) ∧
          SelmerCyclotomicTowerRootBound F 2 R c Nat.prime_two ∧
          SelmerCyclotomicCokernelPresentation F 2 R Nat.prime_two ∧
          (∃ z : F, IsPrimitiveRoot z 4) ∧
          Module.finrank ℚ F ≤ nBase ∧
          Nonempty (F →ₐ[ℚ] CyclotomicField
            ((4 * (target.modulus : ℕ)) * ((q : ℕ) * (d : ℕ))) ℚ) ∧
          ∀ e : ℕ, 2 ≤ e →
            ∃ (m : ℕ) (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L),
              IsPrimePowerCyclotomicLayer 2 m F L ∧ m ≤ e + 2 ∧
              ∀ i : ℕ, 1 ≤ i → numberFieldSelmerLengths (selmerHostField target e q d) 2 i ≤
                1 + numberFieldSelmerLengths L 2 i := by
  sorry

/-- The arithmetic profile of the fixed odd-prime cyclotomic base. -/
theorem selmerOdd_cyclotomicBaseProfile
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    ∃ R c : ℕ,
      let F := CyclotomicField (ℓ * (target.modulus : ℕ)) ℚ
      SelmerCyclotomicTowerRootBound F ℓ R c hℓ ∧ SelmerCyclotomicCokernelPresentation F ℓ R hℓ := by
  sorry

/-- Uniform arithmetic data for the dyadic base and the layers that bound
the host length up to an additive one per twist. -/
theorem selmerTwo_cyclotomicTowerData
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive) :
    ∃ (R c N : ℕ) (K D : ℝ), 1 ≤ K ∧ 0 ≤ D ∧
      ∀ (q d : ℕ+), SelmerEstimatePrimePair target q d →
        ∃ (F L₀ : Type) (_ : Field F) (_ : NumberField F)
            (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra F L₀),
          SelmerCyclotomicTowerProfile F 2 R c K ∧
          IsPrimePowerCyclotomicLayer 2 (selmerCyclotomicReferenceDepth 2 R) F L₀ ∧
          Module.finrank ℚ L₀ ≤ N ∧
          Real.log (2 * ((NumberField.discr L₀).natAbs : ℝ)) ≤
            D * (1 + Real.log ((q : ℕ) * (d : ℕ) : ℝ)) ∧
          ∀ e : ℕ, 2 ≤ e →
            ∃ (m : ℕ) (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L),
              IsPrimePowerCyclotomicLayer 2 m F L ∧ m ≤ e + 2 ∧
              ∀ i : ℕ, 1 ≤ i → numberFieldSelmerLengths (selmerHostField target e q d) 2 i ≤
                1 + numberFieldSelmerLengths L 2 i := by
  obtain ⟨R, nBase, hbase⟩ := selmerTwo_cyclotomicBaseData target hprim
  obtain ⟨K, hK, hbudget⟩ := exists_selmerIntegralTateH2_torsionBudget
  let modulus := 4 * (target.modulus : ℕ)
  have hmodulus : 0 < modulus := Nat.mul_pos (by norm_num) target.modulus.pos
  obtain ⟨N, D, hD, hgeometry⟩ :=
    exists_primePowerCyclotomicLayer_discriminant_bound 2 (selmerCyclotomicReferenceDepth 2 R)
      nBase modulus Nat.prime_two hmodulus
  refine ⟨R, 2 * nBase, N, K, D, hK, hD, ?_⟩
  intro q d hpair
  obtain ⟨F, _, _, c, ⟨u, hu⟩, hroots, hpresentation, ⟨z, hz⟩, hdegree, ⟨f⟩, hhost⟩ := hbase q d hpair
  have hc : c ≤ 2 * nBase :=
    Nat.lt_two_pow_self.le.trans ((primePow_le_two_mul_finrank_of_isPrimitiveRoot F Nat.prime_two hu).trans
      (Nat.mul_le_mul_left 2 hdegree))
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hμ : HasSmallPrimeTorsionRoots F 2 := ⟨z, by simpa using hz⟩
  have hdepth := selmerCyclotomicTowerDepthBound_of_cokernelPresentation
    Nat.prime_two hpresentation
  have href := selmerCyclotomicTowerReferenceBound_of_depthBound hμ hdepth hbudget
  have hroot : ∃ u : F, IsPrimitiveRoot u 2 := ⟨z ^ 2, hz.pow (by norm_num) (by norm_num)⟩
  obtain ⟨L₀, _, _, _, hL₀⟩ :=
    exists_primePowerCyclotomicLayer F Nat.prime_two hroot (selmerCyclotomicReferenceDepth 2 R)
  obtain ⟨hN, hdisc⟩ := hgeometry ((q : ℕ) * (d : ℕ)) (Nat.mul_pos q.pos d.pos)
    F L₀ hdegree f hL₀
  push_cast at hdisc
  exact ⟨F, L₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    selmerCyclotomicTowerProfile_of_rootBound Nat.prime_two (hroots.mono hc) href, hL₀, hN, hdisc, hhost⟩

/-- The arithmetic data over the fixed odd-prime cyclotomic base, with its
reference layer. -/
theorem selmerOdd_cyclotomicTowerData
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    ∃ (R c : ℕ) (K : ℝ), 1 ≤ K ∧
      let F := CyclotomicField (ℓ * (target.modulus : ℕ)) ℚ
      ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra F L₀),
        SelmerCyclotomicTowerProfile F ℓ R c K ∧
        IsPrimePowerCyclotomicLayer ℓ (selmerCyclotomicReferenceDepth ℓ R) F L₀ := by
  obtain ⟨R, c, hroots, hpresentation⟩ := selmerOdd_cyclotomicBaseProfile target hprim ℓ hℓ hodd
  obtain ⟨K, hK, hbudget⟩ := exists_selmerIntegralTateH2_torsionBudget
  let _ : Fact ℓ.Prime := ⟨hℓ⟩
  let N := ℓ * (target.modulus : ℕ)
  let F := CyclotomicField N ℚ
  have hN : 0 < N := Nat.mul_pos hℓ.pos target.modulus.pos
  let _ : NeZero N := ⟨hN.ne'⟩
  let _ : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  let _ : IsCyclotomicExtension {N} ℚ F := CyclotomicField.isCyclotomicExtension N ℚ
  let z := IsCyclotomicExtension.zeta N ℚ F
  have hz : IsPrimitiveRoot z N := IsCyclotomicExtension.zeta_spec N ℚ F
  have hroot : ∃ u : F, IsPrimitiveRoot u ℓ := ⟨z ^ (target.modulus : ℕ),
    hz.pow hN (Nat.mul_comm _ _)⟩
  have hμ : HasSmallPrimeTorsionRoots F ℓ := by
    simpa only [HasSmallPrimeTorsionRoots, ite_eq_right hodd] using hroot
  have hdepth := selmerCyclotomicTowerDepthBound_of_cokernelPresentation
    hℓ hpresentation
  have href := selmerCyclotomicTowerReferenceBound_of_depthBound hμ hdepth hbudget
  obtain ⟨L₀, _, _, _, hL₀⟩ :=
    exists_primePowerCyclotomicLayer F hℓ hroot (selmerCyclotomicReferenceDepth ℓ R)
  exact ⟨R, c, K, hK, L₀, inferInstance, inferInstance, inferInstance,
    selmerCyclotomicTowerProfile_of_rootBound hℓ hroots href, hL₀⟩

private theorem exists_windowThreshold {J : ℝ} {P : ℝ → Prop} (hJ : 0 < J)
    (hP : ∀ᶠ x in atTop, P x) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, 1 ≤ X ∧ ∀ x ≥ X ^ (1 / J), P x := by
  obtain ⟨x₀, h₀⟩ := eventually_atTop.mp hP
  let U := max 1 x₀
  have hU : 1 ≤ U := le_max_left _ _
  have hU₀ := zero_le_one.trans hU
  refine ⟨U ^ J, fun X hX => ⟨(Real.one_le_rpow hU hJ.le).trans hX, fun x hx => ?_⟩⟩
  have hUX : U ≤ X ^ (1 / J) := calc
    _ = (U ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hU₀ hJ.ne']
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hU₀ _) hX (by positivity)
  exact h₀ x ((le_max_right 1 x₀).trans (hUX.trans hx))

private theorem scale_quarter_rpow_le {X x ε J : ℝ} (hX : 0 ≤ X) (hε : 0 < ε)
    (hx : X ^ (1 / J) ≤ x) :
    X ^ (ε / (4 * J)) ≤ x ^ (ε / 4) := by
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hX _) hx (show 0 ≤ ε / 4 by positivity)
  rwa [← Real.rpow_mul hX, show 1 / J * (ε / 4) = ε / (4 * J) by ring] at hpow

/-- The dyadic estimates on scales avoiding a bounded finite set of
exceptions. This is the input from the archived PartA. -/
theorem selmerTwo_exceptionalScaleControl
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive) :
    ∃ (R : ℕ) (K : ℝ), 1 ≤ K ∧
      ∀ (ε J : ℝ), 0 < ε → ε < 1 / 52 → 0 < J →
        ∀ e t : ℝ → ℕ, SelmerSmallPrimeAdmissible e t → ∃ X₀ : ℝ,
          ∀ X ≥ X₀, ∀ q d : ℕ+, SelmerEstimatePrimePair target q d →
            Real.log ((q : ℕ) * (d : ℕ) : ℝ) ≤ X ^ (ε / (4 * J)) →
            ∃ exc : Finset ℕ, exc.card ≤ R ∧
              ∀ x ∈ Set.Icc (X ^ (1 / J)) X, 2 ≤ x →
                GoodFiniteScale (ε / (2 * K)) 401 exc x →
                TwoSelmerLengthBound (numberFieldSelmerLengths (selmerHostField target (e x) q d))
                  (t x) (Real.exp (x ^ (4 * ε / 5))) := by
  obtain ⟨R, c, N, K, D, hK, hD, hdata⟩ := selmerTwo_cyclotomicTowerData target hprim
  refine ⟨R, K, hK, fun ε J hε _ hJ e t hadm => ?_⟩
  obtain ⟨C, hC, hpoint⟩ := selmerCyclotomicTower_pointwiseOnScales
    (R := R) (c := c) (N := N) (ε := ε) Nat.prime_two hK
    (D := 2 * D) (by positivity) (a := 8) (by norm_num) (T := 401) (by norm_num) hJ hε
  obtain ⟨X₀, hX₀⟩ := exists_windowThreshold hJ
    (eventually_rpow_mul_selmerCyclotomicPointBudget_le 401 hC hε)
  refine ⟨X₀, fun X hX q d hpair hqd => ?_⟩
  obtain ⟨hX₁, hbudget⟩ := hX₀ X hX
  obtain ⟨F, L₀, _, _, _, _, _, hprof, hL₀, hdegree, hdisc, hcomp⟩ := hdata q d hpair
  obtain ⟨exc, hcard, hpoint⟩ := hpoint F L₀ hprof hL₀ hdegree X hX₁
  refine ⟨exc, hcard, fun x hx hx₂ hgood => ?_⟩
  have hx₁ : 1 ≤ x := by linarith
  obtain ⟨he, hex, _, htx⟩ := hadm x hx₂
  obtain ⟨m, L, _, _, _, hL, hm, hcmp⟩ := hcomp (e x) he
  have hm' : (m : ℝ) ≤ 8 * (1 + Real.log x) := by
    have helog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ e x) hex
    rw [Real.log_pow, Real.log_pow] at helog
    norm_num at helog
    have hlog₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hmcast : (m : ℝ) ≤ (e x : ℝ) + 2 := by exact_mod_cast hm
    nlinarith only [helog, hmcast, mul_le_mul_of_nonneg_left hlog₂ (Nat.cast_nonneg (e x))]
  have hqd' := hqd.trans (scale_quarter_rpow_le (zero_le_one.trans hX₁) hε hx.1)
  have hdisc' : Real.log (2 * ((NumberField.discr L₀).natAbs : ℝ)) ≤ 2 * D * x ^ (ε / 4) := by
    have hw : 1 ≤ x ^ (ε / 4) := Real.one_le_rpow hx₁ (by positivity)
    refine hdisc.trans ?_
    have h := mul_le_mul_of_nonneg_left (add_le_add hw hqd') hD
    linarith only [h]
  rw [← Real.rpow_natCast] at htx
  refine selmerPrimeLengthBound_of_pointwise (selmerCyclotomicPointBudget_nonneg hC hx₁)
    htx (hbudget x hx.1) fun i hi => ?_
  have hi₁ := (Finset.mem_Ico.mp hi).1
  have hiₓ := (show (i : ℝ) ≤ t x by exact_mod_cast (Finset.mem_Ico.mp hi).2.le).trans htx
  obtain ⟨hfin, hlen⟩ := hpoint x hx hx₁ hgood hdisc' m L hL hm' i hi₁ hiₓ
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hle : numberFieldSelmerLengths (selmerHostField target (e x) q d) 2 i ≤
      (↑(1 + n : ℕ) : WithTop ℕ) := by
    calc
      _ ≤ 1 + numberFieldSelmerLengths L 2 i := hcmp i hi₁
      _ = (1 : WithTop ℕ) + (n : WithTop ℕ) := congrArg (fun z => 1 + z) hn.symm
      _ = _ := (WithTop.coe_add (α := ℕ) 1 n).symm
  refine ⟨ne_top_of_le_ne_top WithTop.coe_ne_top hle, ?_⟩
  have hnat := WithTop.untopD_le (a := 0) hle
  rw [← hn] at hlen
  change (n : ℝ) + 1 ≤ _ at hlen
  have hreal : (((numberFieldSelmerLengths (selmerHostField target (e x) q d) 2 i).untopD 0 : ℕ) : ℝ)
      ≤ 1 + (n : ℝ) := by exact_mod_cast hnat
  linarith only [hreal, hlen]

/-- The fixed odd-layer estimates on scales avoiding a bounded finite
set of exceptions. This is the input from the archived PartB. -/
theorem selmerOddLayer_exceptionalScaleControl
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    ∃ (R j : ℕ) (K : ℝ), 1 ≤ K ∧
      ∀ (ε J : ℝ), 0 < ε → ε < 1 / 52 → 0 < J →
        ∀ e t : ℝ → ℕ, SelmerSmallPrimeAdmissible e t → ∃ X₀ : ℝ,
          ∀ X ≥ X₀, ∃ exc : Finset ℕ, exc.card ≤ R ∧
            ∀ x ∈ Set.Icc (X ^ (1 / J)) X, 2 ≤ x →
              GoodFiniteScale (ε / (2 * K)) 401 exc x →
                SelmerOddLayerBound target ℓ j (t x) (Real.exp (x ^ (4 * ε / 5))) := by
  obtain ⟨R, c, K, hK, L₀, _, _, _, hprof, hL₀⟩ :=
    selmerOdd_cyclotomicTowerData target hprim ℓ hℓ hodd
  let j := selmerCyclotomicReferenceDepth ℓ R
  let D := |Real.log (2 * ((NumberField.discr L₀).natAbs : ℝ))|
  refine ⟨R, j, K, hK, fun ε J hε _ hJ e t hadm => ?_⟩
  obtain ⟨C, hC, hpoint⟩ := selmerCyclotomicTower_pointwiseOnScales
    (R := R) (c := c) (N := Module.finrank ℚ L₀) (a := (j : ℝ)) (T := 401)
    (ε := ε) hℓ hK (D := D) (abs_nonneg _) (Nat.cast_nonneg _) (by norm_num) hJ hε
  obtain ⟨X₀, hX₀⟩ := exists_windowThreshold hJ
    (eventually_rpow_mul_selmerCyclotomicPointBudget_le 401 hC hε)
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hX₁, hbudget⟩ := hX₀ X hX
  obtain ⟨exc, hcard, hpoint⟩ := hpoint _ L₀ hprof hL₀ le_rfl X hX₁
  refine ⟨exc, hcard, fun x hx hx₂ hgood L _ _ _ hL => ?_⟩
  have hx₁ : 1 ≤ x := by linarith
  have htx := (hadm x hx₂).2.2.2
  rw [← Real.rpow_natCast] at htx
  have hdisc : Real.log (2 * ((NumberField.discr L₀).natAbs : ℝ)) ≤ D * x ^ (ε / 4) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_rpow hx₁ (by positivity)))
  have hm : (j : ℝ) ≤ (j : ℝ) * (1 + Real.log x) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith [Real.log_nonneg hx₁])
  refine selmerPrimeLengthBound_of_pointwise (selmerCyclotomicPointBudget_nonneg hC hx₁)
    htx (hbudget x hx.1) fun i hi => ?_
  have hiₓ := (show (i : ℝ) ≤ t x by exact_mod_cast (Finset.mem_Ico.mp hi).2.le).trans htx
  obtain ⟨hfin, hlen⟩ := hpoint x hx hx₁ hgood hdisc j L hL hm i (Finset.mem_Ico.mp hi).1 hiₓ
  exact ⟨hfin, by linarith only [hlen]⟩

/-- The integral comparison transfers one odd-prime layer bound to the
weighted plus length on the host. The polynomial term includes the
bounded character counts and the descent losses. -/
theorem selmerPlus_badPrime_of_layerBound
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    (ℓ j : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    ∃ (A : ℕ) (P : ℝ),
      ∀ (e t : ℕ) (q d : ℕ+), 2 ≤ e → 2 ≤ t → SelmerEstimatePrimePair target q d →
        max P (2 * (t : ℝ) + 1) < (q : ℕ) → max P (2 * (t : ℝ) + 1) < (d : ℕ) →
        ∀ B : ℝ, 0 ≤ B → SelmerOddLayerBound target ℓ j t B →
          let L := numberFieldSelmerSignLengths true (selmerHostField target e q d)
          (∀ i ∈ Finset.Ico 1 t, L ℓ i ≠ ⊤) ∧
            selmerWeightedLength L t ℓ ≤ ((selmerHostModulus target e q d : ℝ) * t) ^ A + A * B := by
  sorry

/-- Transfer the layer bounds to the bad odd-prime part of the host.
The polynomial term from the character counts is retained at this stage. -/
theorem selmerPlus_badPrimes_of_layerBounds
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    (bad : Finset ℕ) (hbad : ∀ ℓ ∈ bad, ℓ.Prime ∧ ℓ ≠ 2)
    (j : ℕ → ℕ) :
    ∃ (A : ℕ) (P : ℝ), 0 < P ∧
      ∀ (e t : ℕ) (q d : ℕ+), 2 ≤ e → 2 ≤ t → SelmerEstimatePrimePair target q d →
        max P (2 * (t : ℝ) + 1) < (q : ℕ) → max P (2 * (t : ℝ) + 1) < (d : ℕ) →
        ∀ B : ℝ, 0 ≤ B → (∀ ℓ ∈ bad, SelmerOddLayerBound target ℓ (j ℓ) t B) →
          let L := numberFieldSelmerSignLengths true (selmerHostField target e q d)
          (∀ ℓ ∈ bad, ∀ i ∈ Finset.Ico 1 t, L ℓ i ≠ ⊤) ∧
            (∑ ℓ ∈ bad, selmerWeightedLength L t ℓ) ≤
              ((selmerHostModulus target e q d : ℝ) * t) ^ A + A * B := by
  classical
  have hper ℓ (h : ℓ ∈ bad) :=
    selmerPlus_badPrime_of_layerBound target hprim ℓ (j ℓ) (hbad ℓ h).1 (hbad ℓ h).2
  choose! A P hbound using hper
  let A₀ := ∑ ℓ ∈ bad, A ℓ
  let P₀ := 1 + ∑ ℓ ∈ bad, |P ℓ|
  have hP₀ : 0 < P₀ := by dsimp [P₀]; positivity
  refine ⟨A₀ + bad.card, P₀, hP₀, fun e t q d he ht hpair hq hd B hB hlayer => ?_⟩
  let L := numberFieldSelmerSignLengths true (selmerHostField target e q d)
  let M := (selmerHostModulus target e q d : ℝ) * t
  have hM : 2 ≤ M := by
    have hN : (1 : ℝ) ≤ selmerHostModulus target e q d := by
      exact_mod_cast selmerHostModulus_pos target e q d
    exact (by exact_mod_cast ht : (2 : ℝ) ≤ t).trans (le_mul_of_one_le_left (by positivity) hN)
  have hsingle ℓ (hℓ : ℓ ∈ bad) :
      (∀ i ∈ Finset.Ico 1 t, L ℓ i ≠ ⊤) ∧ selmerWeightedLength L t ℓ ≤ M ^ A ℓ + A ℓ * B := by
    have hP : P ℓ ≤ P₀ :=
      (le_abs_self _).trans ((Finset.single_le_sum (fun k _ => abs_nonneg (P k)) hℓ).trans
        (by dsimp only [P₀]; linarith))
    have hcut := max_le_max_right (2 * (t : ℝ) + 1) hP
    exact hbound ℓ hℓ e t q d he ht hpair (hcut.trans_lt hq) (hcut.trans_lt hd) B hB (hlayer ℓ hℓ)
  have hpow : (∑ ℓ ∈ bad, M ^ A ℓ) ≤ M ^ (A₀ + bad.card) := by
    have hcard : (bad.card : ℝ) ≤ M ^ bad.card :=
      (by exact_mod_cast (Nat.lt_two_pow_self (n := bad.card)).le :
        (bad.card : ℝ) ≤ (2 : ℝ) ^ bad.card).trans (pow_le_pow_left₀ (by norm_num) hM _)
    calc
      _ ≤ ∑ _ℓ ∈ bad, M ^ A₀ := Finset.sum_le_sum fun ℓ hℓ =>
        pow_le_pow_right₀ (by linarith) (Finset.single_le_sum (fun k _ => Nat.zero_le (A k)) hℓ)
      _ = M ^ A₀ * (bad.card : ℝ) := by simp [mul_comm]
      _ ≤ M ^ A₀ * M ^ bad.card := mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = _ := (pow_add _ _ _).symm
  have hlinear : (∑ ℓ ∈ bad, (A ℓ : ℝ) * B) ≤ (A₀ + bad.card : ℕ) * B := by
    rw [← Finset.sum_mul, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right A₀ bad.card) hB
  refine ⟨fun ℓ hℓ => (hsingle ℓ hℓ).1, ?_⟩
  exact (Finset.sum_le_sum fun ℓ hℓ => (hsingle ℓ hℓ).2).trans
    (by rw [Finset.sum_add_distrib]; exact add_le_add hpow hlinear)

/-- On the logarithmic range of the small-prime windows, the polynomial
term from the bad-prime transfer is absorbed by the exponential allowance. -/
theorem eventually_selmerSmallPrimePolynomial_le (target : BundledDirichletCharacter)
    (A : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (e t : ℕ) (q d : ℕ+),
      (2 : ℝ) ^ e ≤ x ^ (4 : ℕ) → 0 < t → (t : ℝ) ≤ x ^ (401 : ℕ) →
      Real.log ((q : ℕ) * (d : ℕ) : ℝ) ≤ x ^ (ε / 4) →
      ((selmerHostModulus target e q d : ℝ) * t) ^ A ≤ Real.exp (x ^ (4 * ε / 5)) := by
  let N₀ : ℝ := (target.modulus : ℕ)
  have hN₀ : 0 < N₀ := by
    dsimp [N₀]
    exact_mod_cast target.modulus.pos
  have hgap : 0 < ε / 4 := by positivity
  have hconst := isLittleO_const_rpow_atTop (Real.log 4 + Real.log N₀) hgap
  have hlog := (isLittleO_log_rpow_atTop hgap).const_mul_left (405 : ℝ)
  have hpow := (tendsto_rpow_atTop (show 0 < 4 * ε / 5 - ε / 4 by linarith)).eventually_ge_atTop
    (2 * (A : ℝ))
  filter_upwards [((hconst.add hlog).bound zero_lt_one), hpow, eventually_ge_atTop (1 : ℝ)]
    with x hsmall hA hx e t q d he ht htupper hqd
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hsmall' : Real.log 4 + Real.log N₀ + 405 * Real.log x ≤ x ^ (ε / 4) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _), one_mul, Real.norm_eq_abs] at hsmall
    exact (le_abs_self _).trans hsmall
  have helog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ e) he
  rw [Real.log_pow, Real.log_pow] at helog
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have htlog := Real.log_le_log htpos htupper
  rw [Real.log_pow] at htlog
  let N := selmerHostModulus target e q d
  have hN : (0 : ℝ) < N := by exact_mod_cast selmerHostModulus_pos target e q d
  have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  have hd : (0 : ℝ) < (d : ℕ) := by exact_mod_cast d.pos
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ (e + 2) * N₀ * ((q : ℕ) * (d : ℕ)) := by
    rw [← mul_assoc]
    dsimp only [N, N₀]
    exact_mod_cast selmerHostModulus_le_product target e q d
  have hNlog := Real.log_le_log hN hNle
  rw [Real.log_mul (by positivity) (mul_ne_zero hq.ne' hd.ne'),
    Real.log_mul (by positivity) hN₀.ne', pow_add, Real.log_mul (by positivity) (by norm_num),
    Real.log_pow, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] at hNlog
  have hNt : Real.log ((N : ℝ) * t) ≤ 2 * x ^ (ε / 4) := by
    rw [Real.log_mul hN.ne' htpos.ne']
    push_cast at helog htlog
    linarith only [helog, htlog, hNlog, hqd, hsmall']
  have hbudget : (A : ℝ) * Real.log ((N : ℝ) * t) ≤ x ^ (4 * ε / 5) := by
    calc
      _ ≤ (A : ℝ) * (2 * x ^ (ε / 4)) := mul_le_mul_of_nonneg_left hNt (by positivity)
      _ = (2 * (A : ℝ)) * x ^ (ε / 4) := by ring
      _ ≤ x ^ (4 * ε / 5 - ε / 4) * x ^ (ε / 4) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ = _ := by rw [← Real.rpow_add hx₀, sub_add_cancel]
  calc
    ((N : ℝ) * t) ^ A = Real.exp ((A : ℝ) * Real.log ((N : ℝ) * t)) := by
      rw [Real.exp_nat_mul, Real.exp_log (mul_pos hN htpos)]
    _ ≤ _ := Real.exp_le_exp.mpr hbudget

/-- Simultaneous windows for the prime two and the finitely many bad odd
primes, using the same cutoff and the same host parameters. -/
theorem selmerPlus_two_badPrime_windows
    (target : BundledDirichletCharacter) (hprim : target.character.IsPrimitive)
    (ε : ℝ) (hε : 0 < ε) (hsmall : ε < 1 / 52) (e t : ℝ → ℕ)
    (hadm : SelmerSmallPrimeAdmissible e t)
    (bad : Finset ℕ) (hbad : ∀ ℓ ∈ bad, ℓ.Prime ∧ ℓ ≠ 2) :
    ∃ J C P X₁ : ℝ, 0 < J ∧ 0 < C ∧ 0 < P ∧ 2 ≤ X₁ ∧
      ∀ X ≥ X₁, ∀ q d : ℕ+, SelmerEstimatePrimePair target q d →
        max P (2 * X ^ (401 : ℕ) + 1) < (q : ℕ) →
        max P (2 * X ^ (401 : ℕ) + 1) < (d : ℕ) →
        Real.log ((q : ℕ) * (d : ℕ) : ℝ) ≤ X ^ (ε / (4 * J)) →
        ∃ Y : ℝ, 2 ≤ Y ∧ X ^ (1 / J) ≤ Y ∧ Y ≤ X ^ (1 / 2 : ℝ) ∧
          ∀ x ∈ Set.Icc Y (Y ^ (2 : ℕ)),
            let F := selmerHostField target (e x) q d
            let L := numberFieldSelmerSignLengths true F
            TwoSelmerLengthBound (numberFieldSelmerLengths F) (t x) (Real.exp (x ^ (4 * ε / 5))) ∧
            (∀ ℓ ∈ bad, ∀ i ∈ Finset.Ico 1 (t x), L ℓ i ≠ ⊤) ∧
            (∑ ℓ ∈ bad, selmerWeightedLength L (t x) ℓ) ≤ C * Real.exp (x ^ (4 * ε / 5)) := by
  classical
  obtain ⟨R₂, K₂, hK₂, hTwo⟩ := selmerTwo_exceptionalScaleControl target hprim
  choose R j K hK hOdd using fun i : bad =>
    selmerOddLayer_exceptionalScaleControl target hprim i
      (hbad i i.property).1 (hbad i i.property).2
  let depth (ℓ : ℕ) := if h : ℓ ∈ bad then j ⟨ℓ, h⟩ else 0
  obtain ⟨A, P, hP, hTransfer⟩ :=
    selmerPlus_badPrimes_of_layerBounds target hprim bad hbad depth
  let Rtot := R₂ + ∑ i : bad, R i
  let Ktot := K₂ + ∑ i : bad, K i
  have hKnonneg (i : bad) : 0 ≤ K i := zero_le_one.trans (hK i)
  have hK₂tot : K₂ ≤ Ktot := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hKnonneg i)
  have hKtot : 1 ≤ Ktot := hK₂.trans hK₂tot
  have hKle (i : bad) : K i ≤ Ktot :=
    (Finset.single_le_sum (fun i _ => hKnonneg i) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one.trans hK₂))
  let η := ε / (2 * Ktot)
  have hη : 0 < η := div_pos hε (by linarith)
  have hη₄₀₁ : η ≤ 401 := (div_le_iff₀ (by linarith : 0 < 2 * Ktot)).mpr (by linarith)
  have hηle {K' : ℝ} (hK' : 1 ≤ K') (hle : K' ≤ Ktot) : η ≤ ε / (2 * K') :=
    div_le_div_of_nonneg_left hε.le (by linarith) (by linarith)
  let J := finiteScaleWindowExponent Rtot (401 / η)
  have hJ : 0 < J := finiteScaleWindowExponent_pos _ (by positivity)
  obtain ⟨X₂, H₂⟩ := hTwo ε J hε hsmall hJ e t hadm
  choose Xodd Hodd using fun i : bad => hOdd i ε J hε hsmall hJ e t hadm
  obtain ⟨x₀, hpoly⟩ := eventually_atTop.mp (eventually_selmerSmallPrimePolynomial_le target A hε)
  let U := max 2 x₀
  let X₁ := max (U ^ J) (max 2 (max X₂ (∑ i : bad, |Xodd i|)))
  have hU : 2 ≤ U := le_max_left _ _
  let C : ℝ := (A : ℝ) + 1
  have hX₁ : 2 ≤ X₁ := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨J, C, P, X₁, hJ, by dsimp [C]; positivity, hP, hX₁, ?_⟩
  intro X hX q d hp hq hd hqd
  have hXlarge := hX₁.trans hX
  have hX₀ : 0 ≤ X := by linarith
  have hX₂ : X₂ ≤ X :=
    ((le_max_left _ _).trans (le_max_right 2 _)).trans ((le_max_right (U ^ J) _).trans hX)
  have hXodd (i : bad) : Xodd i ≤ X := calc
    _ ≤ |Xodd i| := le_abs_self _
    _ ≤ ∑ k : bad, |Xodd k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (Xodd k)) (Finset.mem_univ i)
    _ ≤ X₁ := (le_max_right _ _).trans ((le_max_right 2 _).trans (le_max_right _ _))
    _ ≤ X := hX
  have hUwindow : U ≤ X ^ (1 / J) := calc
    _ = (U ^ J) ^ (1 / J) := by
      rw [one_div, Real.rpow_rpow_inv (by linarith : 0 ≤ U) hJ.ne']
    _ ≤ _ := Real.rpow_le_rpow (by positivity) ((le_max_left _ _).trans hX) (by positivity)
  obtain ⟨exc₂, hcard₂, hLocalTwo⟩ := H₂ X hX₂ q d hp hqd
  choose exc hcardOdd hLocalOdd using fun i : bad => Hodd i X (hXodd i)
  let total := exc₂ ∪ Finset.univ.biUnion exc
  have hcard : total.card ≤ Rtot :=
    (Finset.card_union_le _ _).trans (add_le_add hcard₂
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => hcardOdd i)))
  obtain ⟨Y, hY₀, hYlo, hYhi, hGood⟩ :=
    exists_quadraticWindow_goodFiniteScale Rtot (X := X) total hη hη₄₀₁ (by linarith) hcard
  have hY₂ := hU.trans (hUwindow.trans hYlo)
  refine ⟨Y, hY₂, hYlo, ?_, ?_⟩
  · rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt hY₀.le hX₀).mpr hYhi
  intro x hx
  have hx₂ := hY₂.trans hx.1
  have hxrange : x ∈ Set.Icc (X ^ (1 / J)) X := ⟨hYlo.trans hx.1, hx.2.trans hYhi⟩
  have hGoodSubset (S : Finset ℕ) (hS : S ⊆ total) {η' : ℝ} (hη' : η ≤ η') :
      GoodFiniteScale η' 401 S x := by
    intro a ha hax
    exact (hGood x hx a (hS ha) hax).trans (Real.rpow_le_rpow_of_exponent_le (by linarith) hη')
  have hTwoAt := hLocalTwo x hxrange hx₂
    (hGoodSubset exc₂ Finset.subset_union_left (hηle hK₂ hK₂tot))
  let B := Real.exp (x ^ (4 * ε / 5))
  have hLayer : ∀ ℓ ∈ bad, SelmerOddLayerBound target ℓ (depth ℓ) (t x) B := by
    intro ℓ hℓ
    let i : bad := ⟨ℓ, hℓ⟩
    have hSubset : exc i ⊆ total :=
      (Finset.subset_biUnion_of_mem exc (Finset.mem_univ i)).trans Finset.subset_union_right
    have hi := hLocalOdd i x hxrange hx₂ (hGoodSubset (exc i) hSubset (hηle (hK i) (hKle i)))
    simpa only [depth, dite_eq_left hℓ] using hi
  obtain ⟨he, hex, ht, htx⟩ := hadm x hx₂
  have htX := htx.trans (pow_le_pow_left₀ (by linarith) hxrange.2 _)
  have hcut : max P (2 * (t x : ℝ) + 1) ≤ max P (2 * X ^ (401 : ℕ) + 1) :=
    max_le_max le_rfl (by linarith)
  obtain ⟨hfin, hsum⟩ := hTransfer (e x) (t x) q d he ht hp (hcut.trans_lt hq) (hcut.trans_lt hd)
    B (Real.exp_nonneg _) hLayer
  have hqd' := hqd.trans (scale_quarter_rpow_le hX₀ hε hxrange.1)
  have hx₀ : x₀ ≤ x := (le_max_right _ _).trans (hUwindow.trans hxrange.1)
  have hpolyAt := hpoly x hx₀ (e x) (t x) q d hex (by omega) htx hqd'
  exact ⟨hTwoAt, hfin, hsum.trans (by dsimp [B, C]; linarith only [hpolyAt])⟩

end Riemann
