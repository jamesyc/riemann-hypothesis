module

public import Riemann.HostTail
public import Riemann.HostAveraging
public import Utilities.QuadraticConductor

@[expose] public section

open Utilities

namespace Riemann

theorem selmerHostInducingCharacter_modulus_dvd_of_quadratic
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H]
    (coord : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)) (ψ : ExcessCharacter H)
    (hquadratic : (selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
      coord ψ).character ^ (2 : ℕ) = 1) :
    ((selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
      coord ψ).modulus : ℕ) ∣ 8 * (target.modulus : ℕ) * (q : ℕ) * (d : ℕ) := by
  let M := (target.modulus : ℕ)
  let F := 8 * M * (q : ℕ) * (d : ℕ)
  let N := selmerHostModulus target e q d
  let _ : NeZero N := ⟨(selmerHostModulus_pos target e q d).ne'⟩
  let _ : NeZero (F * 2 ^ (e + 2)) := ⟨(show 0 < F * 2 ^ (e + 2) by
    dsimp only [F, M]
    positivity).ne'⟩
  let χ := selmerHostDirichlet (target := target) (e := e) (q := q) (d := d) coord ψ
  have hquad : χ ^ (2 : ℕ) = 1 := by
    rw [← χ.changeLevel_primitiveCharacter, ← map_pow]
    rw [show χ.primitiveCharacter ^ (2 : ℕ) = 1 from hquadratic, map_one]
  have hF₈ : 8 ∣ F :=
    ((dvd_mul_right 8 M).trans (dvd_mul_right _ (q : ℕ))).trans (dvd_mul_right _ (d : ℕ))
  have hM : M ∣ F :=
    ((dvd_mul_left M 8).trans (dvd_mul_right _ (q : ℕ))).trans (dvd_mul_right _ (d : ℕ))
  have hq : (q : ℕ) ∣ F := (dvd_mul_left (q : ℕ) (8 * M)).trans (dvd_mul_right _ (d : ℕ))
  have hd : (d : ℕ) ∣ F := dvd_mul_left _ _
  have hFF : F ∣ F * 2 ^ (e + 2) := dvd_mul_right _ _
  have hN : N ∣ F * 2 ^ (e + 2) :=
    Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd (dvd_mul_left _ _) (hM.trans hFF)) (hq.trans hFF))
      (hd.trans hFF)
  exact quadraticCharacter_conductor_dvd_of_dyadic_extension hF₈ hN χ hquad

theorem selmerHostInducingCharacter_modulus_dvd_of_real
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+}
    {H : Type} [AddCommGroup H]
    (coord : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)) (ψ : ExcessCharacter H)
    (hreal :
      let χ := selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) coord ψ
      ∀ a : ZMod (χ.modulus : ℕ), (χ.character a).im = 0) :
    ((selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
      coord ψ).modulus : ℕ) ∣ 8 * (target.modulus : ℕ) * (q : ℕ) * (d : ℕ) := by
  let χ := selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) coord ψ
  let _ : NeZero (χ.modulus : ℕ) := ⟨χ.modulus.pos.ne'⟩
  exact selmerHostInducingCharacter_modulus_dvd_of_quadratic coord ψ
    (dirichletCharacter_sq_eq_one_of_real χ.character hreal)

/-- One cutoff below one works uniformly for all nontrivial real host
characters without a conductor factor at either moving auxiliary prime. -/
theorem exists_noRealZero_nearOne_of_baseCharacter
    (target : BundledDirichletCharacter) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 400 ∧
      ∀ {e : ℕ} {q d : ℕ+} {H : Type} [AddCommGroup H]
        (coord : Multiplicative (ExcessGroup H) ≃*
          (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)) (ψ : ExcessCharacter H),
        ψ ≠ 0 → (q : ℕ).Prime → (d : ℕ).Prime →
        let χ := selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d)
          coord ψ
        (∀ a : ZMod (χ.modulus : ℕ), (χ.character a).im = 0) →
        ¬ (q : ℕ) ∣ (χ.modulus : ℕ) → ¬ (d : ℕ) ∣ (χ.modulus : ℕ) →
        ∀ β ∈ Set.Ioo (1 - c) 1, DirichletCharacter.LFunction χ.character (β : ℂ) ≠ 0 := by
  let M : ℕ+ := ⟨8 * (target.modulus : ℕ), by positivity⟩
  obtain ⟨c, hc, hc', hnear⟩ := exists_noRealZero_nearOne_of_modulus_dvd M
  refine ⟨c, hc, hc', ?_⟩
  intro e q d H inst coord ψ hψ hqPrime hdPrime χ hreal hq hd
  have hχ := selmerHostInducingCharacter_modulus_dvd_of_real coord ψ hreal
  have hqC := (hqPrime.coprime_iff_not_dvd.mpr hq).symm
  have hdC := (hdPrime.coprime_iff_not_dvd.mpr hd).symm
  have hdiv : (χ.modulus : ℕ) ∣ (M : ℕ) :=
    hqC.dvd_of_dvd_mul_right (hdC.dvd_of_dvd_mul_right hχ)
  exact hnear χ hdiv (selmerHostInducingCharacter_ne_one coord hψ)

/-- The nontrivial quadratic character is the only nontrivial quadratic
choice at either auxiliary prime. -/
theorem quadraticCharacter_at_auxiliaryPrime_eq_sign_pow
    {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (χ : DirichletCharacter ℂ p) (hχ : χ ^ (2 : ℕ) = 1) :
    ∃ b : Bool, χ = selmerQuadraticCharacter hp ^ b.toNat := by
  let f : (ZMod p)ˣ →* ℂ := (Units.coeHom ℂ).comp χ.toUnitHom
  have hker : selmerSquareUnits p ≤ f.ker := by
    intro u hu
    obtain ⟨v, _, rfl⟩ := Subgroup.mem_map.mp hu
    change (χ.toUnitHom (v ^ (2 : ℕ)) : ℂ) = 1
    rw [MulChar.coe_toUnitHom, Units.val_pow_eq_pow_val, map_pow, ← MulChar.pow_apply_coe,
      hχ, MulChar.one_apply_coe]
  let g := QuotientGroup.lift (selmerSquareUnits p) f hker
  let ξ : AddChar (ZMod 2) ℂ := AddChar.toMonoidHomEquiv.symm
    (g.comp (selmerSquareClassSign hp).symm.toMonoidHom)
  obtain ⟨b, hb⟩ := zmodTwo_character_eq_sign_pow ξ
  refine ⟨b, ?_⟩
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply_coe, selmerQuadraticCharacter_apply_unit]
  let z := selmerSquareClassSign hp (QuotientGroup.mk u)
  have h := hb z.toAdd
  change g ((selmerSquareClassSign hp).symm z) = zmodTwoSign z.toAdd ^ b.toNat at h
  rw [show (selmerSquareClassSign hp).symm z = QuotientGroup.mk u from
    (selmerSquareClassSign hp).symm_apply_apply _] at h
  change (χ.toUnitHom u : ℂ) = _ at h
  simpa only [MulChar.coe_toUnitHom] using h

/-- Any real inducing host character is a primitive fixed-level base
character times one of the four choices of the two auxiliary twists. -/
theorem selmerHostInducingCharacter_eq_quadraticTwists_of_real
    {target : BundledDirichletCharacter} {e : ℕ} {q d : ℕ+} {H : Type} [AddCommGroup H]
    [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime]
    (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3)
    (hq : (8 * (target.modulus : ℕ)).Coprime q)
    (hd : (8 * (target.modulus : ℕ) * (q : ℕ)).Coprime d)
    (coord : Multiplicative (ExcessGroup H) ≃*
      (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)) (ψ : ExcessCharacter H)
    (hreal :
      let χ := selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) coord ψ
      ∀ a : ZMod (χ.modulus : ℕ), (χ.character a).im = 0) :
    let χ := selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) coord ψ
    ∃ ξ : BundledDirichletCharacter, ∃ qSign dSign : Bool,
      ξ.character.IsPrimitive ∧ (ξ.modulus : ℕ) ∣ 8 * (target.modulus : ℕ) ∧
      χ = selmerTwistedCharacter ξ q d hq₄ hd₄ 1 qSign dSign := by
  dsimp only
  let χ := selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) coord ψ
  let M := 8 * (target.modulus : ℕ)
  let F := M * (q : ℕ) * (d : ℕ)
  let _ : NeZero F := ⟨(show 0 < F by dsimp only [F, M]; positivity).ne'⟩
  let _ : NeZero M := ⟨(show 0 < M by dsimp only [M]; positivity).ne'⟩
  let _ : NeZero (χ.modulus : ℕ) := ⟨χ.modulus.pos.ne'⟩
  have hdiv : (χ.modulus : ℕ) ∣ F := selmerHostInducingCharacter_modulus_dvd_of_real coord ψ hreal
  let χF := DirichletCharacter.changeLevel hdiv χ.character
  have hχF : χF ^ (2 : ℕ) = 1 := by
    change (DirichletCharacter.changeLevel hdiv χ.character) ^ (2 : ℕ) = 1
    rw [← map_pow, dirichletCharacter_sq_eq_one_of_real χ.character hreal, map_one]
  obtain ⟨χMq, χd, hχMq, hχd, hdecompD⟩ := exists_quadraticCharacter_mul_of_coprime hd χF hχF
  obtain ⟨χM, χq, hχM, hχq, hdecompQ⟩ := exists_quadraticCharacter_mul_of_coprime hq χMq hχMq
  obtain ⟨qSign, hqSign⟩ := quadraticCharacter_at_auxiliaryPrime_eq_sign_pow hq₄ χq hχq
  obtain ⟨dSign, hdSign⟩ := quadraticCharacter_at_auxiliaryPrime_eq_sign_pow hd₄ χd hχd
  let ξ := BundledDirichletCharacter.primitiveOf χM
  have hξ : (ξ.modulus : ℕ) ∣ M := χM.conductor_dvd_level
  refine ⟨ξ, qSign, dSign, BundledDirichletCharacter.primitiveOf_isPrimitive χM, hξ, ?_⟩
  have hprimF : BundledDirichletCharacter.primitiveOf χF = χ := by
    rw [BundledDirichletCharacter.primitiveOf_changeLevel]
    exact χ.primitiveOf_eq_self (selmerHostInducingCharacter_isPrimitive coord ψ)
  let G := ((ξ.modulus : ℕ).lcm q).lcm d
  let _ : NeZero G := ⟨(Nat.lcm_pos (Nat.lcm_pos ξ.modulus.pos q.pos) d.pos).ne'⟩
  have hMF : M ∣ F := dvd_trans (dvd_mul_right M (q : ℕ)) (dvd_mul_right _ (d : ℕ))
  have hqF : (q : ℕ) ∣ F := dvd_trans (dvd_mul_left (q : ℕ) M) (dvd_mul_right _ (d : ℕ))
  have hdF : (d : ℕ) ∣ F := dvd_mul_left _ _
  have hGF : G ∣ F := Nat.lcm_dvd (Nat.lcm_dvd (hξ.trans hMF) hqF) hdF
  change χ = selmerTwistedCharacter ξ q d hq₄ hd₄ 1 qSign dSign
  rw [← hprimF]
  unfold selmerTwistedCharacter
  rw [← BundledDirichletCharacter.primitiveOf_changeLevel hGF]
  apply congrArg (fun c : DirichletCharacter ℂ F => BundledDirichletCharacter.primitiveOf c)
  rw [hdecompD, hdecompQ, hqSign, hdSign, ← χM.changeLevel_primitiveCharacter]
  simp only [pow_one, map_mul, ← DirichletCharacter.changeLevel_trans]
  rfl

/-- The fixed testing level remains coprime to the window primes. -/
theorem SelmerWindowPair.coprime_fixedRealBaseModulus
    {ε base : ℝ} {q d : ℕ+} (pair : SelmerWindowPair ε base q d)
    (target : BundledDirichletCharacter)
    (hsize : ((target.modulus : ℕ) : ℝ) ≤ base ^ (ε / 5)) :
    (8 * (target.modulus : ℕ)).Coprime q ∧
      (8 * (target.modulus : ℕ) * (q : ℕ)).Coprime d := by
  obtain ⟨hq, hd⟩ := pair.coprime_host_base_modulus target 0 hsize
  have hbase : (target.modulus : ℕ) ∣ selmerBaseModulus target 0 := Nat.dvd_lcm_right _ _
  have hqM : (target.modulus : ℕ).Coprime q := hq.of_dvd_left hbase
  have hdMq : ((target.modulus : ℕ) * (q : ℕ)).Coprime d :=
    hd.of_dvd_left (Nat.mul_dvd_mul_right hbase _)
  have hq₂ : (q : ℕ) ≠ 2 := by have := pair.q_residue; omega
  have hd₂ : (d : ℕ) ≠ 2 := by have := pair.d_residue; omega
  have hq₈ : (8 : ℕ).Coprime q :=
    (Nat.coprime_two_left.mpr (pair.q_prime.odd_of_ne_two hq₂)).pow_left 3
  have hd₈ : (8 : ℕ).Coprime d :=
    (Nat.coprime_two_left.mpr (pair.d_prime.odd_of_ne_two hd₂)).pow_left 3
  exact ⟨hq₈.mul_left hqM, by simpa only [mul_assoc] using hd₈.mul_left hdMq⟩

/-- The real-zero exclusions for the two auxiliary-prime tests, together
with the fixed-level interval, exclude real zeros uniformly for every real
nontrivial inducing character at the moving host. -/
theorem exists_noRealZero_nearOne_of_goodTwists (target : BundledDirichletCharacter) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 400 ∧
      ∀ (q d : ℕ+) [Fact (q : ℕ).Prime] [Fact (d : ℕ).Prime]
        (hq₄ : (q : ℕ) % 4 = 3) (hd₄ : (d : ℕ) % 4 = 3),
        (8 * (target.modulus : ℕ)).Coprime q →
        (8 * (target.modulus : ℕ) * (q : ℕ)).Coprime d →
        (∀ ξ : BundledDirichletCharacter, ξ.character.IsPrimitive →
          (ξ.modulus : ℕ) ∣ 8 * (target.modulus : ℕ) →
          ∀ β ∈ Set.Ioo (1 - (1 / 400 : ℝ)) 1,
            DirichletCharacter.LFunction
              (selmerFirstTwistedCharacter ξ q hq₄ 1 true).character (β : ℂ) ≠ 0) →
        (∀ ξ : BundledDirichletCharacter, ξ.character.IsPrimitive →
          (ξ.modulus : ℕ) ∣ 8 * (target.modulus : ℕ) →
          ∀ (qSign : Bool) (β : ℝ), β ∈ Set.Ioo (1 - (1 / 400 : ℝ)) 1 →
            DirichletCharacter.LFunction
              (selmerTwistedCharacter ξ q d hq₄ hd₄ 1 qSign true).character (β : ℂ) ≠ 0) →
        ∀ {e : ℕ} {H : Type} [AddCommGroup H]
          (coord : Multiplicative (ExcessGroup H) ≃*
            (ExcessHost target e q d ≃ₐ[ℚ] ExcessHost target e q d)) (ψ : ExcessCharacter H),
          ψ ≠ 0 →
          let χ := selmerHostInducingCharacter (target := target) (e := e) (q := q) (d := d) coord ψ
          (∀ a : ZMod (χ.modulus : ℕ), (χ.character a).im = 0) →
          ∀ β ∈ Set.Ioo (1 - c) 1, DirichletCharacter.LFunction χ.character (β : ℂ) ≠ 0 := by
  let M : ℕ+ := ⟨8 * (target.modulus : ℕ), by positivity⟩
  obtain ⟨c, hc, hc', hnear⟩ := exists_noRealZero_nearOne_of_modulus_dvd M
  refine ⟨c, hc, hc', ?_⟩
  intro q d instq instd hq₄ hd₄ hq hd hQ hD e H instH coord ψ hψ χ hreal β hβ
  have hβ' : β ∈ Set.Ioo (1 - (1 / 400 : ℝ)) 1 :=
    ⟨(sub_le_sub_left hc' 1).trans_lt hβ.1, hβ.2⟩
  obtain ⟨ξ, qSign, dSign, hξp, hξM, hχ⟩ :=
    selmerHostInducingCharacter_eq_quadraticTwists_of_real hq₄ hd₄ hq hd coord ψ hreal
  change χ = selmerTwistedCharacter ξ q d hq₄ hd₄ 1 qSign dSign at hχ
  cases dSign
  · rw [selmerTwistedCharacter_no_second_twist] at hχ
    cases qSign
    · rw [selmerFirstTwistedCharacter_no_twist] at hχ
      have hfixed : selmerFixedCharacter ξ 1 = ξ := by
        let _ : NeZero (ξ.modulus : ℕ) := ⟨ξ.modulus.pos.ne'⟩
        unfold selmerFixedCharacter
        rw [pow_one]
        exact ξ.primitiveOf_eq_self hξp
      have heq : χ = ξ := hχ.trans hfixed
      have hξne : ξ.character ≠ 1 := by
        rw [← heq]
        exact selmerHostInducingCharacter_ne_one coord hψ
      rw [heq]
      exact hnear ξ hξM hξne β hβ
    · rw [hχ]
      exact hQ ξ hξp hξM β hβ'
  · rw [hχ]
    exact hD ξ hξp hξM qSign β hβ'

end Riemann
