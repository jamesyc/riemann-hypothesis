module

public import Utilities.FrobeniusGeneration
import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open NumberField
open scoped NumberField Pointwise Topology

namespace Utilities

set_option maxHeartbeats 600000 in
/-- A specified arithmetic Frobenius on a finite layer lifts to
arithmetic Frobenius at any prime above the given prime. -/
theorem numberField_isArithFrobAt_lift
    {L : Type} [Field L] [Algebra ℚ L] [IsGalois ℚ L]
    (E : FiniteGaloisIntermediateField ℚ L) {p : ℕ} [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    letI : Algebra ℚ E := E.toIntermediateField.algebra'
    ∀ {τ : Gal(E/ℚ)}, IsArithFrobAt ℤ τ (P.under (𝓞 E)) →
      ∃ φ : Gal(L/ℚ), φ.restrictNormal E = τ ∧ IsArithFrobAt ℤ φ P := by
  let _ : Algebra ℚ E := E.toIntermediateField.algebra'
  intro τ hτ
  let Q := P.under (𝓞 E)
  let _ : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨(Ideal.over_def P (Ideal.span {(p : ℤ)})).trans (Ideal.under_under P).symm⟩
  obtain ⟨φ, hφ⟩ := numberField_exists_isArithFrobAt_of_isGalois (p := p) P
  have hres : IsArithFrobAt ℤ (φ.restrictNormal E) Q :=
    numberField_isArithFrobAt_restrictNormal_tower E (p := p) Q P hφ
  have hI : τ * (φ.restrictNormal E)⁻¹ ∈ Q.inertia Gal(E/ℚ) := hτ.mul_inv_mem_inertia hres
  have hmap : (P.inertia Gal(L/ℚ)).map (AlgEquiv.restrictNormalHom E) = Q.inertia Gal(E/ℚ) :=
    numberField_inertia_map_restrictNormal_of_isGalois E P
  obtain ⟨u, hu, hur⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hI)
  refine ⟨u * φ, ?_, (numberField_isArithFrobAt_iff (p := p) P _).mpr fun x => ?_⟩
  · change (AlgEquiv.restrictNormalHom E) (u * φ) = τ
    rw [map_mul, hur]
    exact inv_mul_cancel_right _ _
  · have h₁ := (Ideal.mem_inertia.mp hu) (φ • x)
    have h₂ := (numberField_isArithFrobAt_iff (p := p) P φ).mp hφ x
    rw [mul_smul, ← sub_add_sub_cancel (u • (φ • x)) (φ • x) (x ^ p)]
    exact P.add_mem h₁ h₂

/-- An arithmetic Frobenius at a finite prime lifts to one at a prime
of the algebraic Galois extension above it. -/
theorem exists_isArithFrobAt_lift_from_finite_prime
    {L : Type} [Field L] [Algebra ℚ L] [IsGalois ℚ L]
    (E : FiniteGaloisIntermediateField ℚ L) {p : ℕ} [Fact p.Prime]
    (Q : Ideal (𝓞 E)) [Q.IsPrime] (hQ : (p : 𝓞 E) ∈ Q) :
    letI : Algebra ℚ E := E.toIntermediateField.algebra'
    ∀ {τ : Gal(E/ℚ)}, IsArithFrobAt ℤ τ Q →
      ∃ (P : Ideal (𝓞 L)) (φ : Gal(L/ℚ)), P.IsPrime ∧ (p : 𝓞 L) ∈ P ∧
        φ.restrictNormal E = τ ∧ IsArithFrobAt ℤ φ P := by
  let _ : Algebra ℚ E := E.toIntermediateField.algebra'
  intro τ hτ
  let B := Ideal.span {(p : ℤ)}
  let _ : B.IsMaximal := rationalPrime_isMaximal p
  let _ : Q.LiesOver B := liesOver_rationalPrime_of_mem Q p hQ
  let _ : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q B
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral Q (S := 𝓞 L)
  let _ : P.IsPrime := hP.isPrime
  let _ : P.LiesOver Q := hPQ
  let _ : P.LiesOver B := Ideal.LiesOver.trans P Q B
  obtain ⟨φ, hφr, hφ⟩ := numberField_isArithFrobAt_lift E (p := p) P (τ := τ)
    ((Ideal.over_def P Q) ▸ hτ)
  have hPmem : (p : 𝓞 L) ∈ P :=
    (natCast_mem_iff_dvd_of_liesOver_rationalPrime P p p).mpr dvd_rfl
  exact ⟨P, φ, hP.isPrime, hPmem, hφr, hφ⟩

/-- A Krull-open set containing an automorphism contains its whole
restriction fiber at some finite Galois layer. -/
theorem exists_finiteGalois_restriction_fiber_subset_open
    {L : Type} [Field L] [Algebra ℚ L] [IsGalois ℚ L]
    (U : Set Gal(L/ℚ)) (hU : IsOpen U) {s : Gal(L/ℚ)} (hs : s ∈ U) :
    ∃ E : FiniteGaloisIntermediateField ℚ L,
      letI : Algebra ℚ E := E.toIntermediateField.algebra'
      ∀ t : Gal(L/ℚ), t.restrictNormal E = s.restrictNormal E → t ∈ U := by
  let V := (fun t : Gal(L/ℚ) => s * t) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : Gal(L/ℚ)) ∈ V := by simpa [V] using hs
  obtain ⟨A, hA, hN, hAV⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ L V).mp (hV.mem_nhds h1)
  let _ : Algebra ℚ A := A.algebra'
  let _ : FiniteDimensional ℚ A := hA
  let _ : IsGalois ℚ A := isGalois_iff.mpr ⟨inferInstance, hN⟩
  let E : FiniteGaloisIntermediateField ℚ L := ⟨A⟩
  refine ⟨E, fun t ht => ?_⟩
  have hker : s⁻¹ * t ∈ A.fixingSubgroup := by
    rw [← A.restrictNormalHom_ker]
    change (AlgEquiv.restrictNormalHom A) (s⁻¹ * t) = 1
    rw [map_mul, map_inv, show (AlgEquiv.restrictNormalHom A) t =
      (AlgEquiv.restrictNormalHom A) s from ht, inv_mul_cancel]
  have hmem := hAV hker
  change s * (s⁻¹ * t) ∈ U at hmem
  rwa [mul_inv_cancel_left] at hmem

/-- The finite rational Frobenius realization statement used for selecting
auxiliary primes. The nonzero integer lists the excluded rational primes. -/
def HasFiniteRationalFrobeniusRealization : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] [NumberField K] [IsGalois ℚ K]
    (τ : Gal(K/ℚ)) (m : ℕ), m ≠ 0 →
    ∃ (p : ℕ) (Q : Ideal (𝓞 K)), p.Prime ∧ ¬ p ∣ m ∧ Q.IsPrime ∧
      (p : 𝓞 K) ∈ Q ∧ IsArithFrobAt ℤ τ Q

/-- Any finite rational Frobenius realization theorem supplies auxiliary
Frobenius elements in nonempty Krull-open sets with finitely many primes excluded. -/
theorem exists_rational_isArithFrobAt_in_open
    (hreal : HasFiniteRationalFrobeniusRealization)
    {L : Type} [Field L] [Algebra ℚ L] [IsGalois ℚ L]
    (U : Set Gal(L/ℚ)) (hU : IsOpen U) (hne : U.Nonempty) (m : ℕ) (hm : m ≠ 0) :
    ∃ (p : ℕ) (P : Ideal (𝓞 L)) (φ : Gal(L/ℚ)), p.Prime ∧ ¬ p ∣ m ∧ P.IsPrime ∧
      (p : 𝓞 L) ∈ P ∧ IsArithFrobAt ℤ φ P ∧ φ ∈ U := by
  obtain ⟨s, hs⟩ := hne
  obtain ⟨E, hE⟩ := exists_finiteGalois_restriction_fiber_subset_open U hU hs
  let A := E.toIntermediateField
  let _ : Algebra ℚ A := A.algebra'
  let _ : FiniteDimensional ℚ A := E.finiteDimensional
  let _ : NumberField A := NumberField.of_module_finite ℚ A
  let _ : IsGalois ℚ A := E.isGalois
  obtain ⟨p, Q, hp, hpm, hprime, hmem, hτ⟩ := hreal A (s.restrictNormal A) m hm
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Q.IsPrime := hprime
  obtain ⟨P, φ, hP, hPmem, hφr, hφ⟩ :=
    exists_isArithFrobAt_lift_from_finite_prime E (p := p) Q hmem hτ
  exact ⟨p, P, φ, hp, hpm, hP, hPmem, hφ, hE φ hφr⟩

end Utilities
