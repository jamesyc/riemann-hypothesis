module

public import Utilities.CyclotomicFrobenius
public import Utilities.RationalPrime
public import Utilities.InertiaRestriction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

open NumberField
open scoped NumberField Pointwise Topology

namespace Utilities

private theorem exists_pow_eq_of_apply_eq_pow_card (k l : Type*) [Field k] [Fintype k]
    [Field l] [Finite l] [Algebra k l] (φ : Gal(l/k))
    (hφ : ∀ x : l, φ x = x ^ Fintype.card k) (g : Gal(l/k)) :
    ∃ n : ℕ, φ ^ n = g := by
  have he : φ = FiniteField.frobeniusAlgEquivOfAlgebraic k l := AlgEquiv.ext hφ
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l).surjective g
  exact ⟨n.val, he.symm ▸ hn⟩

set_option maxHeartbeats 700000 in
set_option synthInstance.maxHeartbeats 70000 in
/-- In a finite number field, an arithmetic Frobenius and inertia
generate the whole decomposition group. -/
theorem numberField_inertia_sup_zpowers_eq_stabilizer {K : Type} [Field K] [Algebra ℚ K] [NumberField K]
    {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] {φ : Gal(K/ℚ)} (hφ : IsArithFrobAt ℤ φ P) :
    P.inertia Gal(K/ℚ) ⊔ Subgroup.zpowers φ = MulAction.stabilizer Gal(K/ℚ) P := by
  let B := Ideal.span {(p : ℤ)}
  let _ : B.IsMaximal := rationalPrime_isMaximal p
  let _ : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P B
  let k := ℤ ⧸ B
  let l := 𝓞 K ⧸ P
  let _ : Field k := Ideal.Quotient.field B
  let _ : Field l := Ideal.Quotient.field P
  have hp : p.Prime := Fact.out
  have hB : B ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  let _ : Finite l := Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hB P)
  have hk' : Nat.card k = p := by
    change Nat.card (ℤ ⧸ (Ideal.span {(p : ℤ)} : Ideal ℤ)) = p
    rw [Int.card_ideal_quot]
  let _ : Finite k := Nat.finite_of_card_ne_zero (by rw [hk']; exact hp.ne_zero)
  let _ := Fintype.ofFinite k
  let D := MulAction.stabilizer Gal(K/ℚ) P
  let f := Ideal.Quotient.stabilizerHom P B Gal(K/ℚ)
  let φD : D := ⟨φ, hφ.mem_stabilizer⟩
  have hk : Fintype.card k = p := Nat.card_eq_fintype_card.symm.trans hk'
  have hφf (z : l) : f φD z = z ^ Fintype.card k := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk P (φ • x) = (Ideal.Quotient.mk P x) ^ Fintype.card k
    rw [hk, ← map_pow]
    exact Ideal.Quotient.eq.mpr ((numberField_isArithFrobAt_iff (p := p) P φ).mp hφ x)
  refine le_antisymm (sup_le P.inertia_le_stabilizer (Subgroup.zpowers_le.mpr hφ.mem_stabilizer)) ?_
  intro g hg
  let gD : D := ⟨g, hg⟩
  obtain ⟨n, hn⟩ := exists_pow_eq_of_apply_eq_pow_card k l (f φD) hφf (f gD)
  rw [← map_pow] at hn
  have hI : gD * (φD ^ n)⁻¹ ∈ P.inertia D := by
    rw [← Ideal.Quotient.ker_stabilizerHom P B Gal(K/ℚ)]
    change f (gD * (φD ^ n)⁻¹) = 1
    rw [map_mul, map_inv, hn, mul_inv_cancel]
  have hgI : g * (φ ^ n)⁻¹ ∈ P.inertia Gal(K/ℚ) := P.coe_mem_inertia.mpr hI
  have hz : φ ^ n ∈ Subgroup.zpowers φ :=
    (Subgroup.zpowers φ).pow_mem (Subgroup.mem_zpowers φ) _
  let S := P.inertia Gal(K/ℚ) ⊔ Subgroup.zpowers φ
  have h₁ : g * (φ ^ n)⁻¹ ∈ S := (le_sup_left : P.inertia Gal(K/ℚ) ≤ S) hgI
  have h₂ : φ ^ n ∈ S := (le_sup_right : Subgroup.zpowers φ ≤ S) hz
  simpa only [inv_mul_cancel_right] using S.mul_mem h₁ h₂

/-- An arithmetic Frobenius lift exists in an algebraic Galois extension.
Finite lifts satisfy every finite family of the defining congruences. -/
theorem numberField_exists_isArithFrobAt_of_isGalois {L : Type} [Field L] [Algebra ℚ L]
    [IsGalois ℚ L] {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : ∃ φ : Gal(L/ℚ), IsArithFrobAt ℤ φ P := by
  classical
  let D (s : Finset (𝓞 L)) : Set Gal(L/ℚ) :=
    ⋂ x ∈ (s : Set (𝓞 L)), {σ | σ • x - x ^ p ∈ P}
  have hclosed (s : Finset (𝓞 L)) : IsClosed (D s) := by
    refine isClosed_biInter fun x _ => ?_
    apply isOpen_compl_iff.mp
    exact isLocallyConstant_galois_smul_integer (K := ℚ) x {y | y - x ^ p ∉ P}
  have hdir : Directed (· ⊇ ·) D := by
    intro s t
    exact ⟨s ∪ t, Set.biInter_subset_biInter_left Finset.subset_union_left,
      Set.biInter_subset_biInter_left Finset.subset_union_right⟩
  have hnonempty (s : Finset (𝓞 L)) : (D s).Nonempty := by
    let t : Set L := (fun x : 𝓞 L => (x : L)) '' (s : Set (𝓞 L))
    let _ : Finite t := ((s.finite_toSet).image _).to_subtype
    let E := FiniteGaloisIntermediateField.adjoin ℚ t
    let A := E.toIntermediateField
    let _ : Algebra ℚ A := A.algebra'
    let _ : FiniteDimensional ℚ A := E.finiteDimensional
    let _ : IsGalois ℚ A := E.isGalois
    let _ : NumberField A := NumberField.of_module_finite ℚ A
    let Q := P.under (𝓞 A)
    let _ : Q.IsPrime := inferInstanceAs (P.under (𝓞 A)).IsPrime
    let _ : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
      ⟨(Ideal.over_def P (Ideal.span {(p : ℤ)})).trans (Ideal.under_under P).symm⟩
    obtain ⟨τ, hτ⟩ := numberField_exists_isArithFrobAt (Fact.out : p.Prime) Q
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective L τ
    refine ⟨σ, Set.mem_iInter.mpr fun x => Set.mem_iInter.mpr fun hx => ?_⟩
    have hxA : (x : L) ∈ A := FiniteGaloisIntermediateField.subset_adjoin ℚ t (Set.mem_image_of_mem _ hx)
    let y : A := ⟨x, hxA⟩
    let z : 𝓞 A := ⟨y, (isIntegral_algebraMap_iff (B := L)).mp x.isIntegral_coe⟩
    have hz : algebraMap (𝓞 A) (𝓞 L) z = x := RingOfIntegers.ext rfl
    have hh := (numberField_isArithFrobAt_iff (p := p) Q τ).mp hτ z
    change algebraMap (𝓞 A) (𝓞 L) (τ • z - z ^ p) ∈ P at hh
    rw [map_sub, map_pow, ← hσ] at hh
    change algebraMap (𝓞 A) (𝓞 L) (σ.restrictNormal A • z) -
      (algebraMap (𝓞 A) (𝓞 L) z) ^ p ∈ P at hh
    rwa [algebraMap_ringOfIntegers_restrictNormal_smul, hz] at hh
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed D hdir
    hnonempty (fun s => (hclosed s).isCompact) hclosed
  refine ⟨σ, (numberField_isArithFrobAt_iff (p := p) P σ).mpr fun x => ?_⟩
  exact Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hσ {x}) x) (by simp)

/-- An arithmetic Frobenius topologically generates the decomposition
quotient by inertia in an algebraic Galois extension. -/
theorem numberField_dense_zpowers_quotient_inertia_of_isArithFrobAt
    {L : Type} [Field L] [Algebra ℚ L] [IsGalois ℚ L] {p : ℕ} [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (φ : MulAction.stabilizer Gal(L/ℚ) P) (hφ : IsArithFrobAt ℤ φ.val P) :
    let D := MulAction.stabilizer Gal(L/ℚ) P
    let I := P.inertia D
    Dense (Subgroup.zpowers (QuotientGroup.mk' I φ) : Set (D ⧸ I)) := by
  let G := Gal(L/ℚ)
  let D := MulAction.stabilizer G P
  let I := P.inertia D
  change Dense (Subgroup.zpowers (QuotientGroup.mk' I φ) : Set (D ⧸ I))
  rw [← QuotientGroup.dense_preimage_mk]
  change Dense (((Subgroup.zpowers (QuotientGroup.mk' I φ)).comap (QuotientGroup.mk' I) :
    Subgroup D) : Set D)
  rw [← MonoidHom.map_zpowers, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  let S := Subgroup.zpowers φ ⊔ I
  change Dense (S : Set D)
  rw [dense_iff_inter_open]
  rintro U hU ⟨g, hg⟩
  change IsOpen[(inferInstance : TopologicalSpace G).induced (Subtype.val : D → G)] U at hU
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hU
  let V : Set G := (fun t => g.val * t) ⁻¹' W
  have hV : IsOpen V := hW.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ V := by simpa [V] using hg
  obtain ⟨A, hA, hN, hAV⟩ := (krullTopology_mem_nhds_one_iff_of_normal ℚ L V).mp (hV.mem_nhds h1)
  let _ : Algebra ℚ A := A.algebra'
  let _ : FiniteDimensional ℚ A := hA
  let _ : IsGalois ℚ A := isGalois_iff.mpr ⟨inferInstance, hN⟩
  let E : FiniteGaloisIntermediateField ℚ L := ⟨A⟩
  let _ : NumberField A := NumberField.of_module_finite ℚ A
  let Q := P.under (𝓞 A)
  let _ : Q.IsPrime := inferInstanceAs (P.under (𝓞 A)).IsPrime
  let _ : P.LiesOver Q := inferInstanceAs (P.LiesOver (P.under (𝓞 A)))
  let _ : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨(Ideal.over_def P (Ideal.span {(p : ℤ)})).trans (Ideal.under_under P).symm⟩
  let f : G →* Gal(A/ℚ) := AlgEquiv.restrictNormalHom A
  have hφA : IsArithFrobAt ℤ (f φ.val) Q := numberField_isArithFrobAt_restrictNormal_tower A (p := p) Q P hφ
  have hI : I.map D.subtype = P.inertia G := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact P.coe_mem_inertia.mpr hs
    · intro ht
      exact ⟨⟨t, P.inertia_le_stabilizer ht⟩, P.coe_mem_inertia.mp ht, rfl⟩
  have hS : S.map (f.comp D.subtype) = MulAction.stabilizer Gal(A/ℚ) Q := by
    change (Subgroup.zpowers φ ⊔ I).map (f.comp D.subtype) = _
    rw [← Subgroup.map_map, Subgroup.map_sup, MonoidHom.map_zpowers, hI,
      Subgroup.map_sup, MonoidHom.map_zpowers, sup_comm]
    rw [show (P.inertia G).map f = Q.inertia Gal(A/ℚ) from
      numberField_inertia_map_restrictNormal_of_isGalois E P]
    exact numberField_inertia_sup_zpowers_eq_stabilizer (p := p) Q hφA
  have hga : f g.val ∈ MulAction.stabilizer Gal(A/ℚ) Q :=
    (numberField_stabilizer_map_restrictNormal_of_isGalois E P) ▸ Subgroup.mem_map_of_mem f g.property
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp (hS.symm ▸ hga)
  have hfix : g.val⁻¹ * u.val ∈ A.fixingSubgroup := by
    rw [← A.restrictNormalHom_ker]
    change f (g.val⁻¹ * u.val) = 1
    rw [map_mul, map_inv, show f u.val = f g.val from he, inv_mul_cancel]
  have hw := hAV hfix
  change g.val * (g.val⁻¹ * u.val) ∈ W at hw
  rw [mul_inv_cancel_left] at hw
  exact ⟨u, hw, hu⟩

end Utilities
