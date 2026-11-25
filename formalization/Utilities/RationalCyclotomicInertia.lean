module

public import Utilities.CyclotomicInertia
public import Utilities.CyclotomicLayer
import Utilities.InertiaRestriction
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace Utilities

/-- Inertia above a rational prime realizes every power action on the
roots of unity of that prime order. -/
theorem exists_inertia_acts_by_unit_on_prime_roots
    {L : Type} [Field L] [CharZero L] [IsGalois ℚ L] [IsAlgClosed L]
    {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (b : (ZMod p)ˣ) :
    ∃ t ∈ P.inertia Gal(L/ℚ), ∀ z : L, z ^ p = 1 → t z = z ^ b.val.val := by
  have hp : p.Prime := Fact.out
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p : L) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := (inferInstance : HasEnoughRootsOfUnity L p).prim
  let E := IntermediateField.adjoin ℚ ({ζ} : Set L)
  let _ : IsCyclotomicExtension {p} ℚ E := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let _ : NumberField E := IsCyclotomicExtension.numberField {p} ℚ E
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {p} ℚ E
  let C : FiniteGaloisIntermediateField ℚ L := ⟨E⟩
  let Q := P.under (𝓞 E)
  let _ : Q.IsPrime := inferInstanceAs (P.under (𝓞 E)).IsPrime
  let _ : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨(Ideal.over_def P (Ideal.span {(p : ℤ)})).trans (Ideal.under_under P).symm⟩
  have hker : b ∈ (ZMod.unitsMap (Nat.ordCompl_dvd p p)).ker := by
    change ZMod.unitsMap (Nat.ordCompl_dvd p p) b = 1
    have he : ordCompl[p] p = 1 := by
      simpa only [pow_one] using (Nat.ordCompl_self_pow (p := p) (k := 1) hp)
    let _ : Subsingleton ((ZMod (ordCompl[p] p))ˣ) := by rw [he]; infer_instance
    exact Subsingleton.elim _ _
  have hmap := cyclotomic_inertia_map_eq_ordCompl_ker (n := p) (p := p) E Q
  obtain ⟨τ, hτ, hτb⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hker)
  have hmap' : (P.inertia Gal(L/ℚ)).map (AlgEquiv.restrictNormalHom E) = Q.inertia Gal(E/ℚ) :=
    numberField_inertia_map_restrictNormal_of_isGalois C P
  obtain ⟨t, ht, htt⟩ := Subgroup.mem_map.mp (hmap'.symm ▸ hτ)
  refine ⟨t, ht, fun z hz => ?_⟩
  let w : E := ⟨z, mem_cyclotomicLayer_of_pow_eq_one p E hz⟩
  have hw : w ^ p = 1 := Subtype.ext hz
  have h := Rat.galEquivZMod_apply_of_pow_eq p E τ hw
  change Rat.galEquivZMod p E τ = b at hτb
  rw [hτb] at h
  change t (algebraMap E L w) = (algebraMap E L w) ^ b.val.val
  rw [← t.restrictNormal_commutes E, show t.restrictNormal E = τ from htt, h, map_pow]

end Utilities
