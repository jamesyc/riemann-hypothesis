module

public import Utilities.CyclotomicLayer
import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

open IsCyclotomicExtension

namespace Utilities

/-- Restriction to the rational cyclotomic field gives surjective finite
coordinates for automorphisms of a Galois field containing the roots. -/
theorem exists_rationalCyclotomicQuotient {L : Type*} [Field L] [CharZero L]
    [IsGalois ℚ L] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity L n] :
    ∃ γ : Gal(L/ℚ) →* (ZMod n)ˣ, Function.Surjective γ ∧
      ∀ (s : Gal(L/ℚ)) (z : L), z ^ n = 1 → s z = z ^ (γ s).val.val := by
  obtain ⟨ζ, hζ⟩ := (inferInstance : HasEnoughRootsOfUnity L n).prim
  let C := IntermediateField.adjoin ℚ ({ζ} : Set L)
  let _ : IsCyclotomicExtension {n} ℚ C := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let _ : NumberField C := IsCyclotomicExtension.numberField {n} ℚ C
  let _ : IsGalois ℚ C := IsCyclotomicExtension.isGalois {n} ℚ C
  let f : Gal(L/ℚ) →* Gal(C/ℚ) := AlgEquiv.restrictNormalHom C
  let e := Rat.galEquivZMod n C
  refine ⟨e.toMonoidHom.comp f, e.surjective.comp (AlgEquiv.restrictNormalHom_surjective L), ?_⟩
  intro s z hz
  let w : C := ⟨z, mem_cyclotomicLayer_of_pow_eq_one n C hz⟩
  have hw : w ^ n = 1 := Subtype.ext hz
  have h := Rat.galEquivZMod_apply_of_pow_eq n C (f s) hw
  change s (algebraMap C L w) = _ ^ (e (f s)).val.val
  rw [← s.restrictNormal_commutes C w, show s.restrictNormal C w = f s w from rfl, h, map_pow]
  rfl

end Utilities
