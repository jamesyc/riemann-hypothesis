module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

@[expose] public section

open scoped NumberField

namespace Utilities

/-- A prime that ramifies in a number field divides the modulus of every
cyclotomic field containing an isomorphic copy. -/
theorem prime_dvd_cyclotomicModulus_of_ramification {E L : Type*}
    [Field E] [NumberField E] [Field L] [NumberField L]
    {N p : ℕ} [NeZero N] [Fact p.Prime] [IsCyclotomicExtension {N} ℚ L]
    (j : E →ₐ[ℚ] L) (Q : Ideal (𝓞 E)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(p : ℤ)})] (hQ : 1 < Q.ramificationIdx ℤ) :
    p ∣ N := by
  let : Algebra E L := j.toRingHom.toAlgebra
  let : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  let : Q.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {(p : ℤ)})
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral Q (S := 𝓞 L)
  let : P.IsPrime := hP.isPrime
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P Q _
  by_contra hp
  have hone := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p L P hp
  have hle := Ideal.ramificationIdx_below_le (R := ℤ) Q P
  omega

end Utilities
