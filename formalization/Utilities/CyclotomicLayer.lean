module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Data.Nat.Find
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

namespace Utilities

section Restriction

variable {F L : Type*} [Field F] [NumberField F] [Field L] [Algebra F L]
  [Algebra ℚ L] [IsScalarTower ℚ F L]

open IsCyclotomicExtension

omit [Algebra ℚ L] [IsScalarTower ℚ F L] in
/-- Every root of the layer's order lies in the cyclotomic intermediate field. -/
theorem mem_cyclotomicLayer_of_pow_eq_one (N : ℕ) [NeZero N]
    (E : IntermediateField F L) [IsCyclotomicExtension {N} ℚ E]
    {ζ : L} (hζ : ζ ^ N = 1) : ζ ∈ E := by
  let z := zeta N ℚ E
  have hz : IsPrimitiveRoot (algebraMap E L z) N :=
    (zeta_spec N ℚ E).map_of_injective (algebraMap E L).injective
  obtain ⟨a, _, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  change (z : L) ^ a ∈ E
  exact pow_mem z.property a

/-- An automorphism fixing the cyclotomic roots belongs to the fixing subgroup
of the cyclotomic intermediate field. -/
theorem mem_fixingSubgroup_of_fixes_cyclotomicLayer (N : ℕ) [NeZero N]
    (E : IntermediateField F L) [IsCyclotomicExtension {N} ℚ E] (σ : Gal(L/F))
    (hσ : ∀ ζ : L, ζ ^ N = 1 → σ ζ = ζ) : σ ∈ E.fixingSubgroup := by
  let j : E →ₐ[ℚ] L := E.val.toRingHom.toRatAlgHom
  have hζ := zeta_spec N ℚ E
  have hfix : (σ.restrictScalars ℚ).toAlgHom.comp j = j := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    exact hσ _ (hζ.map_of_injective j.injective).pow_eq_one
  exact (IntermediateField.mem_fixingSubgroup_iff E σ).mpr fun x hx =>
    DFunLike.congr_fun hfix ⟨x, hx⟩

variable (F) [Normal ℚ F]
variable (K : Type*) [Field K] [NumberField K] [Algebra F K] [IsScalarTower ℚ F K]

/-- If the base embeds in the cyclotomic field of order `f`, the cyclotomic
layer of any multiple of `f` can be realized over the base in its algebraic
closure. Restriction to the base agrees with reducing the cyclotomic residue
to order `f` and then restricting through the given embedding. -/
theorem exists_cyclotomicLayer_restrictNormal
    (f N : ℕ) [NeZero f] [NeZero N] [IsCyclotomicExtension {f} ℚ K] (h : f ∣ N) :
    ∃ E : IntermediateField F (AlgebraicClosure F), ∃ _ : IsCyclotomicExtension {N} ℚ E,
      letI : NumberField E := IsCyclotomicExtension.numberField {N} ℚ E
      letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {N} ℚ E
      ∀ s : Gal(E/ℚ), s.restrictNormal F =
        ((Rat.galEquivZMod f K).symm (ZMod.unitsMap h (Rat.galEquivZMod N E s))).restrictNormal F := by
  let Ω := AlgebraicClosure F
  let _ : NeZero (N : F) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := (inferInstance : HasEnoughRootsOfUnity Ω N).prim
  let C := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  let _ : IsCyclotomicExtension {N} ℚ C := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let _ : FiniteDimensional F K := FiniteDimensional.right ℚ F K
  let j : K →ₐ[F] Ω := IsAlgClosed.lift
  let j₀ := j.restrictScalars ℚ
  let B := j₀.fieldRange
  let _ : IsCyclotomicExtension {f} ℚ B := IsCyclotomicExtension.equiv {f} ℚ K j₀.equivFieldRange
  have hBC : B ≤ C := IntermediateField.isCyclotomicExtension_le_of_dvd ℚ Ω f N B C h
  have hj (x : K) : j x ∈ C := hBC (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  let E : IntermediateField F Ω := C.toSubfield.toIntermediateField fun x =>
    j.commutes x ▸ hj (algebraMap F K x)
  let e : C ≃+* E := RingEquiv.refl C
  let hE : IsCyclotomicExtension {N} ℚ E :=
    IsCyclotomicExtension.equiv {N} ℚ C e.toRatAlgEquiv
  refine ⟨E, hE, ?_⟩
  let _ : IsCyclotomicExtension {N} ℚ E := hE
  let _ : NumberField E := IsCyclotomicExtension.numberField {N} ℚ E
  let _ : IsGalois ℚ E := IsCyclotomicExtension.isGalois {N} ℚ E
  let _ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {f} ℚ K
  let jE : K →ₐ[F] E :=
    { toRingHom := j.toRingHom.codRestrict E.toSubring hj
      commutes' := fun x => Subtype.ext (j.commutes x) }
  let _ : Algebra K E := jE.toRingHom.toAlgebra
  let _ : IsScalarTower ℚ K E := IsScalarTower.of_algHom (jE.restrictScalars ℚ)
  let _ : IsScalarTower F K E := IsScalarTower.of_algHom jE
  intro s
  have hK : (s.restrictNormal K) =
      (Rat.galEquivZMod f K).symm (ZMod.unitsMap h (Rat.galEquivZMod N E s)) :=
    (Rat.galEquivZMod f K).injective (by
      rw [MulEquiv.apply_symm_apply]
      exact Rat.galEquivZMod_restrictNormal_apply N E K h s)
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F K s).trans
    (congrArg (AlgEquiv.restrictNormalHom F) hK)

end Restriction

section PrimePower

universe u

open Polynomial

/-- A layer of relative degree `p^j` obtained by adjoining roots of unity
of prime-power order to the base. -/
def IsPrimePowerCyclotomicLayer (p j : ℕ) (F L : Type*)
    [Field F] [Field L] [Algebra F L] : Prop :=
  Module.finrank F L = p ^ j ∧ ∃ k : ℕ, IsCyclotomicExtension {p ^ k} F L

private theorem totient_primePow_le_finrank (F : Type*) [Field F] [NumberField F]
    {p k : ℕ} (hp : p.Prime) {z : F} (hz : IsPrimitiveRoot z (p ^ k)) :
    (p ^ k).totient ≤ Module.finrank ℚ F := by
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  have h := hz.lcm_totient_le_finrank (K := ℚ) hz
    (by simpa only [Nat.lcm_self] using Polynomial.cyclotomic.irreducible_rat hpos)
  simpa only [Nat.lcm_self] using h

/-- The order of a primitive prime-power root is at most twice the absolute
degree of the number field containing it. -/
theorem primePow_le_two_mul_finrank_of_isPrimitiveRoot
    (F : Type*) [Field F] [NumberField F] {p k : ℕ}
    (hp : p.Prime) {z : F} (hz : IsPrimitiveRoot z (p ^ k)) :
    p ^ k ≤ 2 * Module.finrank ℚ F := by
  have h := totient_primePow_le_finrank F hp hz
  cases k with
  | zero =>
    have hdegree : 0 < Module.finrank ℚ F := Module.finrank_pos
    simp only [pow_zero]
    omega
  | succ k =>
    rw [Nat.totient_prime_pow_succ hp] at h
    calc
      p ^ (k + 1) = p ^ k * p := pow_succ _ _
      _ ≤ p ^ k * (2 * (p - 1)) := Nat.mul_le_mul_left _ (by have := hp.two_le; omega)
      _ = 2 * (p ^ k * (p - 1)) := by ring
      _ ≤ 2 * Module.finrank ℚ F := Nat.mul_le_mul_left _ h

private theorem exists_last_primePowerRoot (F : Type*) [Field F] [NumberField F]
    {p k : ℕ} (hp : p.Prime) (hroot : ∃ z : F, IsPrimitiveRoot z (p ^ (k + 1))) :
    ∃ m ≥ k, (∃ z : F, IsPrimitiveRoot z (p ^ (m + 1))) ∧
      ¬ ∃ z : F, IsPrimitiveRoot z (p ^ (m + 2)) := by
  classical
  let P (m : ℕ) := ∃ z : F, IsPrimitiveRoot z (p ^ (m + 1))
  let n := Module.finrank ℚ F
  have hle (m : ℕ) (hm : P m) : m ≤ n := by
    obtain ⟨z, hz⟩ := hm
    have hd := totient_primePow_le_finrank F hp hz
    rw [Nat.totient_prime_pow_succ hp] at hd
    have hp₁ : 1 ≤ p - 1 := by have := hp.two_le; omega
    have hpw := Nat.mul_le_mul_left (p ^ m) hp₁
    have hlt := Nat.lt_pow_self (n := m) hp.one_lt
    omega
  let m := Nat.findGreatest P n
  have hkm : k ≤ m := Nat.le_findGreatest (hle k hroot) hroot
  have hm : P m := Nat.findGreatest_spec (hle k hroot) hroot
  refine ⟨m, hkm, hm, fun hnext => ?_⟩
  have hnext' : P (m + 1) := hnext
  have := Nat.le_findGreatest (hle (m + 1) hnext') hnext'
  change m + 1 ≤ m at this
  omega

private theorem isPrimitiveRoot_of_prime_pow_succ {F : Type*} [Field F]
    {p m : ℕ} (hp : p.Prime) {z : F} (hz : IsPrimitiveRoot (z ^ p) (p ^ (m + 1))) :
    IsPrimitiveRoot z (p ^ (m + 2)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hprev : ¬ z ^ p ^ (m + 1) = 1 := by
    rw [pow_succ' p m, pow_mul]
    exact hz.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hp.ne_zero)
      (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self m))
  have hnext : z ^ p ^ (m + 2) = 1 := by
    rw [pow_succ' p (m + 1), pow_mul]
    exact hz.pow_eq_one
  have h := IsPrimitiveRoot.orderOf z
  rwa [orderOf_eq_prime_pow hprev hnext] at h

private theorem exists_primePowerCyclotomicStep (F : Type u) [Field F] [NumberField F]
    {p m : ℕ} (hp : p.Prime) {z : F} (hz : IsPrimitiveRoot z (p ^ (m + 1)))
    (hnext : ¬ ∃ u : F, IsPrimitiveRoot u (p ^ (m + 2))) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L),
      Module.finrank F L = p ∧ IsCyclotomicExtension {p ^ (m + 2)} F L := by
  have hpoly : Irreducible (X ^ p - C z) := irreducible_X_pow_sub_C_of_prime hp fun u hu =>
    hnext ⟨u, isPrimitiveRoot_of_prime_pow_succ hp (hu ▸ hz)⟩
  let f : F[X] := X ^ p - C z
  let _ : Fact (Irreducible f) := ⟨hpoly⟩
  let L := AdjoinRoot f
  let b := AdjoinRoot.powerBasis hpoly.ne_zero
  let _ : FiniteDimensional F L := b.finite
  let _ : NumberField L := NumberField.of_module_finite F L
  let _ : NeZero (p ^ (m + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hr : IsPrimitiveRoot (AdjoinRoot.root f) (p ^ (m + 2)) := by
    apply isPrimitiveRoot_of_prime_pow_succ hp
    dsimp only [f]
    rw [root_X_pow_sub_C_pow]
    exact hz.map_of_injective (AdjoinRoot.of f).injective
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [b.finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  · rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hr⟩, fun x => ?_⟩
    have hx : x ∈ Algebra.adjoin F {AdjoinRoot.root f} := by
      rw [AdjoinRoot.adjoinRoot_eq_top]
      trivial
    refine Algebra.adjoin_mono ?_ hx
    rintro _ rfl
    exact hr.pow_eq_one

/-- A number field containing a primitive `p`-th root has a cyclotomic
layer of degree `p^j` for every `j`. -/
theorem exists_primePowerCyclotomicLayer (F : Type u) [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) (hroot : ∃ z : F, IsPrimitiveRoot z p) (j : ℕ) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L),
      IsPrimePowerCyclotomicLayer p j F L := by
  have hlayers (j : ℕ) :
      ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L),
        Module.finrank F L = p ^ j ∧ ∃ k : ℕ, IsCyclotomicExtension {p ^ (k + 1)} F L := by
    induction j with
    | zero =>
      refine ⟨F, inferInstance, inferInstance, inferInstance, by simp, 0, ?_⟩
      let _ : NeZero (p ^ (0 + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      rw [IsCyclotomicExtension.iff_singleton]
      exact ⟨by simpa using hroot, fun x => Subalgebra.algebraMap_mem _ x⟩
    | succ j ih =>
      obtain ⟨K, _, _, _, hdeg, k, hK⟩ := ih
      let _ : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      let _ : IsCyclotomicExtension {p ^ (k + 1)} F K := hK
      obtain ⟨m, hkm, ⟨z, hz⟩, hlast⟩ := exists_last_primePowerRoot K hp
        ⟨_, IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) F K⟩
      obtain ⟨L, _, _, _, hLdeg, hL⟩ := exists_primePowerCyclotomicStep K hp hz hlast
      let _ : IsCyclotomicExtension {p ^ (m + 2)} K L := hL
      let _ : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
      let _ : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
      refine ⟨L, inferInstance, inferInstance, inferInstance, ?_, m + 1, ?_⟩
      · rw [← Module.finrank_mul_finrank F K L, hdeg, hLdeg, pow_succ]
      · have h := IsCyclotomicExtension.trans {p ^ (k + 1)} {p ^ (m + 2)} F K L
          (algebraMap K L).injective
        rw [Set.union_comm] at h
        exact (IsCyclotomicExtension.iff_union_of_dvd F L
          ⟨p ^ (m + 2), Set.mem_singleton _, pow_ne_zero _ hp.ne_zero,
            pow_dvd_pow _ (by omega)⟩).mpr h
  obtain ⟨L, _, _, _, hdeg, k, hL⟩ := hlayers j
  exact ⟨L, inferInstance, inferInstance, inferInstance, hdeg, k + 1, hL⟩

/-- A prime-power layer over a cyclotomic subfield still embeds into a
cyclotomic field, with a bound on its ambient modulus. -/
theorem IsPrimePowerCyclotomicLayer.exists_cyclotomic_embedding
    {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
    {p j N : ℕ} (h : IsPrimePowerCyclotomicLayer p j F L) (hp : p.Prime)
    (hN : 0 < N) (f : F →ₐ[ℚ] CyclotomicField N ℚ) :
    ∃ M : ℕ, 0 < M ∧ M ≤ 2 * Module.finrank ℚ L * N ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField M ℚ) := by
  obtain ⟨k, hL⟩ := h.2
  let M := p ^ k * N
  have hpk : 0 < p ^ k := pow_pos hp.pos _
  have hM : 0 < M := Nat.mul_pos hpk hN
  let _ : NeZero N := ⟨hN.ne'⟩
  let _ : NeZero (p ^ k) := ⟨hpk.ne'⟩
  let _ : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  let _ : NeZero (M : ℚ) := ⟨Nat.cast_ne_zero.mpr hM.ne'⟩
  let _ : NeZero M := ⟨hM.ne'⟩
  let _ : IsCyclotomicExtension {p ^ k} F L := hL
  have hroot := IsCyclotomicExtension.zeta_spec (p ^ k) F L
  refine ⟨M, hM, Nat.mul_le_mul_right N (primePow_le_two_mul_finrank_of_isPrimitiveRoot L hp hroot), ?_⟩
  let K := CyclotomicField M ℚ
  let _ : IsCyclotomicExtension {M} ℚ K := CyclotomicField.isCyclotomicExtension M ℚ
  let _ : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  have hz := IsCyclotomicExtension.zeta_spec M ℚ K
  have hzN : IsPrimitiveRoot (IsCyclotomicExtension.zeta M ℚ K ^ p ^ k) N := hz.pow hM rfl
  have hzpk : IsPrimitiveRoot (IsCyclotomicExtension.zeta M ℚ K ^ N) (p ^ k) :=
    hz.pow hM (Nat.mul_comm _ _)
  let _ := IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ (CyclotomicField N ℚ)
  let g : CyclotomicField N ℚ →ₐ[ℚ] K :=
    @Polynomial.IsSplittingField.lift K ℚ (CyclotomicField N ℚ) _ _ _ _ _
      (X ^ N - 1) inferInstance (by simpa using Polynomial.X_pow_sub_one_splits hzN)
  let _ : Algebra F K := (g.comp f).toRingHom.toAlgebra
  let _ := IsCyclotomicExtension.isSplittingField_X_pow_sub_one (p ^ k) F L
  let i : L →ₐ[F] K :=
    @Polynomial.IsSplittingField.lift K F L _ _ _ _ _
      (X ^ (p ^ k) - 1) inferInstance (by simpa using Polynomial.X_pow_sub_one_splits hzpk)
  exact ⟨i.toRingHom.toRatAlgHom⟩

end PrimePower

end Utilities
