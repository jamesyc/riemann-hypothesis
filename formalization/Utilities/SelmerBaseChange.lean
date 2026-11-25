module

public import Utilities.SelmerCoefficientMap
public import Utilities.SelmerKernelAction
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

@[expose] public section

open groupCohomology
open scoped TensorProduct

namespace Utilities.DiscreteGaloisModule

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
  (A : DiscreteGaloisModule k G) (S : Type) [CommRing S] [Algebra k S]

/-- Extension of the coefficient representation to the tensor product.
Local constancy of each orbit follows by tensor induction. -/
@[implicit_reducible]
def baseChange : DiscreteGaloisModule S G where
  rep := Rep.of ((Module.End.baseChangeHom k S (↥A.rep)).toMonoidHom.comp A.rep.ρ)
  discreteOrbit x := by
    let ρ := (Module.End.baseChangeHom k S (↥A.rep)).toMonoidHom.comp A.rep.ρ
    change IsLocallyConstant (fun g : G => ρ g x)
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
        exact (A.discreteOrbit a).comp (fun b => s ⊗ₜ[k] b)
    | add x y hx hy =>
        simpa only [map_add] using hx.comp₂ hy (· + ·)

@[simp]
theorem baseChange_ρ_tmul (g : G) (s : S) (a : A.rep) :
    (A.baseChange S).rep.ρ g (s ⊗ₜ[k] a) = s ⊗ₜ[k] (A.rep.ρ g a) :=
  rfl

local instance baseChangeCoeffModule : Module k ((A.baseChange S).rep) :=
  inferInstanceAs (Module k (S ⊗[k] A.rep))

local instance baseChangeCoeffTower : IsScalarTower k S ((A.baseChange S).rep) :=
  inferInstanceAs (IsScalarTower k S (S ⊗[k] A.rep))

variable (D : Set (Subgroup G))

local notation "CA" => locallyTrivialCocycles₁ A D
local notation "CS" => locallyTrivialCocycles₁ (baseChange A S) D
local notation "BA" => Submodule.comap (Submodule.subtype CA) (coboundaries₁ (DiscreteGaloisModule.rep A))
local notation "BS" => Submodule.comap (Submodule.subtype CS)
  (coboundaries₁ (DiscreteGaloisModule.rep (baseChange A S)))

/-- Tensor a locally trivial cocycle pointwise with a coefficient scalar. -/
def baseChangeCocycle (s : S) : CA →ₗ[k] CS := by
  let u : A.rep →ₗ[k] (A.baseChange S).rep := TensorProduct.mk k S A.rep s
  have hu (g : G) (a : A.rep) : u (A.rep.ρ g a) = (A.baseChange S).rep.ρ g (u a) := rfl
  refine
    { toFun := fun f => ⟨fun g => s ⊗ₜ[k] f.val g,
        map_mem_locallyTrivialCocycles₁ D u.toAddMonoidHom hu f.property⟩
      map_add' := fun f g => Subtype.ext (funext fun x => u.map_add (f.val x) (g.val x))
      map_smul' := fun a f => Subtype.ext (funext fun x => u.map_smul a (f.val x)) }

@[simp]
theorem baseChangeCocycle_apply (s : S) (f : CA) (g : G) :
    (baseChangeCocycle A S D s f).val g = s ⊗ₜ[k] f.val g :=
  rfl

/-- The map from a Selmer class to the class obtained by pointwise tensoring. -/
def baseChangeClass (s : S) : A.selmerKernel D →ₗ[k] (A.baseChange S).selmerKernel D :=
  Submodule.liftQ BA (((Submodule.mkQ BS).restrictScalars k).comp (baseChangeCocycle A S D s)) (by
    intro f hf
    obtain ⟨a, ha⟩ := hf
    apply LinearMap.mem_ker.mpr
    apply (Submodule.Quotient.mk_eq_zero BS).mpr
    let a' : (A.baseChange S).rep := s ⊗ₜ[k] a
    refine ⟨a', funext fun g => ?_⟩
    change (A.baseChange S).rep.ρ g a' - a' = s ⊗ₜ[k] f.val g
    have hρ : (A.baseChange S).rep.ρ g a' = s ⊗ₜ[k] (A.rep.ρ g a) :=
      baseChange_ρ_tmul A S g s a
    have hz : A.rep.ρ g a - a = f.val g := congrFun ha g
    rw [hρ]
    change (s ⊗ₜ[k] (A.rep.ρ g a)) - (s ⊗ₜ[k] a) = s ⊗ₜ[k] f.val g
    rw [← TensorProduct.tmul_sub, hz])

theorem baseChangeClass_mk (s : S) (f : CA) :
    baseChangeClass A S D s ((Submodule.mkQ BA) f) = (Submodule.mkQ BS) (baseChangeCocycle A S D s f) :=
  rfl

/-- The canonical map from the scalar extension of the Selmer kernel to
the Selmer kernel formed using scalar-extended coefficients. -/
def selmerBaseChangeMap : S ⊗[k] A.selmerKernel D →ₗ[S] (A.baseChange S).selmerKernel D :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := baseChangeClass A S D
      map_add' := by
        intro s t
        apply LinearMap.ext
        intro x
        obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective BA) x
        rw [LinearMap.add_apply, baseChangeClass_mk, baseChangeClass_mk, baseChangeClass_mk, ← map_add]
        apply congrArg (Submodule.mkQ BS)
        apply Subtype.ext
        funext g
        exact TensorProduct.add_tmul s t (f.val g)
      map_smul' := by
        intro s t
        apply LinearMap.ext
        intro x
        obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective BA) x
        rw [LinearMap.smul_apply, baseChangeClass_mk, baseChangeClass_mk, ← map_smul]
        apply congrArg (Submodule.mkQ BS)
        apply Subtype.ext
        funext g
        change (s * t) ⊗ₜ[k] f.val g = s • (t ⊗ₜ[k] f.val g)
        exact (TensorProduct.smul_tmul' s t _).symm }

@[simp]
theorem selmerBaseChangeMap_tmul (s : S) (x : A.selmerKernel D) :
    selmerBaseChangeMap A S D (s ⊗ₜ[k] x) = baseChangeClass A S D s x :=
  rfl

section TensorCoordinates

variable {ι M : Type} [AddCommGroup M] [Module k M]
  (b : Module.Basis ι k S)

private noncomputable def tensorCoordinate (i : ι) : (S ⊗[k] M) →ₗ[k] M := by
  classical
  exact (Finsupp.lapply i).comp (TensorProduct.equivFinsuppOfBasisLeft b).toLinearMap

private theorem tensorCoordinate_tmul (i : ι) (t : S) (x : M) :
    tensorCoordinate S b i (t ⊗ₜ[k] x) = b.repr t i • x := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b t x i

private theorem tensorCoordinate_sum [Fintype ι] (z : S ⊗[k] M) :
    ∑ i : ι, b i ⊗ₜ[k] tensorCoordinate S b i z = z := by
  classical
  have hz := (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply z
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype] at hz
  · exact hz
  · intro i
    simp

private theorem tensorCoordinate_baseChange (i : ι) (f : Module.End k M) (z : S ⊗[k] M) :
    tensorCoordinate S b i (f.baseChange S z) = f (tensorCoordinate S b i z) := by
  induction z using TensorProduct.inductionOn with
  | tmul t x => rw [LinearMap.baseChange_tmul, tensorCoordinate_tmul, tensorCoordinate_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorCoordinates

section FiniteFree

variable {ι : Type}

/-- Finite free base change commutes with the Selmer kernel. The same basis
simultaneously separates the cocycle equations and all local coboundaries. -/
theorem selmerBaseChangeMap_bijective_of_basis [Fintype ι] (b : Module.Basis ι k S) :
    Function.Bijective (selmerBaseChangeMap A S D) := by
  classical
  let F := selmerBaseChangeMap A S D
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro z hz
    change F z = 0 at hz
    choose f hf using fun i : ι => (Submodule.mkQ_surjective BA) (tensorCoordinate S b i z)
    have hzsum : (∑ i : ι, b i ⊗ₜ[k] (Submodule.mkQ BA) (f i)) = z := by
      simp only [hf, tensorCoordinate_sum]
    let c : ι → CS := fun i => baseChangeCocycle A S D (b i) (f i)
    have hzero : (Submodule.mkQ BS) (∑ i : ι, c i) = 0 := by
      rw [map_sum]
      have h := congrArg F hzsum
      rw [map_sum, hz] at h
      simpa only [F, selmerBaseChangeMap_tmul, baseChangeClass_mk, c] using h
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero BS).mp hzero
    have hscalar (i : ι) (g : G) :
        tensorCoordinate S b i ((∑ j : ι, c j).val g) = (f i).val g := by
      rw [Submodule.coe_sum, Finset.sum_apply, map_sum]
      simp only [c, baseChangeCocycle_apply, tensorCoordinate_tmul, Module.Basis.repr_self,
        Finsupp.single_apply, ite_smul, zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hfi (i : ι) : (Submodule.mkQ BA) (f i) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero BA).mpr
      refine ⟨tensorCoordinate S b i a, funext fun g => ?_⟩
      have hag : (A.baseChange S).rep.ρ g a - a = (∑ j : ι, c j).val g := congrFun ha g
      have h := congrArg (tensorCoordinate S b i) hag
      rw [map_sub, hscalar i g] at h
      change tensorCoordinate S b i ((A.baseChange S).rep.ρ g a) - tensorCoordinate S b i a = _ at h
      rw [show tensorCoordinate S b i ((A.baseChange S).rep.ρ g a) =
        A.rep.ρ g (tensorCoordinate S b i a) from tensorCoordinate_baseChange S b i (A.rep.ρ g) a] at h
      exact h
    rw [Submodule.mem_bot, ← hzsum]
    simp only [hfi, TensorProduct.tmul_zero, Finset.sum_const_zero]
  · intro x
    obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective BS) x
    have hcoord (i : ι) (g : G) (a : (A.baseChange S).rep) :
        tensorCoordinate S b i ((A.baseChange S).rep.ρ g a) = A.rep.ρ g (tensorCoordinate S b i a) :=
      tensorCoordinate_baseChange S b i (A.rep.ρ g) a
    let a (i : ι) : CA := ⟨fun g => tensorCoordinate S b i (f.val g),
      map_mem_locallyTrivialCocycles₁ D (tensorCoordinate S b i).toAddMonoidHom (hcoord i) f.property⟩
    let c : ι → CS := fun i => baseChangeCocycle A S D (b i) (a i)
    refine ⟨∑ i : ι, b i ⊗ₜ[k] (Submodule.mkQ BA) (a i), ?_⟩
    rw [map_sum]
    simp only [selmerBaseChangeMap_tmul, baseChangeClass_mk]
    change (∑ i : ι, (Submodule.mkQ BS) (c i)) = (Submodule.mkQ BS) f
    rw [← map_sum]
    apply congrArg (Submodule.mkQ BS)
    apply Subtype.ext
    funext g
    rw [Submodule.coe_sum, Finset.sum_apply]
    exact tensorCoordinate_sum S b (f.val g)

end FiniteFree

/-- The canonical comparison is a linear equivalence for finite free
coefficient extensions. -/
noncomputable def selmerBaseChangeEquiv [Module.Free k S] [Module.Finite k S] :
    S ⊗[k] A.selmerKernel D ≃ₗ[S] (A.baseChange S).selmerKernel D := by
  let b := Module.Free.chooseBasis k S
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex k S)
  exact LinearEquiv.ofBijective (selmerBaseChangeMap A S D)
    (selmerBaseChangeMap_bijective_of_basis A S D b)

section Pullback

variable (φ : G →* G) (hφ : Continuous φ) (u : Module.End k A.rep)
  (hu : ∀ g a, u (A.rep.ρ (φ g) a) = A.rep.ρ g (u a))
  (hgroups : ∀ J ∈ D, J.map φ ∈ D)

include hu in
theorem baseChangeSelmerPullback_intertwines (g : G) (a : (A.baseChange S).rep) :
    u.baseChange S ((A.baseChange S).rep.ρ (φ g) a) =
      (A.baseChange S).rep.ρ g (u.baseChange S a) := by
  let x : S ⊗[k] A.rep := a
  change u.baseChange S ((A.baseChange S).rep.ρ (φ g) x) =
    (A.baseChange S).rep.ρ g (u.baseChange S x)
  induction x using TensorProduct.inductionOn with
  | tmul s m => simp only [baseChange_ρ_tmul, LinearMap.baseChange_tmul, hu]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Pullback with the scalar-extended coefficient map. -/
def baseChangeSelmerPullback : Module.End S ((A.baseChange S).selmerKernel D) :=
  (A.baseChange S).pullbackSelmerKernel D φ hφ (u.baseChange S)
    (baseChangeSelmerPullback_intertwines A S φ u hu) hgroups

/-- The scalar extension comparison intertwines pullback on the original
and scalar-extended Selmer kernels. -/
theorem selmerBaseChangeMap_comp_pullback :
    (baseChangeSelmerPullback A S D φ hφ u hu hgroups).comp (selmerBaseChangeMap A S D) =
      (selmerBaseChangeMap A S D).comp ((A.pullbackSelmerKernel D φ hφ u hu hgroups).baseChange S) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective BA) x
  rfl

theorem selmerBaseChangeEquiv_pullback [Module.Free k S] [Module.Finite k S]
    (x : S ⊗[k] A.selmerKernel D) :
    selmerBaseChangeEquiv A S D ((A.pullbackSelmerKernel D φ hφ u hu hgroups).baseChange S x) =
      baseChangeSelmerPullback A S D φ hφ u hu hgroups (selmerBaseChangeEquiv A S D x) :=
  (DFunLike.congr_fun (selmerBaseChangeMap_comp_pullback A S D φ hφ u hu hgroups) x).symm

end Pullback

end Utilities.DiscreteGaloisModule
