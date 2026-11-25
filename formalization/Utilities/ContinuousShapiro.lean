module

public import Utilities.SelmerDecomposition
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Group

@[expose] public section

open groupCohomology Filter
open scoped Topology

namespace Utilities.DiscreteGaloisModule

variable {k G Δ : Type} [CommRing k] [Group G] [TopologicalSpace G] [Group Δ]

/-- Coinduced coefficients for a representation that already extends to the
whole group. The coordinates are the elements of the finite quotient. -/
abbrev finiteQuotientCoinduced (A : DiscreteGaloisModule k G)
    [Finite Δ] (π : G →* Δ) (hπ : IsLocallyConstant π) :
    DiscreteGaloisModule k G := by
  let ρ : G →* Module.End k (Δ → A.rep) :=
    { toFun := fun g =>
        { toFun := fun a δ => A.rep.ρ g (a (δ * π g))
          map_add' := fun a b => funext fun δ => map_add _ _ _
          map_smul' := fun c a => funext fun δ => (A.rep.ρ g).map_smul _ _ }
      map_one' := by ext a δ; simp
      map_mul' := by intro g h; ext a δ; simp [mul_assoc] }
  refine ⟨Rep.of ρ, fun a => ?_⟩
  change IsLocallyConstant (fun g : G => fun δ : Δ => A.rep.ρ g (a (δ * π g)))
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hall : ∀ᶠ g in 𝓝 g₀, ∀ δ : Δ,
      A.rep.ρ g (a (δ * π g₀)) = A.rep.ρ g₀ (a (δ * π g₀)) :=
    Filter.eventually_all.mpr fun δ => (A.discreteOrbit (a (δ * π g₀))).eventually_eq g₀
  filter_upwards [hπ.eventually_eq g₀, hall] with g hg hall'
  exact funext fun δ => hg.symm ▸ hall' δ

@[simp] theorem finiteQuotientCoinduced_rho_apply
    (A : DiscreteGaloisModule k G) [Finite Δ] (π : G →* Δ) (hπ : IsLocallyConstant π)
    (g : G) (a : Δ → A.rep) (δ : Δ) :
    (A.finiteQuotientCoinduced π hπ).rep.ρ g a δ = A.rep.ρ g (a (δ * π g)) := rfl

/-- Evaluation at the identity sends a continuous cocycle of the coinduced
module to one on the kernel of the quotient map. -/
def finiteQuotientEvalCocycle
    (A : DiscreteGaloisModule k G) [Finite Δ] (π : G →* Δ) (hπ : IsLocallyConstant π) :
    (A.finiteQuotientCoinduced π hπ).continuousCocycles₁ →ₗ[k]
      (A.restrictToSubgroup π.ker).continuousCocycles₁ where
  toFun f := ⟨fun h : π.ker => f.val h.val 1, by
    have heq := (mem_cocycles₁_iff f.val).mp f.prop.1
    refine ⟨(mem_cocycles₁_iff _).mpr (fun h g => ?_), ?_⟩
    · have hπh : π h.val = 1 := h.prop
      have hcalc := congrFun (heq h.val g.val) 1
      change f.val (h.val * g.val) 1 = A.rep.ρ h.val (f.val g.val 1) + f.val h.val 1
      simpa [hπh] using hcalc
    · exact (f.prop.2.comp_continuous continuous_subtype_val).comp (fun v => v 1)⟩
  map_add' f g := Subtype.ext rfl
  map_smul' a f := Subtype.ext rfl

section Representatives

variable (A : DiscreteGaloisModule k G) [Finite Δ] (π : G →* Δ)
variable (r : Δ → G) (hr : ∀ δ, π (r δ) = δ)

/-- The kernel element measuring the discrepancy between multiplication
by a group element and the chosen quotient representatives. -/
def finiteQuotientTransition (g : G) (δ : Δ) : π.ker :=
  ⟨r δ * g * (r (δ * π g))⁻¹, by simp [MonoidHom.mem_ker, hr]⟩

omit [TopologicalSpace G] [Finite Δ] in
theorem finiteQuotientTransition_mul (g h : G) (δ : Δ) :
    finiteQuotientTransition π r hr (g * h) δ =
      finiteQuotientTransition π r hr g δ * finiteQuotientTransition π r hr h (δ * π g) := by
  apply Subtype.ext
  simp only [finiteQuotientTransition, Subgroup.coe_mul, map_mul, mul_assoc]
  group

/-- Explicit continuous cocycle lift along finite-quotient coinduction. -/
def finiteQuotientLiftCocycle [IsTopologicalGroup G] (hπ : IsLocallyConstant π) :
    (A.restrictToSubgroup π.ker).continuousCocycles₁ →ₗ[k]
      (A.finiteQuotientCoinduced π hπ).continuousCocycles₁ where
  toFun c := by
    let c' (g : π.ker) : A.rep := c.val g
    have heq (g h : π.ker) : c' (g * h) = A.rep.ρ g.val (c' h) + c' g :=
      (mem_cocycles₁_iff c.val).mp c.prop.1 g h
    refine ⟨fun g δ => A.rep.ρ (r δ)⁻¹ (c' (finiteQuotientTransition π r hr g δ)), ?_, ?_⟩
    · apply (mem_cocycles₁_iff _).mpr
      intro g h
      apply funext
      intro δ
      change A.rep.ρ (r δ)⁻¹ (c' (finiteQuotientTransition π r hr (g * h) δ)) =
        A.rep.ρ g (A.rep.ρ (r (δ * π g))⁻¹ (c' (finiteQuotientTransition π r hr h (δ * π g)))) +
        A.rep.ρ (r δ)⁻¹ (c' (finiteQuotientTransition π r hr g δ))
      rw [finiteQuotientTransition_mul, heq, map_add, ← mul_apply_eq_comp, ← map_mul]
      have hn : (r δ)⁻¹ * (finiteQuotientTransition π r hr g δ).val =
          g * (r (δ * π g))⁻¹ := by
        change (r δ)⁻¹ * (r δ * g * (r (δ * π g))⁻¹) = _
        group
      rw [hn, map_mul, mul_apply_eq_comp]
    · have hc (δ : Δ) : Continuous (fun g : G => finiteQuotientTransition π r hr g δ) := by
        apply continuous_induced_rng.mpr
        change Continuous (fun g : G => r δ * g * (r (δ * π g))⁻¹)
        exact (continuous_const.mul continuous_id).mul
          (((hπ.comp fun d => r (δ * d)).continuous).inv)
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro g
      have h (δ : Δ) : ∀ᶠ g' in 𝓝 g,
          c' (finiteQuotientTransition π r hr g' δ) = c' (finiteQuotientTransition π r hr g δ) :=
        (c.prop.2.comp_continuous (hc δ)).eventually_eq g
      filter_upwards [Filter.eventually_all.mpr h] with g' hg'
      exact funext fun δ => congrArg (A.rep.ρ (r δ)⁻¹) (hg' δ)
  map_add' c c' := Subtype.ext (funext fun g => funext fun δ => map_add _ _ _)
  map_smul' a c := Subtype.ext (funext fun g => funext fun δ => (A.rep.ρ _).map_smul _ _)

@[simp] theorem finiteQuotientLiftCocycle_apply [IsTopologicalGroup G]
    (hπ : IsLocallyConstant π) (c : (A.restrictToSubgroup π.ker).continuousCocycles₁)
    (g : G) (δ : Δ) :
    (A.finiteQuotientLiftCocycle π r hr hπ c).val g δ =
      A.rep.ρ (r δ)⁻¹ (c.val (finiteQuotientTransition π r hr g δ)) := rfl

@[simp] theorem finiteQuotientEvalCocycle_apply (hπ : IsLocallyConstant π)
    (f : (A.finiteQuotientCoinduced π hπ).continuousCocycles₁) (g : π.ker) :
    (A.finiteQuotientEvalCocycle π hπ f).val g = f.val g.val 1 := rfl

theorem finiteQuotientEval_liftCocycle [IsTopologicalGroup G] (hπ : IsLocallyConstant π)
    (hr₁ : r 1 = 1) (c : (A.restrictToSubgroup π.ker).continuousCocycles₁) :
    A.finiteQuotientEvalCocycle π hπ (A.finiteQuotientLiftCocycle π r hr hπ c) = c := by
  apply Subtype.ext
  funext g
  rw [finiteQuotientEvalCocycle_apply, finiteQuotientLiftCocycle_apply, hr₁, inv_one, map_one]
  have ht : finiteQuotientTransition π r hr g.val 1 = g := by
    apply Subtype.ext
    have hg : π g.val = 1 := g.prop
    simp [finiteQuotientTransition, hg, hr₁]
  rw [ht]
  rfl

/-- Lifting evaluation changes a cocycle by an explicit coboundary. -/
theorem finiteQuotientLift_evalCocycle_coboundary [IsTopologicalGroup G]
    (hπ : IsLocallyConstant π)
    (f : (A.finiteQuotientCoinduced π hπ).continuousCocycles₁) :
    ∃ a : Δ → A.rep, ∀ g δ,
      f.val g δ - (A.finiteQuotientLiftCocycle π r hr hπ
        (A.finiteQuotientEvalCocycle π hπ f)).val g δ =
          A.rep.ρ g (a (δ * π g)) - a δ := by
  let a (δ : Δ) := A.rep.ρ (r δ)⁻¹ (f.val (r δ) 1)
  refine ⟨a, fun g δ => ?_⟩
  let g₀ := (finiteQuotientTransition π r hr g δ).val
  have hg₀ : π g₀ = 1 := (finiteQuotientTransition π r hr g δ).prop
  have hmul : r δ * g = g₀ * r (δ * π g) := by
    change _ = (r δ * g * (r (δ * π g))⁻¹) * r (δ * π g)
    group
  have h := (mem_cocycles₁_iff _).mp f.prop.1
  have hpair : A.rep.ρ (r δ) (f.val g δ) + f.val (r δ) 1 =
      A.rep.ρ g₀ (f.val (r (δ * π g)) 1) + f.val g₀ 1 := by
    calc
      _ = f.val (r δ * g) 1 := by
        have he := congrFun (h (r δ) g) 1
        simpa [hr] using he.symm
      _ = f.val (g₀ * r (δ * π g)) 1 := by rw [hmul]
      _ = _ := by
        have he := congrFun (h g₀ (r (δ * π g))) 1
        simpa [hg₀] using he
  have hρmul : (r δ)⁻¹ * g₀ = g * (r (δ * π g))⁻¹ := by
    change (r δ)⁻¹ * (r δ * g * (r (δ * π g))⁻¹) = _
    group
  have hleft : A.rep.ρ (r δ)⁻¹ (A.rep.ρ (r δ) (f.val g δ)) = f.val g δ := by
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hright : A.rep.ρ (r δ)⁻¹ (A.rep.ρ g₀ (f.val (r (δ * π g)) 1)) =
      A.rep.ρ g (a (δ * π g)) := by
    rw [← mul_apply_eq_comp, ← map_mul, hρmul, map_mul]
    rfl
  have hsum := congrArg (A.rep.ρ (r δ)⁻¹) hpair
  rw [map_add, map_add, hleft, hright] at hsum
  rw [finiteQuotientLiftCocycle_apply, finiteQuotientEvalCocycle_apply]
  change f.val g δ - A.rep.ρ (r δ)⁻¹ (f.val g₀ 1) = A.rep.ρ g (a (δ * π g)) - a δ
  change f.val g δ + a δ = A.rep.ρ g (a (δ * π g)) + A.rep.ρ (r δ)⁻¹ (f.val g₀ 1) at hsum
  rw [show f.val g δ = A.rep.ρ g (a (δ * π g)) + A.rep.ρ (r δ)⁻¹ (f.val g₀ 1) - a δ from
    eq_sub_of_add_eq hsum]
  abel

end Representatives

end Utilities.DiscreteGaloisModule
