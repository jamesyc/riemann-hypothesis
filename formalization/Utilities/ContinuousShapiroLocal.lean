module

public import Utilities.ContinuousShapiro
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

@[expose] public section

open groupCohomology

namespace Utilities.DiscreteGaloisModule

variable {k G Δ : Type} [CommRing k] [Group G] [TopologicalSpace G] [Group Δ] [Finite Δ]

/-- The host subgroups that correspond to a collection of base restriction
groups, indexed by all conjugates as in the Selmer definition. -/
def finiteQuotientLocalIntersections (π : G →* Δ) (groups : Set (Subgroup G)) :
    Set (Subgroup π.ker) :=
  {I | ∃ D ∈ groups, ∃ r : G, I = (D.map (MulAut.conj r).toMonoidHom).comap π.ker.subtype}

/-- Evaluation on a coinduced cocycle preserves all the corresponding
local coboundaries on the host. -/
def finiteQuotientEvalLocalCocycle (A : DiscreteGaloisModule k G) (π : G →* Δ)
    (hπ : IsLocallyConstant π) (groups : Set (Subgroup G)) :
    (A.finiteQuotientCoinduced π hπ).locallyTrivialCocycles₁ groups →ₗ[k]
      (A.restrictToSubgroup π.ker).locallyTrivialCocycles₁
        (finiteQuotientLocalIntersections π groups) where
  toFun f := by
    let f₀ : (A.finiteQuotientCoinduced π hπ).continuousCocycles₁ := ⟨f.val, f.prop.1⟩
    let ev := A.finiteQuotientEvalCocycle π hπ f₀
    refine ⟨ev.val, ev.prop, ?_⟩
    intro I hI
    obtain ⟨D, hD, r, rfl⟩ := hI
    obtain ⟨u, hu⟩ := f.prop.2 D hD
    let b : A.rep := A.rep.ρ r (u (π r)) - f.val r 1
    refine ⟨b, fun n hn => ?_⟩
    change n.val ∈ D.map (MulAut.conj r).toMonoidHom at hn
    obtain ⟨d, hd, heq⟩ := Subgroup.mem_map.mp hn
    have hprod : r * d = n.val * r := by
      rw [← heq]
      change r * d = (r * d * r⁻¹) * r
      group
    have hπn : π n.val = 1 := n.prop
    have hπd : π d = 1 := by
      have h := congrArg π hprod
      rw [map_mul, map_mul, hπn, one_mul] at h
      exact mul_left_cancel (h.trans (mul_one _).symm)
    have hlocal : f.val d (π r) = A.rep.ρ d (u (π r)) - u (π r) := by
      have h := congrFun (hu d hd) (π r)
      simpa [hπd] using h
    have h := (mem_cocycles₁_iff _).mp f.prop.1.1
    have hpair : A.rep.ρ r (f.val d (π r)) + f.val r 1 =
        A.rep.ρ n.val (f.val r 1) + f.val n.val 1 := by
      calc
        _ = f.val (r * d) 1 := by simpa using (congrFun (h r d) 1).symm
        _ = f.val (n.val * r) 1 := by rw [hprod]
        _ = _ := by simpa [hπn] using congrFun (h n.val r) 1
    have hcomp (a : A.rep) : A.rep.ρ r (A.rep.ρ d a) =
        A.rep.ρ n.val (A.rep.ρ r a) := by
      rw [← mul_apply_eq_comp, ← map_mul, hprod, map_mul, mul_apply_eq_comp]
    change f.val n.val 1 = A.rep.ρ n.val b - b
    calc
      _ = (A.rep.ρ n.val (f.val r 1) + f.val n.val 1) - A.rep.ρ n.val (f.val r 1) := by abel
      _ = (A.rep.ρ r (f.val d (π r)) + f.val r 1) - A.rep.ρ n.val (f.val r 1) := by rw [hpair]
      _ = _ := by
        rw [hlocal, map_sub, hcomp]
        dsimp [b]
        rw [map_sub]
        abel
  map_add' f g := Subtype.ext rfl
  map_smul' a f := Subtype.ext rfl

/-- Continuous Shapiro evaluation on the actual local restriction kernels. -/
def finiteQuotientEvalSelmerKernel (A : DiscreteGaloisModule k G) (π : G →* Δ)
    (hπ : IsLocallyConstant π) (groups : Set (Subgroup G)) :
    (A.finiteQuotientCoinduced π hπ).selmerKernel groups →ₗ[k]
      (A.restrictToSubgroup π.ker).selmerKernel (finiteQuotientLocalIntersections π groups) := by
  apply Submodule.mapQ _ _ (A.finiteQuotientEvalLocalCocycle π hπ groups)
  intro f hf
  change f.val ∈ coboundaries₁ (A.finiteQuotientCoinduced π hπ).rep at hf
  obtain ⟨u, hu⟩ := hf
  refine ⟨u 1, funext fun g => ?_⟩
  have hπg : π g.val = 1 := g.prop
  have h := congrFun (congrFun hu g.val) 1
  change (A.finiteQuotientCoinduced π hπ).rep.ρ g.val u 1 - u 1 = f.val g.val 1 at h
  change A.rep.ρ g.val (u 1) - u 1 = f.val g.val 1
  simpa [hπg] using h

/-- Lifting a host cocycle preserves the base local coboundary conditions.
The proof chooses representatives adapted to one restriction subgroup at
a time, then uses the explicit global coboundary comparison. -/
theorem finiteQuotientLift_mem_locallyTrivial [IsTopologicalGroup G]
    (A : DiscreteGaloisModule k G) (π : G →* Δ) (hπ : IsLocallyConstant π)
    (r : Δ → G) (hr : ∀ δ, π (r δ) = δ) (hr₁ : r 1 = 1)
    (groups : Set (Subgroup G))
    (c : (A.restrictToSubgroup π.ker).locallyTrivialCocycles₁
      (finiteQuotientLocalIntersections π groups)) :
    (A.finiteQuotientLiftCocycle π r hr hπ ⟨c.val, c.prop.1⟩).val ∈
      (A.finiteQuotientCoinduced π hπ).locallyTrivialCocycles₁ groups := by
  classical
  let c₀ : (A.restrictToSubgroup π.ker).continuousCocycles₁ := ⟨c.val, c.prop.1⟩
  let f := A.finiteQuotientLiftCocycle π r hr hπ c₀
  refine ⟨f.prop, fun D hD => ?_⟩
  let S := D.map π
  let base (δ : Δ) := ((QuotientGroup.mk δ : Δ ⧸ S)).out
  have hbase (δ : Δ) : (base δ : Δ ⧸ S) = δ := QuotientGroup.out_eq' _
  have horbit (δ : Δ) (g : G) (hg : g ∈ D) : base (δ * π g) = base δ :=
    congrArg Quotient.out (QuotientGroup.mk_mul_of_mem δ (Subgroup.mem_map_of_mem π hg))
  have hpre (δ : Δ) : ∃ g ∈ D, π g = (base δ)⁻¹ * δ :=
    Subgroup.mem_map.mp (QuotientGroup.eq.mp (hbase δ))
  choose d hd hπd using hpre
  let R (δ : Δ) := r (base δ) * d δ
  have hR (δ : Δ) : π (R δ) = δ := by
    dsimp [R]
    rw [map_mul, hr, hπd, mul_inv_cancel_left]
  let I (δ : Δ) := (D.map (MulAut.conj (r δ)).toMonoidHom).comap π.ker.subtype
  have hlocal (δ : Δ) : ∃ b : A.rep, ∀ g ∈ I δ, c.val g = A.rep.ρ g.val b - b :=
    c.prop.2 _ ⟨D, hD, r δ, rfl⟩
  choose b hb using hlocal
  let a (δ : Δ) := A.rep.ρ (R δ)⁻¹ (b (base δ))
  have hlocalLift (g : G) (hg : g ∈ D) (δ : Δ) :
      (A.finiteQuotientLiftCocycle π R hR hπ c₀).val g δ =
        A.rep.ρ g (a (δ * π g)) - a δ := by
    let n := finiteQuotientTransition π R hR g δ
    have hn : n ∈ I (base δ) := by
      change n.val ∈ D.map (MulAut.conj (r (base δ))).toMonoidHom
      refine Subgroup.mem_map.mpr ⟨d δ * g * (d (δ * π g))⁻¹,
        D.mul_mem (D.mul_mem (hd δ) hg) (D.inv_mem (hd _)), ?_⟩
      change r (base δ) * _ * (r (base δ))⁻¹ =
        r (base δ) * d δ * g * (r (base (δ * π g)) * d (δ * π g))⁻¹
      rw [horbit δ g hg]
      group
    have hbn : (c₀.val n : A.rep) = A.rep.ρ n.val (b (base δ)) - b (base δ) := hb _ n hn
    have hmul : (R δ)⁻¹ * n.val = g * (R (δ * π g))⁻¹ := by
      change (R δ)⁻¹ * (R δ * g * (R (δ * π g))⁻¹) = _
      group
    rw [finiteQuotientLiftCocycle_apply]
    change A.rep.ρ (R δ)⁻¹ (c₀.val n : A.rep) = _
    rw [hbn, map_sub, ← mul_apply_eq_comp, ← map_mul, hmul, map_mul, mul_apply_eq_comp]
    dsimp only [a]
    rw [horbit δ g hg]
  obtain ⟨u, hu⟩ := finiteQuotientLift_evalCocycle_coboundary A π R hR hπ f
  rw [show A.finiteQuotientEvalCocycle π hπ f = c₀ from finiteQuotientEval_liftCocycle A π r hr hπ hr₁ c₀] at hu
  refine ⟨u + a, fun g hg => ?_⟩
  apply funext
  intro δ
  have he := hu g δ
  rw [hlocalLift g hg δ] at he
  change f.val g δ = A.rep.ρ g ((u + a) (δ * π g)) - (u + a) δ
  simp only [Pi.add_apply, map_add]
  rw [eq_add_of_sub_eq he]
  abel

/-- Lift the locally trivial cocycles in the opposite direction. -/
def finiteQuotientLiftLocalCocycle [IsTopologicalGroup G]
    (A : DiscreteGaloisModule k G) (π : G →* Δ) (hπ : IsLocallyConstant π)
    (r : Δ → G) (hr : ∀ δ, π (r δ) = δ) (hr₁ : r 1 = 1)
    (groups : Set (Subgroup G)) :
    (A.restrictToSubgroup π.ker).locallyTrivialCocycles₁
      (finiteQuotientLocalIntersections π groups) →ₗ[k]
        (A.finiteQuotientCoinduced π hπ).locallyTrivialCocycles₁ groups where
  toFun c := ⟨_, finiteQuotientLift_mem_locallyTrivial A π hπ r hr hr₁ groups c⟩
  map_add' c c' := by
    apply Subtype.ext
    funext g δ
    exact (A.rep.ρ (r δ)⁻¹).map_add (c.val _) (c'.val _)
  map_smul' a c := by
    apply Subtype.ext
    funext g δ
    exact (A.rep.ρ (r δ)⁻¹).map_smul a (c.val _)

/-- The lift on the Selmer restriction kernels, using chosen quotient representatives. -/
def finiteQuotientLiftSelmerKernel [IsTopologicalGroup G]
    (A : DiscreteGaloisModule k G) (π : G →* Δ) (hπ : IsLocallyConstant π)
    (r : Δ → G) (hr : ∀ δ, π (r δ) = δ) (hr₁ : r 1 = 1)
    (groups : Set (Subgroup G)) :
    (A.restrictToSubgroup π.ker).selmerKernel (finiteQuotientLocalIntersections π groups) →ₗ[k]
      (A.finiteQuotientCoinduced π hπ).selmerKernel groups := by
  apply Submodule.mapQ _ _ (A.finiteQuotientLiftLocalCocycle π hπ r hr hr₁ groups)
  intro c hc
  change c.val ∈ coboundaries₁ (A.restrictToSubgroup π.ker).rep at hc
  obtain ⟨b', hb⟩ := hc
  let b : A.rep := b'
  let a (δ : Δ) := A.rep.ρ (r δ)⁻¹ b
  refine ⟨a, funext fun g => funext fun δ => ?_⟩
  let n := finiteQuotientTransition π r hr g δ
  have hbn : (c.val n : A.rep) = A.rep.ρ n.val b - b := (congrFun hb n).symm
  have hmul : (r δ)⁻¹ * n.val = g * (r (δ * π g))⁻¹ := by
    change (r δ)⁻¹ * (r δ * g * (r (δ * π g))⁻¹) = _
    group
  have hcomp : A.rep.ρ (r δ)⁻¹ (A.rep.ρ n.val b) = A.rep.ρ g (a (δ * π g)) := by
    rw [← mul_apply_eq_comp, ← map_mul, hmul, map_mul, mul_apply_eq_comp]
  change A.rep.ρ g (a (δ * π g)) - a δ = A.rep.ρ (r δ)⁻¹ (c.val n : A.rep)
  rw [hbn, map_sub, hcomp]

/-- The degree-one continuous Shapiro isomorphism with the local
conditions of Mackey restriction. Evaluation at the identity is the
forward map. -/
noncomputable def finiteQuotientShapiroSelmerEquiv [IsTopologicalGroup G]
    (A : DiscreteGaloisModule k G) (π : G →* Δ) (hπ : IsLocallyConstant π)
    (hπsurj : Function.Surjective π) (groups : Set (Subgroup G)) :
    (A.finiteQuotientCoinduced π hπ).selmerKernel groups ≃ₗ[k]
      (A.restrictToSubgroup π.ker).selmerKernel (finiteQuotientLocalIntersections π groups) := by
  classical
  choose r₀ hr₀ using hπsurj
  let r (δ : Δ) := if δ = 1 then 1 else r₀ δ
  have hr (δ : Δ) : π (r δ) = δ := by by_cases h : δ = 1 <;> simp [r, h, hr₀]
  have hr₁ : r 1 = 1 := by simp [r]
  let u := A.finiteQuotientEvalSelmerKernel π hπ groups
  let v := A.finiteQuotientLiftSelmerKernel π hπ r hr hr₁ groups
  refine LinearEquiv.ofLinearMap u v ?_ ?_
  · apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on _ z fun c => ?_
    change Submodule.Quotient.mk (A.finiteQuotientEvalLocalCocycle π hπ groups
      (A.finiteQuotientLiftLocalCocycle π hπ r hr hr₁ groups c)) = Submodule.Quotient.mk c
    congr 1
    apply Subtype.ext
    have he := finiteQuotientEval_liftCocycle A π r hr hπ hr₁ ⟨c.val, c.prop.1⟩
    have hv := congrArg Subtype.val he
    exact hv
  · apply LinearMap.ext
    intro z
    refine Submodule.Quotient.induction_on _ z fun f => ?_
    change Submodule.Quotient.mk (A.finiteQuotientLiftLocalCocycle π hπ r hr hr₁ groups
      (A.finiteQuotientEvalLocalCocycle π hπ groups f)) = Submodule.Quotient.mk f
    symm
    apply (Submodule.Quotient.eq _).mpr
    obtain ⟨a, ha⟩ := finiteQuotientLift_evalCocycle_coboundary A π r hr hπ ⟨f.val, f.prop.1⟩
    refine ⟨a, funext fun g => funext fun δ => ?_⟩
    exact (ha g δ).symm

end Utilities.DiscreteGaloisModule
