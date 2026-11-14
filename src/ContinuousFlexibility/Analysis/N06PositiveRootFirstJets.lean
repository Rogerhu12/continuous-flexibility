module

public import ContinuousFlexibility.Analysis.N06CharacteristicRootJets
public import ContinuousFlexibility.Analysis.ParameterizedPositiveEndpointGerms
public import ContinuousFlexibility.Analysis.BoundaryTaylorExtension
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Positive interpolation of the actual characteristic-root first jets

The radial coordinate is the existing normalized integral of a clipped
slope. Its inputs are the affine radial Taylor fields of the genuine
root charts. The angular coordinate and logarithmic height use the fixed
boundary Taylor extension. The endpoint identities below follow from
these formulas and the previously proved endpoint-germ theorem.

The last theorem substitutes the actual root-flow witnesses. No matching
condition is an input. The result supplies the root first jets needed
for transmission; it does not assert global invertibility of this
interpolation or identify an arbitrary existing canonical atlas with it.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n06PositiveRootRadialTaylor (l r v m : ℝ) (q : Bool → ℝ → ℝ)
    (side : Bool) (p : PolarPoint) : ℝ :=
  (if side then v + m else v) + q side p.2 * (p.1 - (if side then r else l))

def n06PositiveRootRadial (l r δ v m : ℝ) (q : Bool → ℝ → ℝ) :
    PolarPoint → ℝ :=
  parameterizedPositiveReferenceCoordinate l r δ v m
    (fun side => radialPartial (n06PositiveRootRadialTaylor l r v m q side))

def n06PositiveRootAngularData (β κ : Bool → ℝ → ℝ)
    (side : Bool) (j : ℕ) (θ : ℝ) : ℝ :=
  if j = 0 then β side θ - θ else κ side θ

def n06PositiveRootAngular (l r : ℝ) (β κ : Bool → ℝ → ℝ)
    (p : PolarPoint) : ℝ :=
  p.2 + boundaryTaylorExtension 1 l r
    (n06PositiveRootAngularData β κ false) (n06PositiveRootAngularData β κ true) p

def n06PositiveRootLogHeightData (H Hr : Bool → ℝ → ℝ)
    (side : Bool) (j : ℕ) (θ : ℝ) : ℝ :=
  if j = 0 then Real.log (H side θ) else Hr side θ / H side θ

def n06PositiveRootLogHeight (l r : ℝ) (H Hr : Bool → ℝ → ℝ) :
    PolarPoint → ℝ :=
  boundaryTaylorExtension 1 l r
    (n06PositiveRootLogHeightData H Hr false) (n06PositiveRootLogHeightData H Hr true)

def n06PositiveRootHeight (l r : ℝ) (H Hr : Bool → ℝ → ℝ)
    (p : PolarPoint) : ℝ :=
  Real.exp (n06PositiveRootLogHeight l r H Hr p)

def n06PositiveRootChart (l r δ v m : ℝ) (q β κ : Bool → ℝ → ℝ)
    (p : PolarPoint) : PolarPoint :=
  (n06PositiveRootRadial l r δ v m q p, n06PositiveRootAngular l r β κ p)

theorem contDiff_n06PositiveRootRadialTaylor
    {q : Bool → ℝ → ℝ} (hq : ∀ side, ContDiff ℝ ∞ (q side))
    (l r v m : ℝ) (side : Bool) :
    ContDiff ℝ ∞ (n06PositiveRootRadialTaylor l r v m q side) :=
  contDiff_const.add (((hq side).comp contDiff_snd).mul
    (contDiff_fst.sub contDiff_const))

theorem contDiff_n06PositiveRootRadial
    {q : Bool → ℝ → ℝ} (hq : ∀ side, ContDiff ℝ ∞ (q side))
    (l r δ v m : ℝ) : ContDiff ℝ ∞ (n06PositiveRootRadial l r δ v m q) :=
  contDiff_parameterizedPositiveReferenceCoordinate
    (fun side => contDiff_cylinder_radialPartial
      (contDiff_n06PositiveRootRadialTaylor hq l r v m side)) l r δ v m

private theorem n06_contDiff_positiveAngularData
    {β κ : Bool → ℝ → ℝ}
    (hβ : ∀ side, ContDiff ℝ ∞ (β side))
    (hκ : ∀ side, ContDiff ℝ ∞ (κ side)) (side : Bool) (j : ℕ) :
    ContDiff ℝ ∞ (n06PositiveRootAngularData β κ side j) := by
  by_cases hj : j = 0
  · have he : n06PositiveRootAngularData β κ side j =
        (fun θ => β side θ - θ) := by
      funext θ
      simp only [n06PositiveRootAngularData, hj, ite_true]
    rw [he]
    simpa only [id_eq] using (hβ side).sub contDiff_id
  · have he : n06PositiveRootAngularData β κ side j = κ side := by
      funext θ
      simp only [n06PositiveRootAngularData, ite_eq_right hj]
    rw [he]
    exact hκ side

theorem contDiff_n06PositiveRootAngular
    {β κ : Bool → ℝ → ℝ}
    (hβ : ∀ side, ContDiff ℝ ∞ (β side))
    (hκ : ∀ side, ContDiff ℝ ∞ (κ side)) (l r : ℝ) :
    ContDiff ℝ ∞ (n06PositiveRootAngular l r β κ) :=
  contDiff_snd.add (contDiff_boundaryTaylorExtension
    (fun j _ => n06_contDiff_positiveAngularData hβ hκ false j)
    (fun j _ => n06_contDiff_positiveAngularData hβ hκ true j) l r)

private theorem n06_contDiff_positiveLogHeightData
    {H Hr : Bool → ℝ → ℝ}
    (hH : ∀ side, ContDiff ℝ ∞ (H side))
    (hHr : ∀ side, ContDiff ℝ ∞ (Hr side))
    (hpos : ∀ side θ, 0 < H side θ) (side : Bool) (j : ℕ) :
    ContDiff ℝ ∞ (n06PositiveRootLogHeightData H Hr side j) := by
  by_cases hj : j = 0
  · have he : n06PositiveRootLogHeightData H Hr side j =
        (fun θ => Real.log (H side θ)) := by
      funext θ
      simp only [n06PositiveRootLogHeightData, hj, ite_true]
    rw [he]
    exact (hH side).log (fun θ => (hpos side θ).ne')
  · have he : n06PositiveRootLogHeightData H Hr side j = Hr side / H side := by
      funext θ
      simp only [n06PositiveRootLogHeightData, ite_eq_right hj, Pi.div_apply]
    rw [he]
    exact (hHr side).div (hH side) (fun θ => (hpos side θ).ne')

theorem contDiff_n06PositiveRootLogHeight
    {H Hr : Bool → ℝ → ℝ}
    (hH : ∀ side, ContDiff ℝ ∞ (H side))
    (hHr : ∀ side, ContDiff ℝ ∞ (Hr side))
    (hpos : ∀ side θ, 0 < H side θ) (l r : ℝ) :
    ContDiff ℝ ∞ (n06PositiveRootLogHeight l r H Hr) :=
  contDiff_boundaryTaylorExtension
    (fun j _ => n06_contDiff_positiveLogHeightData hH hHr hpos false j)
    (fun j _ => n06_contDiff_positiveLogHeightData hH hHr hpos true j) l r

theorem contDiff_n06PositiveRootHeight
    {H Hr : Bool → ℝ → ℝ}
    (hH : ∀ side, ContDiff ℝ ∞ (H side))
    (hHr : ∀ side, ContDiff ℝ ∞ (Hr side))
    (hpos : ∀ side θ, 0 < H side θ) (l r : ℝ) :
    ContDiff ℝ ∞ (n06PositiveRootHeight l r H Hr) :=
  Real.contDiff_exp.comp (contDiff_n06PositiveRootLogHeight hH hHr hpos l r)

theorem n06_positiveRootHeight_pos (l r : ℝ) (H Hr : Bool → ℝ → ℝ)
    (p : PolarPoint) : 0 < n06PositiveRootHeight l r H Hr p :=
  Real.exp_pos _

/-- This is an output of the normalized primitive's actual endpoint
germ theorem, not an assumed identity of boundary derivatives. -/
theorem n06_positiveRootRadial_firstJets
    {q : Bool → ℝ → ℝ} (hq : ∀ side, ContDiff ℝ ∞ (q side))
    {l r δ v m : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) (hm : m ≠ 0)
    (side : Bool) (θ : ℝ) :
    n06PositiveRootRadial l r δ v m q (if side then r else l, θ) =
        (if side then v + m else v) ∧
      radialPartial (n06PositiveRootRadial l r δ v m q)
        (if side then r else l, θ) = q side θ := by
  have hF := contDiff_n06PositiveRootRadialTaylor hq l r v m
  have hvalue (s : Bool) (η : ℝ) :
      n06PositiveRootRadialTaylor l r v m q s (if s then r else l, η) =
        if s then v + m else v := by
    simp only [n06PositiveRootRadialTaylor, sub_self, mul_zero, add_zero]
  have hgerm := parameterizedPositiveReferenceCoordinate_endpoint_germ
    hF hδ hgap hm hvalue side θ
  refine ⟨hgerm.eq_of_nhds.trans (hvalue side θ), ?_⟩
  have he := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0))
    (hgerm.fderiv_eq (𝕜 := ℝ))
  change radialPartial (n06PositiveRootRadial l r δ v m q)
    (if side then r else l, θ) =
    radialPartial (n06PositiveRootRadialTaylor l r v m q side)
      (if side then r else l, θ) at he
  rw [he]
  have hder : HasDerivAt
      (fun x => n06PositiveRootRadialTaylor l r v m q side (x, θ))
      (q side θ) (if side then r else l) := by
    simpa only [n06PositiveRootRadialTaylor, id_eq, mul_one] using
      ((((hasDerivAt_id (if side then r else l)).sub_const
        (if side then r else l)).const_mul (q side θ)).const_add
        (if side then v + m else v))
  exact (deriv_cylinder_radial_slice ((hF side).differentiable (by simp))
    (if side then r else l) θ).symm.trans hder.deriv

private theorem n06_boundaryTaylor_firstJets
    {l r : ℝ} (hlr : l ≠ r) (A : Bool → ℕ → ℝ → ℝ)
    (side : Bool) (θ : ℝ) :
    boundaryTaylorExtension 1 l r (A false) (A true)
        (if side then r else l, θ) = A side 0 θ ∧
      deriv (fun x => boundaryTaylorExtension 1 l r (A false) (A true) (x, θ))
        (if side then r else l) = A side 1 θ := by
  have h0 := iteratedDeriv_boundaryTaylorExtension 1 hlr (A false) (A true)
    side (k := 0) (by omega) θ
  have h1 := iteratedDeriv_boundaryTaylorExtension 1 hlr (A false) (A true)
    side (k := 1) (by omega) θ
  cases side <;> simpa only [Bool.false_eq_true, ite_false, ite_true,
    iteratedDeriv_zero, iteratedDeriv_one] using And.intro h0 h1

theorem n06_positiveRootAngular_firstJets
    {β κ : Bool → ℝ → ℝ}
    (hβ : ∀ side, ContDiff ℝ ∞ (β side))
    (hκ : ∀ side, ContDiff ℝ ∞ (κ side))
    {l r : ℝ} (hlr : l ≠ r) (side : Bool) (θ : ℝ) :
    n06PositiveRootAngular l r β κ (if side then r else l, θ) = β side θ ∧
      radialPartial (n06PositiveRootAngular l r β κ)
        (if side then r else l, θ) = κ side θ := by
  let E := boundaryTaylorExtension 1 l r
    (n06PositiveRootAngularData β κ false) (n06PositiveRootAngularData β κ true)
  have hE : ContDiff ℝ ∞ E := contDiff_boundaryTaylorExtension
    (fun j _ => n06_contDiff_positiveAngularData hβ hκ false j)
    (fun j _ => n06_contDiff_positiveAngularData hβ hκ true j) l r
  have hj := n06_boundaryTaylor_firstJets hlr (n06PositiveRootAngularData β κ) side θ
  have hv : E (if side then r else l, θ) = β side θ - θ := by
    simpa only [E, n06PositiveRootAngularData, if_true] using hj.1
  have hd : radialPartial E (if side then r else l, θ) = κ side θ := by
    rw [← deriv_cylinder_radial_slice (hE.differentiable (by simp))]
    simpa only [E, n06PositiveRootAngularData, Nat.one_ne_zero, if_false] using hj.2
  constructor
  · change θ + E (if side then r else l, θ) = β side θ
    rw [hv]
    ring
  · change radialPartial (fun p => p.2 + E p) (if side then r else l, θ) = _
    rw [radialPartial_add differentiableAt_snd
      (hE.differentiable (by simp) _), radialPartial_snd, zero_add, hd]

theorem n06_positiveRootHeight_firstJets
    {H Hr : Bool → ℝ → ℝ}
    (hH : ∀ side, ContDiff ℝ ∞ (H side))
    (hHr : ∀ side, ContDiff ℝ ∞ (Hr side))
    (hpos : ∀ side θ, 0 < H side θ)
    {l r : ℝ} (hlr : l ≠ r) (side : Bool) (θ : ℝ) :
    n06PositiveRootHeight l r H Hr (if side then r else l, θ) = H side θ ∧
      radialPartial (n06PositiveRootHeight l r H Hr)
        (if side then r else l, θ) = Hr side θ := by
  have hE := contDiff_n06PositiveRootLogHeight hH hHr hpos l r
  have hj := n06_boundaryTaylor_firstJets hlr (n06PositiveRootLogHeightData H Hr) side θ
  have hv : n06PositiveRootLogHeight l r H Hr (if side then r else l, θ) =
      Real.log (H side θ) := by
    simpa only [n06PositiveRootLogHeight, n06PositiveRootLogHeightData, if_true] using hj.1
  have hd : radialPartial (n06PositiveRootLogHeight l r H Hr)
      (if side then r else l, θ) = Hr side θ / H side θ := by
    rw [← deriv_cylinder_radial_slice (hE.differentiable (by simp))]
    simpa only [n06PositiveRootLogHeight, n06PositiveRootLogHeightData,
      Nat.one_ne_zero, if_false] using hj.2
  constructor
  · change Real.exp (n06PositiveRootLogHeight l r H Hr (if side then r else l, θ)) = _
    rw [hv, Real.exp_log (hpos side θ)]
  · change fderiv ℝ (fun p => Real.exp (n06PositiveRootLogHeight l r H Hr p))
      (if side then r else l, θ) (1, 0) = _
    rw [fderiv_exp (hE.differentiable (by simp) _),
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    change Real.exp (n06PositiveRootLogHeight l r H Hr (if side then r else l, θ)) *
      radialPartial (n06PositiveRootLogHeight l r H Hr) (if side then r else l, θ) = _
    rw [hv, Real.exp_log (hpos side θ), hd]
    exact mul_div_cancel₀ _ (hpos side θ).ne'

/-- Every jet in this record has just been computed from the actual
integral and Taylor formulas. The orientation is part of the input
coordinate normalization, not a separate compatibility condition. -/
theorem n06_positiveRootInterpolation_firstJets
    {β H ρ κ Hr : Bool → ℝ → ℝ} (σ : Bool → ℝ)
    (hβ : ∀ side, ContDiff ℝ ∞ (β side))
    (hH : ∀ side, ContDiff ℝ ∞ (H side))
    (hρ : ∀ side, ContDiff ℝ ∞ (ρ side))
    (hκ : ∀ side, ContDiff ℝ ∞ (κ side))
    (hHr : ∀ side, ContDiff ℝ ∞ (Hr side))
    (hpos : ∀ side θ, 0 < H side θ)
    {l r δ v m : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) (hm : m ≠ 0)
    (side : Bool) :
    N06RootFirstJets
      (n06PositiveRootChart l r δ v m (fun s θ => σ s * ρ s θ) β κ)
      (n06PositiveRootHeight l r H Hr) (if side then r else l)
      (if side then v + m else v) (σ side) (β side) (H side) (ρ side)
      (κ side) (Hr side) := by
  have hq (s : Bool) : ContDiff ℝ ∞ (fun θ => σ s * ρ s θ) :=
    contDiff_const.mul (hρ s)
  have hY := contDiff_n06PositiveRootRadial hq l r δ v m
  have hφ := contDiff_n06PositiveRootAngular hβ hκ l r
  have hh := contDiff_n06PositiveRootHeight hH hHr hpos l r
  have hlr : l ≠ r := ne_of_lt (by linarith : l < r)
  refine ⟨fun θ => (hY.prodMk hφ).differentiable (by simp) _,
    fun θ => hh.differentiable (by simp) _, ?_, ?_, ?_, ?_⟩
  · intro θ
    exact Prod.ext (n06_positiveRootRadial_firstJets hq hδ hgap hm side θ).1
      (n06_positiveRootAngular_firstJets hβ hκ hlr side θ).1
  · intro θ
    exact (n06_positiveRootHeight_firstJets hH hHr hpos hlr side θ).1
  · intro θ
    change fderiv ℝ (fun p =>
      (n06PositiveRootRadial l r δ v m (fun s θ => σ s * ρ s θ) p,
        n06PositiveRootAngular l r β κ p)) (if side then r else l, θ) (1, 0) = _
    rw [DifferentiableAt.fderiv_prodMk (hY.differentiable (by simp) _)
      (hφ.differentiable (by simp) _), ContinuousLinearMap.prod_apply]
    exact Prod.ext (n06_positiveRootRadial_firstJets hq hδ hgap hm side θ).2
      (n06_positiveRootAngular_firstJets hβ hκ hlr side θ).2
  · intro θ
    exact (n06_positiveRootHeight_firstJets hH hHr hpos hlr side θ).2

private theorem n06_contDiff_axis_restriction {f : PolarPoint → ℝ}
    (hf : ∀ θ, ContDiffAt ℝ ∞ f (0, θ)) :
    ContDiff ℝ ∞ (fun θ => f (0, θ)) :=
  contDiff_iff_contDiffAt.mpr fun θ => (hf θ).comp θ
    (contDiffAt_const.prodMk contDiffAt_id)

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (P : N04bRootCoordinateProperties d c₀ β Φ R σ G)

include P

theorem n06_boundary_scale_smooth : ContDiff ℝ ∞ (n06RootBoundaryScale G) := by
  have hfield : ∀ θ, ContDiffAt ℝ ∞
      (radialPartial (fun p => (extendedRootEvenOddChart G p).1)) (0, θ) :=
    fun θ => contDiffAt_radialPartial (P.n06_chart_contDiffAt_zero θ).fst (by simp)
  have he : n06RootBoundaryScale G =
      fun θ => radialPartial (fun p => (extendedRootEvenOddChart G p).1) (0, θ) := by
    funext θ
    change n06RootBoundaryScale G θ =
      fderiv ℝ (fun p => (extendedRootEvenOddChart G p).1) (0, θ) (1, 0)
    rw [fderiv.fst ((P.n06_chart_contDiffAt_zero θ).differentiableAt (by simp)),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', P.n06_chart_radial_zero θ]
  rw [he]
  exact n06_contDiff_axis_restriction hfield

theorem n06_boundary_drift_smooth (ι : ℝ) :
    ContDiff ℝ ∞ (n06RootBoundaryDrift G ι) := by
  have hs : ContDiff ℝ ∞ (extendedRootEven G) :=
    contDiff_extendedRootEven P.smooth Real.pi_ne_zero (fun x _ => P.even_period x)
  exact contDiff_const.mul (n06_contDiff_axis_restriction
    (fun θ => contDiffAt_radialPartial hs.contDiffAt (by simp)))

theorem n06_boundary_height_smooth {a : PolarPoint → ℝ}
    (ha : ∀ θ, ContDiffAt ℝ ∞ a (0, θ)) (ha0 : ∀ θ, 0 < a (0, θ)) :
    ContDiff ℝ ∞ (n06RootBoundaryHeight a G) :=
  n06_contDiff_axis_restriction (fun θ => (P.height_boundary θ (ha θ) (ha0 θ)).2.1)

theorem n06_boundary_heightNormal_smooth {a : PolarPoint → ℝ}
    (ha : ∀ θ, ContDiffAt ℝ ∞ a (0, θ)) (ha0 : ∀ θ, 0 < a (0, θ)) (ι : ℝ) :
    ContDiff ℝ ∞ (n06RootBoundaryHeightNormal a G ι) :=
  contDiff_const.mul (n06_contDiff_axis_restriction (fun θ => contDiffAt_radialPartial
    (P.height_boundary θ (ha θ) (ha0 θ)).2.1 (by simp)))

end N04bRootCoordinateProperties

/-- Actual characteristic-root witnesses supply all interpolation data
and their smoothness. The positive and root charts consequently share
the five boundary functions, with precisely their chosen orientations. -/
theorem n06_actualRoot_positiveInterpolation_firstJets
    {d c₀ a : Bool → PolarPoint → ℝ} {β : Bool → ℝ → ℝ}
    {Φ : Bool → ℝ → ℝ → ℝ} {R σ : Bool → ℝ}
    {G : Bool → ℝ × ℝ × ℝ → ℝ}
    (P : ∀ side, N04bRootCoordinateProperties (d side) (c₀ side) (β side)
      (Φ side) (R side) (σ side) (G side))
    (ha : ∀ side θ, ContDiffAt ℝ ∞ (a side) (0, θ))
    (ha0 : ∀ side θ, 0 < a side (0, θ)) (ι τ : Bool → ℝ)
    {l r δ v m : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) (hm : m ≠ 0)
    (side : Bool) :
    N06RootFirstJets
      (n06PositiveRootChart l r δ v m
        (fun s θ => (τ s * ι s) * n06RootBoundaryScale (G s) θ) β
        (fun s => n06RootBoundaryDrift (G s) (ι s)))
      (n06PositiveRootHeight l r
        (fun s => n06RootBoundaryHeight (a s) (G s))
        (fun s => n06RootBoundaryHeightNormal (a s) (G s) (ι s)))
      (if side then r else l) (if side then v + m else v) (τ side * ι side)
      (β side) (n06RootBoundaryHeight (a side) (G side))
      (n06RootBoundaryScale (G side)) (n06RootBoundaryDrift (G side) (ι side))
      (n06RootBoundaryHeightNormal (a side) (G side) (ι side)) :=
  n06_positiveRootInterpolation_firstJets (fun s => τ s * ι s)
    (fun s => (P s).label_smooth)
    (fun s => (P s).n06_boundary_height_smooth (ha s) (ha0 s))
    (fun s => (P s).n06_boundary_scale_smooth)
    (fun s => (P s).n06_boundary_drift_smooth (ι s))
    (fun s => (P s).n06_boundary_heightNormal_smooth (ha s) (ha0 s) (ι s))
    (fun s θ => ((P s).height_boundary θ (ha s θ) (ha0 s θ)).2.2.1)
    hδ hgap hm side

end ContinuousFlexibility.Analysis
