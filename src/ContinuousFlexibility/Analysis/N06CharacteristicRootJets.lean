import ContinuousFlexibility.Analysis.N04bRootBoundaryGeometry
import ContinuousFlexibility.Analysis.N06RootTransmissionJets

/-!
# Actual characteristic-root first jets in physical coordinates

The input is the genuine root-coordinate witness constructed from the
characteristic flow. The chart and height below are the existing smooth
root formulas, pulled back by the actual oriented physical radius.
Translation and radial normalization retain the same angular and height
jets. Thus the common data in `N06RootFirstJets` are computed from one
actual root germ; equality of independently assigned jets is not an input.

This module concerns the root germs. It does not identify an arbitrary
canonical atlas with these germs or assert a new global atlas construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Physical radius, centered at the actual root and oriented into the
negative component. For the two roots the value of `ι` is `1` and `-1`. -/
def n06RootPhysicalInput (r ι : ℝ) (p : PolarPoint) : PolarPoint :=
  (ι * (p.1 - r), p.2)

@[simp] theorem n06RootPhysicalInput_boundary (r ι θ : ℝ) :
    n06RootPhysicalInput r ι (r, θ) = (0, θ) := by
  simp only [n06RootPhysicalInput, sub_self, mul_zero]

theorem contDiff_n06RootPhysicalInput (r ι : ℝ) :
    ContDiff ℝ ∞ (n06RootPhysicalInput r ι) :=
  (contDiff_const.mul (contDiff_fst.sub contDiff_const)).prodMk contDiff_snd

/-- The real chain rule, retaining the physical orientation. -/
theorem n06_fderiv_rootPhysicalInput
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : PolarPoint → E} {θ : ℝ} (hf : DifferentiableAt ℝ f (0, θ))
    (r ι : ℝ) :
    fderiv ℝ (fun p => f (n06RootPhysicalInput r ι p)) (r, θ) (1, 0) =
      ι • fderiv ℝ f (0, θ) (1, 0) := by
  have hfat : DifferentiableAt ℝ f (n06RootPhysicalInput r ι (r, θ)) := by
    simpa only [n06RootPhysicalInput_boundary] using hf
  have hcomp : DifferentiableAt ℝ
      (fun p => f (n06RootPhysicalInput r ι p)) (r, θ) :=
    hfat.comp (r, θ)
      ((contDiff_n06RootPhysicalInput r ι).differentiable (by simp) (r, θ))
  have hline : HasDerivAt (fun t : ℝ => n06RootPhysicalInput r ι (t, θ))
      (ι, 0) r := by
    simpa only [n06RootPhysicalInput, id_eq, mul_one] using
      (((hasDerivAt_id r).sub_const r).const_mul ι).prodMk
        (hasDerivAt_const r θ)
  have hphysical := hfat.hasFDerivAt.comp_hasDerivAt r hline
  have hcoordinate := hcomp.hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ))
  have he := hcoordinate.unique hphysical
  change fderiv ℝ (fun p => f (n06RootPhysicalInput r ι p)) (r, θ) (1, 0) =
    fderiv ℝ f (n06RootPhysicalInput r ι (r, θ)) (ι, 0) at he
  rw [n06RootPhysicalInput_boundary] at he
  calc
    _ = fderiv ℝ f (0, θ) (ι, 0) := he
    _ = ι • fderiv ℝ f (0, θ) (1, 0) := by
      rw [show (ι, (0 : ℝ)) = ι • ((1 : ℝ), (0 : ℝ)) by
        simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]]
      exact map_smul _ _ _

/-- The genuine root chart, including a canonical radial translation
and an explicit radial normalization. -/
def n06NormalizedPhysicalRootChart (G : ℝ × ℝ × ℝ → ℝ)
    (r ι v τ : ℝ) (p : PolarPoint) : PolarPoint :=
  (v + τ * (extendedRootEvenOddChart G (n06RootPhysicalInput r ι p)).1,
    (extendedRootEvenOddChart G (n06RootPhysicalInput r ι p)).2)

/-- The height is the same smooth root density on both physical sides. -/
def n06PhysicalRootHeight (a : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ)
    (r ι : ℝ) (p : PolarPoint) : ℝ :=
  rootSmoothHeight a G (n06RootPhysicalInput r ι p)

def n06RootBoundaryHeight (a : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ)
    (θ : ℝ) : ℝ := rootSmoothHeight a G (0, θ)

def n06RootBoundaryScale (G : ℝ × ℝ × ℝ → ℝ) (θ : ℝ) : ℝ :=
  rootRadialFactor G (0, θ)

def n06RootBoundaryDrift (G : ℝ × ℝ × ℝ → ℝ) (ι θ : ℝ) : ℝ :=
  ι * radialPartial (extendedRootEven G) (0, θ)

def n06RootBoundaryHeightNormal (a : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ)
    (ι θ : ℝ) : ℝ := ι * radialPartial (rootSmoothHeight a G) (0, θ)

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (P : N04bRootCoordinateProperties d c₀ β Φ R σ G)

include P

theorem n06_chart_contDiffAt_zero (θ : ℝ) :
    ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (0, θ) :=
  contDiffAt_extendedRootEvenOddChart P.smooth Real.pi_ne_zero
    (fun x _ => P.odd_period x) (fun x _ => P.even_period x)
    (by simp [rootChartHalfPlane]) (P.odd_positive θ).ne'

/-- Both entries are actual ordinary derivatives of the smooth root
extension. The positive radial entry comes from the divided odd formula. -/
theorem n06_chart_radial_zero (θ : ℝ) :
    fderiv ℝ (extendedRootEvenOddChart G) (0, θ) (1, 0) =
      (n06RootBoundaryScale G θ, radialPartial (extendedRootEven G) (0, θ)) := by
  apply Prod.ext
  · rw [fderiv_extendedRootEvenOddChart_zero P.smooth Real.pi_ne_zero
      (fun x _ => P.odd_period x) (fun x _ => P.even_period x)
      θ (P.odd_positive θ).ne']
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul, mul_one, n06RootBoundaryScale]
  · change (fderiv ℝ (extendedRootEvenOddChart G) (0, θ) (1, 0)).2 =
      fderiv ℝ (fun p => (extendedRootEvenOddChart G p).2) (0, θ) (1, 0)
    rw [fderiv.snd ((P.n06_chart_contDiffAt_zero θ).differentiableAt (by simp))]
    rfl

theorem n06_boundary_scale_pos (θ : ℝ) : 0 < n06RootBoundaryScale G θ :=
  rootRadialFactor_pos (P.odd_positive θ)

/-- The actual root-flow witness gives every field of the first-jet
record. No boundary matching assumption appears in the input. -/
theorem n06_firstJets {a : PolarPoint → ℝ}
    (ha : ∀ θ, ContDiffAt ℝ ∞ a (0, θ))
    (ha0 : ∀ θ, 0 < a (0, θ)) (r ι v τ : ℝ) :
    N06RootFirstJets (n06NormalizedPhysicalRootChart G r ι v τ)
      (n06PhysicalRootHeight a G r ι) r v (τ * ι) β
      (n06RootBoundaryHeight a G) (n06RootBoundaryScale G)
      (n06RootBoundaryDrift G ι) (n06RootBoundaryHeightNormal a G ι) := by
  have hF (θ : ℝ) : DifferentiableAt ℝ
      (fun p => extendedRootEvenOddChart G (n06RootPhysicalInput r ι p)) (r, θ) := by
    have hsource : DifferentiableAt ℝ (extendedRootEvenOddChart G)
        (n06RootPhysicalInput r ι (r, θ)) := by
      simpa only [n06RootPhysicalInput_boundary] using
        (P.n06_chart_contDiffAt_zero θ).differentiableAt (by simp)
    exact hsource.comp (r, θ)
      ((contDiff_n06RootPhysicalInput r ι).differentiable (by simp) (r, θ))
  have hh (θ : ℝ) : DifferentiableAt ℝ (rootSmoothHeight a G) (0, θ) :=
    (P.height_boundary θ (ha θ) (ha0 θ)).2.1.differentiableAt (by simp)
  refine ⟨fun θ => (((hF θ).fst.const_mul τ).const_add v).prodMk (hF θ).snd,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro θ
    have hsource : DifferentiableAt ℝ (rootSmoothHeight a G)
        (n06RootPhysicalInput r ι (r, θ)) := by
      simpa only [n06RootPhysicalInput_boundary] using hh θ
    exact hsource.comp (r, θ)
      ((contDiff_n06RootPhysicalInput r ι).differentiable (by simp) (r, θ))
  · intro θ
    simp only [n06NormalizedPhysicalRootChart, n06RootPhysicalInput_boundary,
      P.extended_chart_zero θ, mul_zero, add_zero]
  · intro θ
    simp only [n06PhysicalRootHeight, n06RootPhysicalInput_boundary,
      n06RootBoundaryHeight]
  · intro θ
    have hD := n06_fderiv_rootPhysicalInput
      ((P.n06_chart_contDiffAt_zero θ).differentiableAt (by simp)) r ι
    rw [P.n06_chart_radial_zero θ] at hD
    change fderiv ℝ (fun p =>
      (v + τ * (extendedRootEvenOddChart G (n06RootPhysicalInput r ι p)).1,
        (extendedRootEvenOddChart G (n06RootPhysicalInput r ι p)).2)) (r, θ) (1, 0) = _
    rw [DifferentiableAt.fderiv_prodMk
      (((hF θ).fst.const_mul τ).const_add v) (hF θ).snd,
      fderiv_const_add, fderiv_const_mul (hF θ).fst τ,
      fderiv.fst (hF θ), fderiv.snd (hF θ)]
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', hD, Prod.smul_mk, smul_eq_mul,
      n06RootBoundaryDrift, mul_assoc]
  · intro θ
    change fderiv ℝ (fun p : PolarPoint =>
      rootSmoothHeight a G (n06RootPhysicalInput r ι p)) (r, θ) (1, 0) =
      ι * radialPartial (rootSmoothHeight a G) (0, θ)
    simpa only [radialPartial, smul_eq_mul] using
      n06_fderiv_rootPhysicalInput (hh θ) r ι

/-- The two radial normalizations use exactly the same computed angular
label, positive height, radial scale, drift, and height-normal derivative. -/
theorem n06_oppositeFirstJets {a : PolarPoint → ℝ}
    (ha : ∀ θ, ContDiffAt ℝ ∞ a (0, θ))
    (ha0 : ∀ θ, 0 < a (0, θ)) (r ι vl vr : ℝ) :
    N06RootFirstJets (n06NormalizedPhysicalRootChart G r ι vl 1)
      (n06PhysicalRootHeight a G r ι) r vl ι β
      (n06RootBoundaryHeight a G) (n06RootBoundaryScale G)
      (n06RootBoundaryDrift G ι) (n06RootBoundaryHeightNormal a G ι) ∧
    N06RootFirstJets (n06NormalizedPhysicalRootChart G r ι vr (-1))
      (n06PhysicalRootHeight a G r ι) r vr (-ι) β
      (n06RootBoundaryHeight a G) (n06RootBoundaryScale G)
      (n06RootBoundaryDrift G ι) (n06RootBoundaryHeightNormal a G ι) ∧
    (∀ θ, 0 < n06RootBoundaryHeight a G θ) ∧
    ∀ θ, 0 < n06RootBoundaryScale G θ := by
  refine ⟨?_, ?_, fun θ => (P.height_boundary θ (ha θ) (ha0 θ)).2.2.1,
    P.n06_boundary_scale_pos⟩
  · simpa only [one_mul] using P.n06_firstJets ha ha0 r ι vl 1
  · simpa only [neg_one_mul] using P.n06_firstJets ha ha0 r ι vr (-1)

end N04bRootCoordinateProperties

end ContinuousFlexibility.Analysis
