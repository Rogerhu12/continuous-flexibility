module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryJacobianDirections
public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
public import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations

/-!
# Genuine towers of the eight positive geometric atoms

The stored atoms are evaluated at their actual fixed physical or canonical
unit points. The chart components, inverse components, and height supply
joint towers before that affine pullback. The Jacobian tower is computed
from the chart, and its reciprocal uses the proved positive range.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

/-- Pull an actual joint scalar tower back by the fixed unit interval map. -/
def n04PositiveGeometry_unitPullbackDirections
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ univ) f)
    (hU : IsOpen U) (l r : ℝ) :
    SmoothDirections (U ×ˢ unitStrip)
      (fun z => f (z.1, (l + (r - l) * z.2.1, z.2.2))) := by
  let Lp : PolarPoint →L[ℝ] PolarPoint :=
    ((r - l) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let L : (E × PolarPoint) →L[ℝ] (E × PolarPoint) :=
    (ContinuousLinearMap.fst ℝ E PolarPoint).prod
      (Lp.comp (ContinuousLinearMap.snd ℝ E PolarPoint))
  have hL (z : E × PolarPoint) :
      (0, (l, 0)) + L z = (z.1, (l + (r - l) * z.2.1, z.2.2)) := by
    simp only [L, Lp, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.smul_apply, smul_eq_mul, Prod.mk_add_mk, zero_add]
  have hmap : MapsTo (fun z => (0, (l, 0)) + L z) (U ×ˢ unitStrip) (U ×ˢ univ) := by
    intro z hz
    change ((0, (l, 0)) + L z) ∈ U ×ˢ univ
    rw [hL z]
    exact ⟨hz.1, mem_univ _⟩
  exact (J.compAffine L (0, (l, 0))
    (hU.prod (isOpen_Ioo.prod isOpen_univ)) hmap).congrOn
    (fun z _ => congrArg f (hL z))

private def scalarDifferenceDirections {V : Set (E × PolarPoint)}
    {f g : E × PolarPoint → ℝ} (J : SmoothDirections V f) (K : SmoothDirections V g) :
    SmoothDirections V (fun z => f z - g z) :=
  (smoothDirectionsProd J K).comp_contDiff isOpen_univ
    (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ _ => mem_univ _)

/-- The eight literal stored atom families, not replacement scalar
representatives, have genuine joint towers on the unit strip. -/
def n04PositiveGeometry_atomJointDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (state : E → AnnularState S × ℝ) (m : ℕ)
    (hU : IsOpen U) (hc : Convex ℝ U)
    (Jr : SmoothDirections (U ×ˢ univ)
      (fun z => (K.chart (state z.1) m z.2).1))
    (Jθ : SmoothDirections (U ×ˢ univ)
      (fun z => (K.chart (state z.1) m z.2).2))
    (Jir : SmoothDirections (U ×ˢ univ)
      (fun z => (K.inverseChart (state z.1) m z.2).1))
    (Jiθ : SmoothDirections (U ×ˢ univ)
      (fun z => (K.inverseChart (state z.1) m z.2).2))
    (JH : SmoothDirections (U ×ˢ univ)
      (fun z => K.height (state z.1) m z.2))
    (hH : ∀ x ∈ U, ∀ p, 0 < K.height (state x) m p)
    (hJac : ∀ x ∈ U, ∀ p, 0 < planeJacobian (K.chart (state x) m) p)
    (a : Atom) (ha : atomIsGeometry a) :
    SmoothDirections (U ×ˢ unitStrip)
      (fun z => atom D T S C L K (state z.1) m a z.2) := by
  let physical := fun {f : E × PolarPoint → ℝ}
      (J : SmoothDirections (U ×ˢ univ) f) =>
    n04PositiveGeometry_unitPullbackDirections J hU (K.physicalLeft m) (K.physicalRight m)
  let canonical := fun {f : E × PolarPoint → ℝ}
      (J : SmoothDirections (U ×ˢ univ) f) =>
    n04PositiveGeometry_unitPullbackDirections J hU (K.left m) (K.right m)
  let angle : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let Ja : SmoothDirections (U ×ˢ unitStrip) (fun z : E × PolarPoint => z.2.2) :=
    (smoothDirectionsLinearOn angle (hU.prod (isOpen_Ioo.prod isOpen_univ))).congrOn
      (fun _ _ => rfl)
  cases a
  case chartRadial =>
    exact (physical Jr).comp_contDiff isOpen_univ
      ((contDiff_id.sub contDiff_const).div_const (K.right m - K.left m)).contDiffOn
      (fun _ _ => mem_univ _)
  case chartAngleDefect => exact scalarDifferenceDirections (physical Jθ) Ja
  case inverseRadial =>
    exact (canonical Jir).comp_contDiff isOpen_univ
      ((contDiff_id.sub contDiff_const).div_const
        (K.physicalRight m - K.physicalLeft m)).contDiffOn (fun _ _ => mem_univ _)
  case inverseAngleDefect => exact scalarDifferenceDirections (canonical Jiθ) Ja
  case height => exact physical JH
  case heightInverse =>
    exact physical (JH.comp_contDiff isOpen_Ioi
      (contDiffOn_id.inv (fun t (ht : t ∈ Ioi (0 : ℝ)) => ht.ne'))
      (fun z hz => hH z.1 hz.1 z.2))
  case jacobian =>
    exact physical (n04PositiveGeometry_jacobianAtomDirections Jr Jθ isOpen_univ
      (hc.prod convex_univ) (fun x hx p _ => hJac x hx p) false)
  case jacobianInverse =>
    exact physical (n04PositiveGeometry_jacobianAtomDirections Jr Jθ isOpen_univ
      (hc.prod convex_univ) (fun x hx p _ => hJac x hx p) true)
  all_goals exact False.elim ha

end ContinuousFlexibility.Analysis
