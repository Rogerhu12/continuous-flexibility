module

public import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
public import ContinuousFlexibility.Analysis.N04bRootHeightSymmetry
public import ContinuousFlexibility.Analysis.N01cParameterCalculus
public import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition

/-!
# Actual Jacobian towers from the two chart components

Spatial differentiation is performed on the genuine joint chart tower.
The determinant is then the displayed two-product formula. Positivity
permits the absolute value and reciprocal used by the geometric atoms,
without introducing independent determinant jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint} {F : E → PolarPoint → PolarPoint}

/-- The actual spatial Jacobian has its joint parameter/spatial tower. -/
def n04PositiveGeometry_jacobianDirections
    (Jr : SmoothDirections (U ×ˢ V) (fun z => (F z.1 z.2).1))
    (Jθ : SmoothDirections (U ×ˢ V) (fun z => (F z.1 z.2).2))
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V)) :
    SmoothDirections (U ×ˢ V) (fun z => planeJacobian (F z.1) z.2) := by
  let A := (Jr.spatialRadialTower hV hc).mul (Jθ.spatialAngularTower hV hc)
  let B := (Jθ.spatialRadialTower hV hc).mul (Jr.spatialAngularTower hV hc)
  let J := (smoothDirectionsProd A B).comp_contDiff isOpen_univ
    (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ _ => mem_univ _)
  apply J.congrOn
  intro z hz
  have hF : ContDiffOn ℝ ∞ (F z.1) V :=
    (Jr.spatial_value_contDiffOn hV z.1 hz.1).prodMk
      (Jθ.spatial_value_contDiffOn hV z.1 hz.1)
  exact (n04b_planeJacobian_eq_componentPartials
    ((hF.contDiffAt (hV.mem_nhds hz.2)).differentiableAt (by simp))).symm

/-- Both determinant atoms use the same actual Jacobian and its positive
range. A reciprocal tower is obtained by ordinary smooth composition. -/
def n04PositiveGeometry_jacobianAtomDirections
    (Jr : SmoothDirections (U ×ˢ V) (fun z => (F z.1 z.2).1))
    (Jθ : SmoothDirections (U ×ˢ V) (fun z => (F z.1 z.2).2))
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (hpos : ∀ x ∈ U, ∀ q ∈ V, 0 < planeJacobian (F x) q)
    (inverse : Bool) :
    SmoothDirections (U ×ˢ V)
      (fun z => if inverse then |planeJacobian (F z.1) z.2|⁻¹
        else |planeJacobian (F z.1) z.2|) := by
  let J := n04PositiveGeometry_jacobianDirections Jr Jθ hV hc
  cases inverse with
  | false =>
      exact J.congrOn (fun z hz => (abs_of_pos (hpos z.1 hz.1 z.2 hz.2)).symm)
  | true =>
      let Jinv := J.comp_contDiff isOpen_Ioi
        (contDiffOn_id.inv (fun t (ht : t ∈ Ioi (0 : ℝ)) => ht.ne'))
        (fun z hz => hpos z.1 hz.1 z.2 hz.2)
      exact Jinv.congrOn (fun z hz => congrArg (fun t : ℝ => t⁻¹)
        (abs_of_pos (hpos z.1 hz.1 z.2 hz.2)).symm)

end ContinuousFlexibility.Analysis
