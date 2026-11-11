import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Geometry.PlanarOrientation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual inverse angular direction of a chart

The inverse angular vector is computed from the actual derivative of the
forward chart. Its derivative identity follows by differentiating the
genuine local inverse relation. The scalar pullback chain rule therefore
uses no assumed coordinate-derivative formula.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The second column of the inverse of the actual chart derivative. -/
abbrev n07bInverseAngleVector (Ψ : PolarPoint → PolarPoint) (x : PolarPoint) : PolarPoint :=
  ContinuousFlexibility.Statements.canonicalInverseAngularVector Ψ x

/-- The actual forward derivative sends this vector to the angular unit
vector. This is a two-dimensional matrix calculation. -/
theorem n07b_fderiv_inverseAngleVector
    {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hJ : planeJacobian Ψ x ≠ 0) :
    fderiv ℝ Ψ x (n07bInverseAngleVector Ψ x) = (0, 1) := by
  rw [planeCLM_apply_decompose]
  apply Prod.ext <;> dsimp only [n07bInverseAngleVector, canonicalInverseAngularVector] <;>
    field_simp [hJ] <;> simp only [planeJacobian] <;> ring

/-- A genuine local left inverse has the computed angular derivative.
The differential identity is derived from the inverse germ. -/
theorem n07b_fderiv_inverse_angular
    {Ψ G : PolarPoint → PolarPoint} {U : Set PolarPoint} {x : PolarPoint}
    (hU : IsOpen U) (hx : x ∈ U)
    (hleft : ∀ y ∈ U, G (Ψ y) = y)
    (hΨ : DifferentiableAt ℝ Ψ x)
    (hG : DifferentiableAt ℝ G (Ψ x))
    (hJ : planeJacobian Ψ x ≠ 0) :
    fderiv ℝ G (Ψ x) (0, 1) = n07bInverseAngleVector Ψ x := by
  have hgerm : (G ∘ Ψ) =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hleft y hy
  have hchain : (fderiv ℝ G (Ψ x)).comp (fderiv ℝ Ψ x) =
      ContinuousLinearMap.id ℝ PolarPoint := by
    rw [← fderiv_comp x hG hΨ, hgerm.fderiv_eq, fderiv_id]
  have hv := n07b_fderiv_inverseAngleVector hJ
  calc
    fderiv ℝ G (Ψ x) (0, 1) =
        fderiv ℝ G (Ψ x) (fderiv ℝ Ψ x (n07bInverseAngleVector Ψ x)) :=
      congrArg (fderiv ℝ G (Ψ x)) hv.symm
    _ = n07bInverseAngleVector Ψ x :=
      congrArg (fun L : PolarPoint →L[ℝ] PolarPoint => L (n07bInverseAngleVector Ψ x)) hchain

/-- The first-order scalar chain rule along the actual inverse angle. -/
theorem n07b_angularPartial_comp_inverse
    {Ψ G : PolarPoint → PolarPoint} {U : Set PolarPoint} {x : PolarPoint}
    (hU : IsOpen U) (hx : x ∈ U)
    (hleft : ∀ y ∈ U, G (Ψ y) = y)
    (hΨ : DifferentiableAt ℝ Ψ x)
    (hG : DifferentiableAt ℝ G (Ψ x))
    (hJ : planeJacobian Ψ x ≠ 0)
    {F : PolarPoint → ℝ} (hF : DifferentiableAt ℝ F x) :
    angularPartial (F ∘ G) (Ψ x) =
      (n07bInverseAngleVector Ψ x).1 * radialPartial F x +
        (n07bInverseAngleVector Ψ x).2 * angularPartial F x := by
  have hinv : G (Ψ x) = x := hleft x hx
  have hFG : DifferentiableAt ℝ F (G (Ψ x)) := by
    rw [hinv]
    exact hF
  change fderiv ℝ (F ∘ G) (Ψ x) (0, 1) = _
  rw [fderiv_comp (Ψ x) hFG hG, ContinuousLinearMap.comp_apply, hinv,
    n07b_fderiv_inverse_angular hU hx hleft hΨ hG hJ]
  exact polarCLM_apply_decompose (fderiv ℝ F x) (n07bInverseAngleVector Ψ x)

/-- Part A supplies all hypotheses from its actual charts and inverse
identities. Only differentiability of the physical scalar at this point
is needed. -/
theorem n07b_canonical_angularPartial_comp_inverse
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m)
    {F : PolarPoint → ℝ} (hF : DifferentiableAt ℝ F x) :
    angularPartial (F ∘ K.inverseChart z m) (K.chart z m x) =
      (n07bInverseAngleVector (K.chart z m) x).1 * radialPartial F x +
        (n07bInverseAngleVector (K.chart z m) x).2 * angularPartial F x := by
  have hcharts := hK.charts z hz hs m
  have hU : IsOpen (physicalPieceOpen S K z m) := (hK.domains z hz hs m).1
  have hΨ : DifferentiableAt ℝ (K.chart z m) x :=
    (hcharts.2.2.2.2.1.contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (K.inverseChart z m) (K.chart z m x) :=
    (hcharts.2.2.2.2.2.1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hcharts.1 hx))).differentiableAt (by simp)
  exact n07b_angularPartial_comp_inverse hU hx
    hcharts.2.2.1 hΨ hG (hcharts.2.2.2.2.2.2.2 x hx).2.1 hF

end ContinuousFlexibility.Analysis
