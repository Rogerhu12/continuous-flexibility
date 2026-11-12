import ContinuousFlexibility.Analysis.N07bReferenceGeometry
import ContinuousFlexibility.Analysis.N07aAngularJacobianEnvelope

/-!
# Primitive identities on the actual moving pieces

The two reference directions use one chain rule with an arbitrary vector.
The density drift is pulled back by the actual material radius chart.
Source and reciprocal-height factors are expressed through the stored
canonical source and the genuine inverse-chart Jacobian. Every local
identity holds on a whole physical or material piece, before derivatives
are transferred. No quantitative field estimate is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

/-- One actual chain rule handles both transported reference directions. -/
theorem n04Realization_referenceDirection_eqOn
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (e : PolarPoint) :
    EqOn (n07bReferenceDirection (canonicalCurrentPoint C K z m)
      (canonicalReferencePoint C K z m) e)
      (fun x => fderiv ℝ (K.inverseChart z m) (K.chart z m x)
        (fderiv ℝ (K.chart (C.referenceState, 0) m)
          (canonicalReferencePoint C K z m x) e)) (physicalPieceOpen S K z m) := by
  intro x hx
  have hc := hgeom.charts z hz hs m
  have hr := hgeom.charts (C.referenceState, 0) href hsref m
  have hq := hc.1 hx
  have hx₀ := hr.2.1 hq
  have he := hr.2.2.2.1 (K.chart z m x) hq
  have hF := (hr.2.2.2.2.1.contDiffAt
    ((hgeom.domains (C.referenceState, 0) href hsref m).1.mem_nhds hx₀)).differentiableAt
      (by simp)
  have hG : DifferentiableAt ℝ (K.inverseChart z m)
      (K.chart (C.referenceState, 0) m
        (K.inverseChart (C.referenceState, 0) m (K.chart z m x))) := by
    rw [he]
    exact (hc.2.2.2.2.2.1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  change fderiv ℝ (K.inverseChart z m ∘ K.chart (C.referenceState, 0) m)
    (K.inverseChart (C.referenceState, 0) m (K.chart z m x)) e = _
  rw [fderiv_comp _ hG hF, ContinuousLinearMap.comp_apply, he]

/-- The current primitive direction is the angular column of the genuine
inverse differential throughout the current physical piece. -/
theorem n04Realization_inverseAngleDirection_eqOn
    (hgeom : CanonicalGeometry D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    EqOn (canonicalPrimitiveDirection C K z m 0)
      (fun x => fderiv ℝ (K.inverseChart z m) (K.chart z m x) (0, 1))
      (physicalPieceOpen S K z m) := by
  intro x hx
  have hc := hgeom.charts z hz hs m
  have hU := (hgeom.domains z hz hs m).1
  have hF := (hc.2.2.2.2.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hG := (hc.2.2.2.2.2.1.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hc.1 hx))).differentiableAt (by simp)
  rw [n07b_canonicalPrimitiveDirection_zero]
  exact (n07b_fderiv_inverse_angular hU hx hc.2.2.1 hF hG
    (hc.2.2.2.2.2.2.2 x hx).2.1).symm

/-- The exact material drift has the reciprocal density denominator.
The equality holds on the genuine open material preimage. -/
theorem n04Realization_materialDirectionDrift_eqOn
    (hT : IsMaterialData D T) (hgeom : CanonicalGeometry D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (Y : PolarPoint → PolarPoint) :
    EqOn (n07bMaterialDirectionDrift T K z m Y)
      (fun y => -(n07bMaterialDirectionV1 T Y y *
          radialPartial (canonicalMaterialJacobian T K z m ∘ n07bMaterialRadiusChart T) y +
        n07bMaterialDirectionV2 T Y y *
          angularPartial (canonicalMaterialJacobian T K z m ∘ n07bMaterialRadiusChart T) y) /
        (2 * canonicalMaterialJacobian T K z m (n07bMaterialRadiusChart T y)))
      (n07bSourceMaterialPiece T K z m) := by
  intro y hy
  have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
  have hc := n07bSourceMaterialJacobian_contDiffAt hT hgeom hz hs m hx
  have hd := n07b_directional_materialized hT Y
    (((hgeom.domains z hz hs m).2.2.1 hx).1) (hc.differentiableAt (by simp))
  rw [n07bMaterialChart_radiusChart hT y] at hd
  simpa only [n07bMaterialDirectionDrift, Function.comp_apply,
    n07bDirectionNormalizationDrift, n07bMaterialDirectionV1, n07bMaterialDirectionV2,
    n07bSourceMaterialJacobian] using
      congrArg (fun t : ℝ => -t /
        (2 * canonicalMaterialJacobian T K z m (n07bMaterialRadiusChart T y))) hd

/-- The actual reciprocal density uses the inverse-chart Jacobian. -/
theorem n04Realization_materialJacobian_inverse_eqOn
    (hgeom : CanonicalGeometry D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    EqOn (fun y => (canonicalMaterialJacobian T K z m (n07bMaterialRadiusChart T y))⁻¹)
      (fun y => (T.ell (T.radius y.1))⁻¹ *
        |planeJacobian (K.inverseChart z m) (K.chart z m (n07bMaterialRadiusChart T y))|)
      (n07bSourceMaterialPiece T K z m) := by
  intro y hy
  have hc := hgeom.charts z hz hs m
  have hj := n07a_actual_inverseChart_jacobian_abs hgeom hz hs m (hc.1 hy)
  rw [hc.2.2.1 _ hy] at hj
  change (T.ell (T.radius y.1) *
    |planeJacobian (K.chart z m) (n07bMaterialRadiusChart T y)|)⁻¹ = _
  rw [mul_inv_rev, hj, mul_comm]

/-- The source factor is evaluated at the current canonical point. -/
theorem n04Realization_materialSourceFactor_eqOn
    (hgeom : CanonicalGeometry D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    EqOn (fun y => K.height z m (n07bMaterialRadiusChart T y) /
        |planeJacobian (K.chart z m) (n07bMaterialRadiusChart T y)|)
      (fun y => canonicalSource S K z m (fun _ => 1)
        (K.chart z m (n07bMaterialRadiusChart T y)))
      (n07bSourceMaterialPiece T K z m) := by
  intro y hy
  simp only [canonicalSource, (hgeom.charts z hz hs m).2.2.1 _ hy, mul_one]

/-- The reciprocal height is the inverse source factor times the
Jacobian of the actual inverse chart, on the same material piece. -/
theorem n04Realization_materialHeightInverse_eqOn
    (hgeom : CanonicalGeometry D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    EqOn (fun y => (K.height z m (n07bMaterialRadiusChart T y))⁻¹)
      (fun y => (canonicalSource S K z m (fun _ => 1)
          (K.chart z m (n07bMaterialRadiusChart T y)))⁻¹ *
        |planeJacobian (K.inverseChart z m) (K.chart z m (n07bMaterialRadiusChart T y))|)
      (n07bSourceMaterialPiece T K z m) := by
  intro y hy
  have hc := hgeom.charts z hz hs m
  have hj := n07a_actual_inverseChart_jacobian_abs hgeom hz hs m (hc.1 hy)
  rw [hc.2.2.1 _ hy] at hj
  have hheight := (hc.2.2.2.2.2.2.2 _ hy).1.ne'
  have hdet := abs_ne_zero.mpr (hc.2.2.2.2.2.2.2 _ hy).2.1
  simp only [canonicalSource, hc.2.2.1 _ hy, mul_one, hj]
  field_simp [hheight, hdet]

/-- The reference source factor is already the stored canonical source
at the shared canonical coordinate. -/
theorem n04Realization_referenceSourceFactor_eq (m : ℕ) :
    canonicalReferenceSourceFactor C K z m =
      canonicalSource S K (C.referenceState, 0) m (fun _ => 1) ∘ K.chart z m := by
  funext x
  simp only [canonicalReferenceSourceFactor, canonicalReferencePoint,
    Function.comp_apply, canonicalSource, mul_one]

/-- The reference/current height ratio uses the same canonical point
and the genuine reference physical point. -/
theorem n04Realization_materialReferenceHeightRatio_eqOn
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    EqOn (canonicalReferenceHeightRatio C K z m ∘ n07bMaterialRadiusChart T)
      (fun y => canonicalSource S K (C.referenceState, 0) m (fun _ => 1)
          (K.chart z m (n07bMaterialRadiusChart T y)) *
        |planeJacobian (K.chart (C.referenceState, 0) m)
          (canonicalReferencePoint C K z m (n07bMaterialRadiusChart T y))| *
        (canonicalSource S K z m (fun _ => 1)
          (K.chart z m (n07bMaterialRadiusChart T y)))⁻¹ *
        |planeJacobian (K.inverseChart z m) (K.chart z m (n07bMaterialRadiusChart T y))|)
      (n07bSourceMaterialPiece T K z m) := by
  intro y hy
  have hc := hgeom.charts z hz hs m
  have hr := hgeom.charts (C.referenceState, 0) href hsref m
  have hx₀ := hr.2.1 (hc.1 hy)
  have hdet := abs_ne_zero.mpr (hr.2.2.2.2.2.2.2 _ hx₀).2.1
  have hheight : K.height (C.referenceState, 0) m
      (canonicalReferencePoint C K z m (n07bMaterialRadiusChart T y)) =
      canonicalSource S K (C.referenceState, 0) m (fun _ => 1)
          (K.chart z m (n07bMaterialRadiusChart T y)) *
        |planeJacobian (K.chart (C.referenceState, 0) m)
          (canonicalReferencePoint C K z m (n07bMaterialRadiusChart T y))| := by
    simp only [canonicalSource, canonicalReferencePoint, mul_one]
    exact (div_mul_cancel₀ _ hdet).symm
  change K.height (C.referenceState, 0) m
    (canonicalReferencePoint C K z m (n07bMaterialRadiusChart T y)) /
      K.height z m (n07bMaterialRadiusChart T y) = _
  rw [div_eq_mul_inv, hheight,
    n04Realization_materialHeightInverse_eqOn hgeom hz hs m y hy]
  ring

end ContinuousFlexibility.Analysis
