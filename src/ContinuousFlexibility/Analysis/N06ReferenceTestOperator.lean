module

public import ContinuousFlexibility.Analysis.N06ReferencePhysicalCoefficients
public import ContinuousFlexibility.Analysis.N06ReferenceRemainderFields
public import ContinuousFlexibility.Analysis.N06CanonicalTestOperator
public import ContinuousFlexibility.Analysis.N06CubicDifferential

/-!
# The reference physical operator on transported tests

On a positive physical piece, the actual N03 correction has the radial
reference coefficient germs. Outside that piece the transported compact
test and its differential expression vanish. The resulting equality is
an equality of the actual global functions, so the original reference
graph equation, integrability, and periodicity transfer together.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- The true radial differential expression vanishes on a zero input
germ, including points on the boundary of a nonradial physical piece. -/
theorem n06_referenceTestOperator_zero_of_germ
    {D : ReferenceData} {φ : PolarPoint → ℝ} {p : PolarPoint}
    (hw : DifferentiableAt ℝ D.w p.1) (hφ : ContDiff ℝ ∞ φ)
    (hzero : φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ)) :
    n06ReferenceTestOperator D φ p = 0 := by
  have hr : radialPartial φ =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    filter_upwards [hzero.fderiv (𝕜 := ℝ)] with q hq
    simp [radialPartial, hq]
  have ht : angularPartial φ =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    filter_upwards [hzero.fderiv (𝕜 := ℝ)] with q hq
    simp [angularPartial, hq]
  have hrr : radialPartial (radialPartial φ) p = 0 := by
    simp [radialPartial, hr.fderiv_eq (𝕜 := ℝ)]
  have htt : angularPartial (angularPartial φ) p = 0 := by
    simp [angularPartial, ht.fderiv_eq (𝕜 := ℝ)]
  change Radial.radialPDE D.w (fun r θ => φ (r, θ)) p.1 p.2 = 0
  rw [Radial.radialPDE_eq_polar_jets hw hφ, hr.eq_of_nhds, hrr, htt]
  simp only [mul_zero, add_zero]

theorem n06CanonicalTestPullback_reference_operator
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base m : ℕ} {ε : ℝ} {φ : PolarPoint → ℝ}
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε)
    (hgeom : RadialProfileGeometry D)
    (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState)
    (hm : K.positive m = true) (hφ : CanonicalTest S K m φ) :
    divergenceOperator (L.coefficients (C.referenceState, 0))
        (n06CanonicalTestPullback S K (C.referenceState, 0) m φ) =
      n06ReferenceTestOperator D
        (n06CanonicalTestPullback S K (C.referenceState, 0) m φ) := by
  have hΦ := n06CanonicalTestPullback_contDiff hA hz hs hφ
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  funext p
  by_cases hp : p ∈ physicalPieceOpen S K (C.referenceState, 0) m
  · have hpref : p ∈ referencePhysicalPieceOpen S K m := by
      simpa only [hA.referenceDomain m] using hp
    have hcore : p.1 ∈ radialCore D := (hA.referenceBounds m).2.2 hpref.1
    have hr : p.1 ≠ 0 := (hgeom.1.trans hcore.1).ne'
    obtain ⟨ha, hb, hc⟩ := n06_correctedReference_positivePiece_germ
      hN03 hA hw href hz hs m hm hpref
    let A0 : SymmetricCoefficients :=
      ⟨fun q => D.w q.1, fun _ => 0, fun q => deriv D.w q.1 / q.1⟩
    calc
      _ = divergenceOperator A0
          (n06CanonicalTestPullback S K (C.referenceState, 0) m φ) p :=
        n06_divergenceOperator_congr_germ _ ha hb hc
      _ = _ := by
        exact Radial.reference_divergence_eq_radialPDE hw hΦ hr
  · rw [n06CanonicalTestPullback_divergence_zero_of_not_mem hA hz hs hφ _ hp]
    exact (n06_referenceTestOperator_zero_of_germ
      (hw.differentiable (by simp) p.1) hΦ
      (n06CanonicalTestPullback_eventually_zero_of_not_mem hA hz hs hφ hp)).symm

end ContinuousFlexibility.Analysis
