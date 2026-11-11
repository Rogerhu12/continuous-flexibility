import ContinuousFlexibility.Analysis.N06ReferencePhysicalCoefficients
import ContinuousFlexibility.Analysis.N06ReferenceRemainderFields
import ContinuousFlexibility.Analysis.N06CanonicalTestOperator
import ContinuousFlexibility.Analysis.N06CubicDifferential

/-!
# The reference physical operator on transported tests

On a positive physical piece, the actual N03 correction has the radial
reference coefficient germs. Outside that piece the transported compact
test and its differential expression vanish. The resulting equality is
an equality of the actual global functions, so the original reference
graph equation, integrability, and periodicity transfer together.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

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
  obtain ⟨J, hJ, hJsub, hJzero⟩ :=
    n06CanonicalTestPullback_radialSupport hA hz hs hφ
  funext p
  by_cases hp : p ∈ physicalPieceOpen S K m
  · have hcore : p.1 ∈ radialCore D := (hA.2.2.2.1 m).2.2 hp.1
    have hr : p.1 ≠ 0 := (hgeom.1.trans hcore.1).ne'
    obtain ⟨ha, hb, hc⟩ := n06_correctedReference_positivePiece_germ
      hN03 hA hw href hz hs m hm hp
    let A0 : SymmetricCoefficients :=
      ⟨fun q => D.w q.1, fun _ => 0, fun q => deriv D.w q.1 / q.1⟩
    calc
      _ = divergenceOperator A0
          (n06CanonicalTestPullback S K (C.referenceState, 0) m φ) p :=
        n06_divergenceOperator_congr_germ _ ha hb hc
      _ = _ := by
        exact Radial.reference_divergence_eq_radialPDE hw hΦ hr
  · rw [n06CanonicalTestPullback_divergence_zero_of_not_mem hA hz hs hφ _ hp]
    have hpJ : p.1 ∉ J := by
      intro h
      exact hp ⟨hJsub h, mem_univ _⟩
    exact (Radial.r11b_radialPDE_test_zero_outside hgeom hΦ hJ.isClosed
      hJzero hpJ p.2).symm

end ContinuousFlexibility.Analysis
