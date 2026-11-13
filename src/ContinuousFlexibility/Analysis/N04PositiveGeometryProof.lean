import ContinuousFlexibility.Analysis.N04PositiveGeometryCommonNeighborhood
import ContinuousFlexibility.Analysis.N04PositiveGeometryActualTransportSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryActualCoordinatesCurrentData
import ContinuousFlexibility.Analysis.N04PositiveGeometryActualPhysicalHeightCurrentData
import ContinuousFlexibility.Analysis.N04PositiveGeometryActualPulledHeightCurrentData
import ContinuousFlexibility.Analysis.N04PositiveGeometryUniformCollector

/-!
# The positive geometry obligation

The controlled construction chooses its buffer before the state. Its
actual factor towers and quantitative prefixes produce the four
coordinate atoms, the physical height and the pulled height. The
collector then supplies all eight geometry atoms on one neighborhood,
uniformly in the auxiliary column.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

/-- Every selected controlled family supplies all positive geometry
data on a smaller neighborhood. No transport estimate or reference-jet
certificate is added to the hypotheses. -/
theorem N04PositiveGeometryControlledFamily.positiveGeometryData
    {W : N04RealizationStart} {X : N04RealizationChoice W}
    (F : N04PositiveGeometryControlledFamily W X 3)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H) :
    ∃ b : ℕ, F.base ≤ b ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ F.ε ∧ ε ≤ 1 / 2 ∧
      ∀ η : (W.S.height (3 / 4 : ℝ)).Space,
        (F.gauge e Y H).GeometryData η ((F.gauge e Y H).Pos η) b ε := by
  classical
  obtain ⟨base, ε, hb, hε, hεW, hεhalf, hFb, hFε, hflow, hctx, hfactors⟩ :=
    n04PositiveGeometry_controlled_common_factor_context F le_rfl
  have hεone : ε ≤ 1 := hεhalf.trans (by norm_num)
  let factors : ∀ i, N04PositiveGeometryFactorData F base ε i :=
    fun i => Classical.choice (hfactors i)
  let JT := fun i => (factors i).transport
  let JS := fun i => (factors i).inverseTransport
  have htransport := n04PositiveGeometry_actualControlledTransport_sample_prefix
    F hb hε hεW hεone hFb hFε hflow hctx factors
  have hC := n04PositiveGeometry_actualControlledCoordinates_currentData_of_transportWords
    F e Y H href hmaterial hε hFb hFε JT JS (htransport false) (htransport true)
  have hH := n04PositiveGeometry_actualControlledPhysicalHeight_currentData_of_inverseWords
    F e Y H href hmaterial hb hε hεW hεone hFb hFε hflow hctx JS (htransport true)
  have hP := n04PositiveGeometry_actualControlledPulledHeight_currentData
    F e Y H href hmaterial hb hε hεW hεone hFb hFε hflow hctx
  have hA : (F.gauge e Y H).Admissible base ε :=
    (F.gauge e Y H).admissible_mono (F.gauge_admissible e Y H href) hFb hε hFε
  obtain ⟨b, hbase, δ, hδ, hδε, hδhalf, hgeometry⟩ :=
    (F.gauge e Y H).positiveGeometryData_of_uniform_coordinates_height
      hA hmaterial hC hH hP
  exact ⟨b, hFb.trans hbase, δ, hδ, hδε.trans hFε, hδhalf, hgeometry⟩

/-- The corrected positive subnode chooses its normalization buffer and
retains the original whole-atlas geometry interface. -/
theorem n04Realization_positiveGeometry : N04RealizationPositiveGeometryObligation := by
  classical
  intro W X Y H href hmaterial e
  let F : N04PositiveGeometryControlledFamily W X 3 :=
    Classical.choice (n04PositiveGeometry_controlledFamily_nonempty W X 3)
  obtain ⟨b, hb, ε, hε, hεF, _, hgeometry⟩ :=
    F.positiveGeometryData e Y H href hmaterial
  refine ⟨F.buffer, b, ε,
    F.toN04PositiveGeometryControlData.lower, F.toN04PositiveGeometryControlData.upper,
    F.toN04PositiveGeometryControlData.τ, F.toN04PositiveGeometryControlData.σ,
    F.toN04PositiveGeometryControlData.Q,
    F.base_le.trans hb, hε, hεF.trans F.radius_le, ?_, F.reference, hgeometry⟩
  intro z hz hs i
  exact F.matching z (stateNeighborhood_mono W.S W.C hb hεF hz) hs i

end ContinuousFlexibility.Analysis
