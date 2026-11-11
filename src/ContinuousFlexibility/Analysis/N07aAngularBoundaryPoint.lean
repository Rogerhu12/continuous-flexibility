import ContinuousFlexibility.Analysis.N07aAngularAlignedInverse
import ContinuousFlexibility.Analysis.N07aAngularBoundaryEquivariance
import ContinuousFlexibility.Analysis.N07aReferenceReturn

/-!
# The common physical boundary point of the actual transports

Reference coordinates preserve the angle. The current boundary angular
map is onto by its actual period equivariance. Therefore the two adjacent
reference boundary images have the same actual current physical preimage.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {i j : ℕ}

theorem n07a_interface_common_preimage
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceRadial S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (d : N07aInterfaceJetData S C K base ε i j) (θ : ℝ) :
    ∃ α : ℝ,
      K.chart z i (K.physicalRight i, α) =
        K.chart (C.referenceState, 0) i (K.physicalRight i, θ) ∧
      K.chart z j (K.physicalRight i, α) =
        K.chart (C.referenceState, 0) j (K.physicalRight i, θ) := by
  have hci : K.physicalRight i ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
    ⟨(h04.2.2.2.1 i).1.le, le_rfl⟩
  obtain ⟨α, hα⟩ := n07a_boundary_chart_angle_surjective h04 hz hs i hci θ
  refine ⟨α, ?_, ?_⟩
  all_goals
    have hc := d.jets z (Or.inr ⟨hz, hs⟩) α
    have hr := d.jets (C.referenceState, 0) (Or.inl rfl) θ
    have hθ : (K.chart (C.referenceState, 0) i (K.physicalRight i, θ)).2 = θ := by
      have h := n07a_reference_chart_radial_closed h04 href
        (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector i
        (p := (K.physicalRight i, θ)) hci
      exact congrArg Prod.snd h
    have he : endpointAlignedChart K z i d.endpointLeft d.orientationLeft
          (K.physicalRight i, α) =
        endpointAlignedChart K (C.referenceState, 0) i d.endpointLeft d.orientationLeft
          (K.physicalRight i, θ) :=
      Prod.ext (hc.1.trans hr.1.symm) (hα.trans hθ.symm)
  · exact n07a_endpointAlignedChart_injective d.orientationLeft_ne he
  · exact n07a_endpointAlignedChart_injective d.orientationRight_ne
      (hc.2.1.symm.trans (he.trans hr.2.1))

theorem n07a_interface_derivative_alignments
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hboundary : K.physicalRight i = K.physicalLeft j)
    (d : N07aInterfaceJetData S C K base ε i j) (θ : ℝ) :
    (n07aNormalAlignment d.orientationLeft).comp
        (fderiv ℝ (K.chart z i) (K.physicalRight i, θ)) =
      (n07aNormalAlignment d.orientationRight).comp
        (fderiv ℝ (K.chart z j) (K.physicalRight i, θ)) := by
  have hci : K.physicalRight i ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
    ⟨(h04.2.2.2.1 i).1.le, le_rfl⟩
  have hcj : K.physicalRight i ∈ Icc (K.physicalLeft j) (K.physicalRight j) := by
    rw [hboundary]
    exact ⟨le_rfl, (h04.2.2.2.1 j).1.le⟩
  have hi := (h04.2.2.2.2.2.2.2.2.1 z hz hs i (K.physicalRight i, θ) hci).1
  have hj := (h04.2.2.2.2.2.2.2.2.1 z hz hs j (K.physicalRight i, θ) hcj).1
  have hei := n07a_endpointAlignedChart_hasFDerivAt (hi.differentiableAt (by simp))
    d.endpointLeft d.orientationLeft
  have hej := n07a_endpointAlignedChart_hasFDerivAt (hj.differentiableAt (by simp))
    d.endpointRight d.orientationRight
  have h := (d.jets z (Or.inr ⟨hz, hs⟩) θ).2.2.1
  rwa [hei.fderiv, hej.fderiv] at h

end ContinuousFlexibility.Analysis
