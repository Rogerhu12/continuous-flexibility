import ContinuousFlexibility.Analysis.N06ReferenceModalPullback

/-!
# Physical transmission of the original canonical modal representatives

The modes are those of the chosen N05 graph element. Their physical
reconstructions represent the same Fourier coefficients of its actual
remainder, so their interface jets match by the original weak graph.
No extra matching condition is imposed on the canonical domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Adjacent canonical modes have the actual matching physical jets.
The regularity assumptions concern the two chosen modal representatives,
not an additional domain condition or a separately chosen physical field. -/
theorem n06N05_canonicalModes_physical_traces
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (u : B.Space) (ml mr n : ℕ) (vl vr : ℝ → ℝ)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hcore : Icc (K.physicalLeft ml) (K.physicalRight mr) ⊆ radialCore D)
    (hvl : ContDiff ℝ 1 (fun r => K.height (C.referenceState, 0) ml (r, 0) *
      vl ((K.chart (C.referenceState, 0) ml (r, 0)).1)))
    (hvr : ContDiff ℝ 1 (fun r => K.height (C.referenceState, 0) mr (r, 0) *
      vr ((K.chart (C.referenceState, 0) mr (r, 0)).1)))
    (hmodeL : n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[volume.restrict (Ioo (K.left ml) (K.right ml))] vl)
    (hmodeR : n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr) :
    let fl : ℝ → ℝ := fun r => K.height (C.referenceState, 0) ml (r, 0) *
      vl ((K.chart (C.referenceState, 0) ml (r, 0)).1)
    let fr : ℝ → ℝ := fun r => K.height (C.referenceState, 0) mr (r, 0) *
      vr ((K.chart (C.referenceState, 0) mr (r, 0)).1)
    fl (K.physicalRight ml) = fr (K.physicalRight ml) ∧
      deriv fl (K.physicalRight ml) = deriv fr (K.physicalRight ml) ∧
      D.w (K.physicalRight ml) * deriv fl (K.physicalRight ml) =
        D.w (K.physicalRight ml) * deriv fr (K.physicalRight ml) := by
  obtain ⟨η, f, hrep, hgraph, htrace⟩ := n06N05_exists_remainder_modal_traces hS h u
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hη : MemLp η 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp h01.1.1 h01.1.2.2.2.1 h.2.2.2.1 hgraph.1
  have hχ : MemLp (fun p : PolarPoint => u.val.1.2.1 * S.chiLeft p.1) 2
      (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (continuous_const.mul (hS.2.2.1.1.continuous.comp continuous_fst))
  have hrem : MemLp (n06ReferenceRemainder S.chiLeft η u.val.1.2.1) 2
      (radialPhysicalMeasure D) := hη.sub hχ
  obtain ⟨a, ha⟩ := hgraph.1
  have hp : Function.Periodic (n06ReferenceRemainder S.chiLeft η u.val.1.2.1)
      (0, Real.pi) := n06_referenceRemainder_periodic ha.2.2.1 _
  have hL := n06_controlledReference_modal_representation h.1 hcoordinates
    hrem hp ml n (hrep.1 ml) hmodeL
  have hR := n06_controlledReference_modal_representation h.1 hcoordinates
    hrem hp mr n (hrep.1 mr) hmodeR
  rw [← hjoin] at hR
  have hright : K.physicalRight ml < K.physicalRight mr :=
    hjoin.trans_lt (h04.1.referenceBounds mr).1
  exact htrace n (K.physicalLeft ml) (K.physicalRight ml) (K.physicalRight mr)
    (h04.1.referenceBounds ml).1 hright hcore _ _ hvl hvr hL hR

end ContinuousFlexibility.Statements
