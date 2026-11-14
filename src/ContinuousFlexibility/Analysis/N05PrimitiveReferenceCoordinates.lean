module

public import ContinuousFlexibility.Analysis.N05ReferenceInterface
public import ContinuousFlexibility.Analysis.N05PrimitiveReferenceFirstBounds
public import ContinuousFlexibility.Analysis.N05PrimitiveReferenceFibers
public import Lean.Util.CollectAxioms

/-!
# Controlled reference coordinates from explicit reference jets

The cubic endpoint window, finite label fibers, and five first coordinate
bounds are assembled with one common positive coefficient and exponent.
All estimates concern the same supplied charts, heights, physical intervals,
and labels. The reference radiality and jet certificates remain explicit
hypotheses; no full nonlinear witness is changed or strengthened here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- Explicit reference radiality and primitive jets give the complete
controlled-coordinate specification on the original canonical data. -/
theorem n05_controlledReferenceCoordinates_of_referenceJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hradial : CanonicalGeometry.ReferenceRadial S C K)
    (hjets : CanonicalGeometry.ReferenceJets D T S C L K) :
    N05ControlledReferenceCoordinates D S C K := by
  have hreferenceRadial : ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      K.chart (C.referenceState, 0) m p =
        ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2) ∧
      K.height (C.referenceState, 0) m p =
        K.height (C.referenceState, 0) m (p.1, 0) := by
    intro m
    simpa only [h04.1.referenceDomain m] using hradial.1 m
  obtain ⟨A, hA, hwindow⟩ := n05_reference_primitive_cubic_window hD hT h04 hjets
  obtain ⟨F, hF, hfibers⟩ := n05_reference_primitive_piece_fibers hD hT h04 hjets
  obtain ⟨G, hG, hfirst⟩ :=
    n05_reference_primitive_first_bounds hD hT h01 h04 hradial hjets
  let B : ℝ := A + F + G + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hAB : A ≤ B := by dsimp only [B]; linarith only [hF, hG]
  have hFB : F ≤ B := by dsimp only [B]; linarith only [hA, hG]
  have hGB : G ≤ B := by dsimp only [B]; linarith only [hA, hF]
  have henvelope (J : ℝ) (hJB : J ≤ B) (n : ℕ) :
      J * radialE n ^ J ≤ B * radialE n ^ B := by
    have hE : 1 ≤ radialE n := Real.one_le_exp (Radial.radialQ_nonneg n)
    exact mul_le_mul hJB (Real.rpow_le_rpow_of_exponent_le hE hJB)
      (Real.rpow_nonneg (Real.exp_pos _).le _) hB.le
  refine ⟨hreferenceRadial, B, hB, ?_, ?_, ?_⟩
  · intro m r hr
    have hrCore : r ∈ radialCore D := (h04.1.referenceBounds m).2.2 hr
    obtain ⟨j, hrj⟩ := hD.choose_spec.2.1.exists_cell hrCore
    refine ⟨j, hrj, (hwindow m j r hr hrj).trans ?_⟩
    exact mul_le_mul_of_nonneg_right hAB
      (add_nonneg (Radial.radialQ_nonneg _) zero_le_one)
  · intro n
    exact ⟨(hfibers n).1, (hfibers n).2.trans (henvelope F hFB n)⟩
  · intro m r hr
    exact (hfirst m r hr).trans (henvelope G hGB (D.cellIndex (K.cell m)))


end ContinuousFlexibility.Statements

open Lean in
run_cmd do
  let axioms ← collectAxioms
    ``ContinuousFlexibility.Statements.n05_controlledReferenceCoordinates_of_referenceJets
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in n05_controlledReferenceCoordinates_of_referenceJets"
