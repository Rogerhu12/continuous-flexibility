import ContinuousFlexibility.Analysis.N04RealizationActualRootRelativeJets
import ContinuousFlexibility.Analysis.N06BoundaryRadialJets

/-!
# Actual relative-coordinate radial traces

The finite ordinary jets are projected onto the requested coordinate and
identified with the original radialBoundaryJet. The equality uses the
stored closed-chart smoothness at the same point, without a parameter
family of chosen root extensions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04ActualRelativeTraceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04Realization_actualRoot_relativeRadialDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    (hK : K = n04bActualTypedAtlas hT hS hN hfield e)
    (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side))
    (N : ℕ)
    (Jraw : ∀ j, 1 ≤ j → j ≤ N → ∀ w : Fin j → Fin 2,
      SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
        (fun p : (StateDirections S × ℝ) × ℝ =>
          iteratedFDeriv ℝ j (K.chart (liftSectorParameter S C p.1) k)
            (if side then C.right m else C.left m, p.2)
            (fun i => cylinderBasisVector (w i))))
    (n : ℕ) (hNn : n ≤ N) (π : PolarPoint →L[ℝ] ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        radialBoundaryJet (fun q =>
          π (canonicalCurrentPoint C K (liftSectorParameter S C p.1) k q))
          (if side then C.right m else C.left m) n p.2) := by
  let c : ℝ := if side then C.right m else C.left m
  let JR := n04Realization_actualRoot_relativeJet_directions hT hS hN hfield e hK
    k m side hi N Jraw n hNn (fun _ => (1, 0))
  let J := solveSmoothDirectionsPostcomp JR π
  have hA : CanonicalGeometry D S C K base ε := by
    simpa only [hK] using n04b_actualTypedAtlas_partA hT hS hN hfield e
  have href := n04b_reference_valid_of_through03 hN
  refine J.congr (fun p hp => ?_)
  have hroot : (c, p.2) ∈ physicalPieceClosed S K (C.referenceState, 0) k := by
    rw [hK]
    exact (n04Realization_actualRoot_chart_data hT hS hN hfield e
      href.1 href.2 k m side hi p.2).1
  have hs : ContDiffAt ℝ ∞
      (canonicalCurrentPoint C K (liftSectorParameter S C p.1) k) (c, p.2) :=
    n04Coordinates_currentPoint_contDiffAt_closed hA href.1 href.2
      (liftSectorParameter_mem_stateNeighborhood hp.1 le_rfl)
      (hN.1.1.2.2.1.liftSectorParameter_sector p.1) k hroot
  have hscalar : ContDiffAt ℝ ∞
      (fun q => π (canonicalCurrentPoint C K (liftSectorParameter S C p.1) k q))
      (c, p.2) := π.contDiff.contDiffAt.comp (c, p.2) hs
  have he : radialBoundaryJet
      (fun q => π (canonicalCurrentPoint C K (liftSectorParameter S C p.1) k q))
      c n p.2 =
      π (iteratedFDeriv ℝ n (canonicalCurrentPoint C K
        (liftSectorParameter S C p.1) k) (c, p.2) (fun _ => (1, 0))) := by
    rw [n06_radialBoundaryJet_eq_frechet n hscalar]
    have hjet := congrArg (fun A : PolarPoint [×n]→L[ℝ] ℝ => A (fun _ => (1, 0)))
      (π.iteratedFDeriv_comp_left hs (by simp : (n : ℕ∞ω) ≤ ∞))
    simpa only [Function.comp_def, ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply] using hjet
  exact he.symm

end ContinuousFlexibility.Analysis
