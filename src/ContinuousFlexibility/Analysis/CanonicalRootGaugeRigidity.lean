module

public import ContinuousFlexibility.Analysis.N03CanonicalRootAngles
public import ContinuousFlexibility.Analysis.CanonicalClosedSymmetry
public import ContinuousFlexibility.Analysis.TwoReturnBoundaryRigidity
public import ContinuousFlexibility.Analysis.N01TravelRigidity

/-!
# The existing canonical root gauges equal the actual N01 gauges

The actual N03 characteristic endpoints satisfy both return laws. The
true closed canonical boundary lifts are continuous, degree one, and
zero at the reflection axis. Irrationality of the actual reference travel
therefore fixes both gauges and the canonical Airy width.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem canonicalCutPair_rootAngle_zero
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) :
    (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1)
      (if side then C.right m else C.left m, 0)).2 = 0 := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  have hp := (canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m side 0).1
  have hclosed := hA.boundary z hz hs i
  apply (canonicalInverse_zero_axis_iff hA hz hs i (hclosed.1 hp)).mp
  rw [hclosed.2.2.1 (c, 0) hp]

/-- Both boundary angle maps and the Airy travel width are forced by the
existing N01/N02/N03 construction, on its original common neighborhood. -/
theorem canonicalRootGauges_eq_n01_of_n03
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    2 * airyTravelPrimitive (K.cutRadius m) = C.travel m ∧
      (∀ θ, (K.chart z (K.cutPair m).1 (C.left m, θ)).2 = stateLeftChart S z.1 m θ) ∧
      ∀ θ, (K.chart z (K.cutPair m).2 (C.right m, θ)).2 = rightChartCandidate S C z m θ := by
  have hleft (θ : ℝ) := hN01.2.2.2.2.2.2.2.1 z hz hs m θ
  have hroot (θ : ℝ) := canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m false θ
  have hboundary := canonicalBoundaryAngular_bijective hA hz hs (K.cutPair m).1
    (fun θ => (hroot θ).1) (fun θ => (hroot θ).2)
  have hlzero : stateLeftChart S z.1 m 0 = 0 := by
    have hodd := (hleft 0).2.2.2
    simp only [neg_zero] at hodd
    linarith only [hodd]
  have hrinj : Function.Injective (rightChartCandidate S C z m) :=
    (strictMono_of_deriv_pos (f := rightChartCandidate S C z m)
      (fun θ => (hN02.1 z hz hs m θ).2.2.2.2)).injective
  apply boundaryLifts_eq_of_two_irrational_returns (c := (1 / 2 : ℝ))
    (Pminus := fun θ => L.minusFlow z m (C.right m) θ)
    (Pplus := fun θ => -L.minusFlow z m (C.right m) (-θ))
    (by norm_num) (fun θ => (hleft θ).1) (fun θ => (hleft θ).2.2.1) hlzero hrinj
    hboundary.1.continuous hboundary.2.2.2
    (canonicalCutPair_rootAngle_zero hA hB hz hs m false)
  · intro θ
    have hflows := hN03.2.2.2.2.1 z hz hs m θ
    exact ⟨hflows.2.2.2.1, hflows.2.2.2.2⟩
  · exact canonicalRootAngles_of_n03Flows hS hT hN01 hN03 hA hB hz hs m
  · exact n01_double_travel_div_pi_irrational hN01 m

end ContinuousFlexibility.Analysis
