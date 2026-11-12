import ContinuousFlexibility.Analysis.N07aAngularCandidateCoordinates
import ContinuousFlexibility.Analysis.N07aPhysicalPieceBound
import ContinuousFlexibility.Analysis.N07bAtlasAEPullback
import ContinuousFlexibility.Analysis.N07aAngularInnerIntervals

/-!
# The actual canonical height coordinates determine the physical height

The smooth canonical transform agrees almost everywhere with zero, so it
vanishes throughout the open strip. The actual inverse chart and positive
height recover the physical function on each piece. Original null-set
coverage and continuity then recover every interface as well.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_height_eq_zero_of_canonical
    (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : (S.height (3 / 4 : ℝ)).Space)
    (hU : ∀ m, canonicalHeight S K z m ((S.height (3 / 4 : ℝ)).decode u)
      =ᵐ[canonicalMeasure S K m] fun _ => 0) : u = 0 := by
  have hd := (hS.1 (3 / 4 : ℝ)).2.2.2.1 u
  let J := n07aRadialIntervalData K D.a D.b
  have hglobal : ((S.height (3 / 4 : ℝ)).decode u) =ᵐ[canonicalMeasure S J 0]
      fun _ => (0 : ℝ) := by
    apply (n07b_canonicalHeights_ae_iff h04.1 hz hs
      ((S.height (3 / 4 : ℝ)).decode u) (fun _ => 0)).mp
    intro m
    simpa only [canonicalHeight, zero_div] using hU m
  have he : EqOn ((S.height (3 / 4 : ℝ)).decode u) (fun _ => 0) (annularOpen D) :=
    n07a_canonical_periodicOn_eqOn_of_ae_eq (S := S) (K := J) (m := 0)
      hd.1.continuousOn continuousOn_const
      (fun p _ => hd.2.2.1 p) (fun _ _ => rfl) hglobal
  apply (hS.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext p
  rw [map_zero, Pi.zero_apply]
  by_cases hp : p ∈ annularOpen D
  · exact he hp
  · exact hd.2.2.2.1 p hp

end ContinuousFlexibility.Analysis
