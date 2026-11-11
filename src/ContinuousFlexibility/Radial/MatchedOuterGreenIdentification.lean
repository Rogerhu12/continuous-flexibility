import ContinuousFlexibility.Radial.MatchedOuterPhysicalFlux
import ContinuousFlexibility.Radial.MatchedOuterSeparatedInverse
import ContinuousFlexibility.Radial.MatchedOuterTraceTransport
import ContinuousFlexibility.Radial.MatchedModeSeparatedTests
import ContinuousFlexibility.Radial.MatchedPiecesAssembly

/-!
# Identifying the retained exterior inverse with its actual Green operator

The supplied whole-tail operators are used unchanged. Their proved
all-source kernels give the physical weak equation, the one-sided
representatives and the actual Robin rows. The existing frozen
realization's uniqueness then identifies its stored exterior inverse
with that same pair of Green operators.

Only equality of the Robin lines is needed: normalizing the natural
state with the opposite orientation does not change the conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

section

variable {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
  (M : RadialMatchingData D)
  (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
  (hb : M.innerRight < D.b) (hlam : ∀ i, 0 < M.boundaryScale i)

local notation "cut" => (fun side : Bool => if side then M.innerRight else M.innerLeft)
local notation "idx" => (fun side : Bool => if side then (1 : Fin 2) else 0)

variable {c : Bool → ℝ} {P ZP Q ZQ : Bool → ℝ → ℝ}
  (H : ∀ side : Bool, OuterFundamentalStatePair
    (fun x => M.boundaryScale (idx side) / outerTailOutwardWeight D side x)
    (fun x => (M.frequency : ℝ) ^ 2 * deriv (outerTailOutwardWeight D side) x /
      (M.boundaryScale (idx side) * x))
    (P side) (ZP side) (Q side) (ZQ side)
    (outerOutwardRadius side (cut side)) (c side)
    (outerOutwardRadius side (tailPhysicalEndpoint D side)))
  (hV : ∀ side, MemLp (H side).V 2 (outerWholeMeasure D side (cut side)))
  (R : ∀ side, OuterWholeL2 D side (cut side) →L[ℝ]
    OuterWholeL2 D side (cut side))
  (hR : ∀ side (f : OuterWholeL2 D side (cut side)),
    (R side f : ℝ → ℝ) =ᵐ[outerWholeMeasure D side (cut side)] fun x =>
      ∫ y, outerGreenKernel (M.boundaryScale (idx side))
        (H side).U (H side).V x y * f y ∂outerWholeMeasure D side (cut side))
  (hline : ∀ side (q : ℝ × ℝ),
    outerStatePair (H side).entrance q = 0 ↔
      outerStatePair (M.A (idx side) (idx side), M.B (idx side) (idx side)) q = 0)

include hD hB ha hm hb hlam H hV R hR hline

/-- The actual pair of supplied whole Green operators satisfies the
original separated graph for every Hilbert source. -/
theorem matchedOuterSeparatedGreen_graph (F : RadialModePair D) :
    ModeOuterSeparatedGraph D M (matchedOuterSeparatedInverse D cut R F) F := by
  classical
  have hcut (side : Bool) : cut side ∈ radialCore D := by
    cases side
    · exact ⟨ha, hm.trans hb⟩
    · exact ⟨ha.trans hm, hb⟩
  have hdata (side : Bool) := matchedOuterWhole_representative hD
    (hcut side) (hlam (idx side)) (H side) (hV side) (R side) (hR side)
    (matchedOuterWholeRestrict D side (cut side) F.1)
  choose u hu hc hw hRobin using hdata
  let v := matchedOuterSideGlue M.innerLeft M.innerRight
    (fun r => u false (outerOutwardRadius false r))
    (fun r => u true (outerOutwardRadius true r))
  let G := matchedOuterSeparatedInverse D cut R
  have hrep : ((G F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] v :=
    matchedOuterSeparatedInverse_representative hD cut hm R F hu
  have hscalar : (G F).2 = 0 := matchedOuterSeparatedInverse_scalar D cut R F
  have hreg : ContDiffOn ℝ 1 v (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) :=
    matchedOuterSideGlue_contDiffOn hm
      (matchedOuterWhole_contDiff_physical (hc false))
      (matchedOuterWhole_contDiff_physical (hc true))
  have hve (side : Bool) : EqOn v
      (fun r => u side (outerOutwardRadius side r))
      (if side then Ico M.innerRight D.b else Ioc D.a M.innerLeft) := by
    cases side
    · intro r hr
      exact matchedOuterSideGlue_of_le _ _ hr.2
    · intro r hr
      exact matchedOuterSideGlue_of_ge hm _ _ hr.1
  have hrepSide (side : Bool) :
      ((G F).1 : ℝ → ℝ) =ᵐ[
        (radialHilbertMeasure D).restrict (radialTailInterval D side (cut side))]
        fun r => u side (outerOutwardRadius side r) := by
    filter_upwards [ae_restrict_of_ae hrep,
      ae_restrict_mem (show MeasurableSet (radialTailInterval D side (cut side)) by
        cases side <;> exact measurableSet_Ioo)] with r hr hi
    rw [hr]
    cases side
    · exact hve false (Ioo_subset_Ioc_self hi)
    · exact hve true (Ioo_subset_Ico_self hi)
  have heqSide (side : Bool) :
      ModeLocalEquation D M.frequency (radialTailInterval D side (cut side)) (G F) F :=
    matchedOuterWhole_modeLocalEquation hD hB (hcut side) hscalar (hrepSide side)
      (matchedOuterWholeRestrict_ae D side (cut side) F.1) (hc side) (hw side)
  have heq : ModeLocalEquation D M.frequency (matchingOuterRegion D M) (G F) F :=
    modeLocalEquation_matchingOuter_of_sides hD hB hm (heqSide false) (heqSide true)
  refine ⟨heq, hscalar, v, hrep, hreg, ?_, ?_⟩
  · intro r hr
    exact matchedOuterSideGlue_inner _ _ hr
  · have hboundary (side : Bool) :
        M.A (idx side) (idx side) * Real.sqrt (M.boundaryScale (idx side)) *
            v (matchingCut D M (idx side)) +
          M.B (idx side) (idx side) * matchingOuterFlux D M v (idx side) = 0 := by
      have hmap : MapsTo (outerOutwardRadius side)
          (Ico (outerOutwardRadius side (cut side))
            (outerOutwardRadius side (tailPhysicalEndpoint D side)))
          (if side then Ico M.innerRight D.b else Ioc D.a M.innerLeft) := by
        intro x hx
        cases side
        · change -M.innerLeft ≤ x ∧ x < -D.a at hx
          change D.a < -x ∧ -x ≤ M.innerLeft
          constructor <;> linarith [hx.1, hx.2]
        · exact hx
      have hveOut : EqOn (fun x => v (outerOutwardRadius side x)) (u side)
          (Ico (outerOutwardRadius side (cut side))
            (outerOutwardRadius side (tailPhysicalEndpoint D side))) := by
        intro x hx
        simpa only [outerOutwardRadius_twice] using hve side (hmap hx)
      have hentry : outerOutwardRadius side (cut side) ∈
          Ico (outerOutwardRadius side (cut side))
            (outerOutwardRadius side (tailPhysicalEndpoint D side)) :=
        ⟨le_rfl, outerWhole_interval (hcut side)⟩
      have hvalue : v (cut side) = u side (outerOutwardRadius side (cut side)) := by
        simpa only [outerOutwardRadius_twice] using hveOut hentry
      have hderiv := derivWithin_congr hveOut (hveOut hentry)
      have hweight : D.w (cut side) =
          outerTailOutwardWeight D side (outerOutwardRadius side (cut side)) := by
        cases side <;> simp only [outerTailOutwardWeight, outerTailSign,
          outerOutwardRadius, Bool.false_eq_true, ite_false, ite_true,
          neg_one_mul, one_mul, neg_neg]
      apply (matchedOuter_boundary_outward_iff ha hm hb side v (hlam (idx side))).mpr
      rw [hvalue, hderiv, hweight]
      exact (hline side _).mp (hRobin side)
    intro i
    fin_cases i
    · exact hboundary false
    · exact hboundary true

/-- The existing retained supplier's exterior inverse is the same
quantified Green operator; no replacement matching datum is introduced. -/
theorem matchedOuterInverse_eq_separatedGreen
    (hM : MatchingOuterRealizations D M) :
    M.outerInverse = matchedOuterSeparatedInverse D cut R := by
  apply ContinuousLinearMap.ext
  intro F
  exact hM.2.1 _ F
    (matchedOuterSeparatedGreen_graph hD hB M ha hm hb hlam H hV R hR hline F)

end

end ContinuousFlexibility.Radial
