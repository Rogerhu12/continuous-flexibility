import ContinuousFlexibility.Radial.OuterPhysicalRobinSolution
import ContinuousFlexibility.Analysis.IntervalWeakReflection
import ContinuousFlexibility.Radial.ModeLocalMeasure

/-!
# The actual whole-outer representative in the frozen flux convention

This is a thin projection of the original all-source Robin graph theorem.
On the open interval its continuous within flux is the ambient derivative
flux, and the original one-sided entrance condition is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem matchedOuterWhole_representative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {right : Bool} {entry c lam : ℝ} {j : ℕ}
    (hentry : entry ∈ radialCore D) (hlam : 0 < lam)
    {P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      P ZP Q ZQ (outerOutwardRadius right entry) c
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hV : MemLp H.V 2 (outerWholeMeasure D right entry))
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry)
    (hR : ∀ f : OuterWholeL2 D right entry,
      (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] fun x =>
        ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂outerWholeMeasure D right entry)
    (f : OuterWholeL2 D right entry) :
    ∃ u : ℝ → ℝ,
      (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] u ∧
      ContDiffOn ℝ 1 u (Ico (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right))) ∧
      HasIntervalWeakDerivative (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right))
        (fun x => outerTailOutwardWeight D right x * deriv u x)
        (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / x * u x -
          outerWholeDensity D right x * f x) ∧
      outerStatePair H.entrance
        (u (outerOutwardRadius right entry),
          outerTailOutwardWeight D right (outerOutwardRadius right entry) *
            derivWithin u (Ico (outerOutwardRadius right entry)
              (outerOutwardRadius right (tailPhysicalEndpoint D right)))
              (outerOutwardRadius right entry) / lam) = 0 := by
  have hgraph := (outerPhysicalGreenValue_graph_and_trace hD hentry
    hlam.ne' H hV R hR f).1
  rcases hgraph with ⟨u, q, hu, hreg, hq, hflux, hweak, hRobin⟩
  refine ⟨u, hu, hreg, ?_, ?_⟩
  · apply hweak.congr_restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [hflux x (Ioo_subset_Ico_self hx), derivWithin_of_mem_nhds
        (mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Ico_self)]
    · exact EventuallyEq.rfl
  · rw [← hflux (outerOutwardRadius right entry) ⟨le_rfl, outerWhole_interval hentry⟩]
    exact hRobin

end ContinuousFlexibility.Radial
