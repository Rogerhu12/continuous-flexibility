import ContinuousFlexibility.Radial.OuterDeepDirichletKernel
import ContinuousFlexibility.Radial.OuterPhysicalFundamentalPair

/-!
# The actual deep blocks in the whole outer Hilbert space

The deep Friedrichs inverse and the same natural Poisson vector are
transported across the proved equality of physical measures.  Their
norms and integral kernels are retained exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem MorsePhysicalTailBasis.exists_wholeDeepBlocks
    {M : MorseChainData} {D : ReferenceData}
    {right : Bool} {j start : ℕ} {entry deep η K : ℝ}
    (F : MorsePhysicalTailBasis M D right j start deep η K)
    (hD : IsAccumulatingProfile D)
    (hentry : entry ∈ radialCore D) (hdeep : deep ∈ radialCore D)
    (horder : outerOutwardRadius right entry ≤ outerOutwardRadius right deep)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start deep η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start deep η K) right j start)
    (hj : 2 ≤ j) (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K)
    (hP : MemLp F.P 2 (outerOutwardTailMeasure D
      (morsePhysicalDeepTail M D right j start deep η K) right)) :
    let μ := outerWholeMeasure D right entry
    let a := outerOutwardRadius right entry
    let c := outerOutwardRadius right deep
    let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
    ∃ A : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict (Icc a c)ᶜ),
      ∃ p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ),
        ‖A‖ ≤ 64 / (j : ℝ) ^ 4 ∧
        (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] F.P ∧
        ‖p‖ = ‖hP.toLp F.P‖ ∧
        (∀ r ∈ Ico c b, MemLp (fun t => F.Q (min r t) * F.P (max r t))
          2 (μ.restrict (Icc a c)ᶜ)) ∧
        ∀ f : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ),
          (A f : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] fun r =>
            ∫ t, F.Q (min r t) * F.P (max r t) * f t ∂μ.restrict (Icc a c)ᶜ := by
  dsimp only
  let T := morsePhysicalDeepTail M D right j start deep η K
  let μ := outerWholeMeasure D right entry
  let a := outerOutwardRadius right entry
  let c := outerOutwardRadius right deep
  have hgeom := matchingProfileGeometry hD
  have hdeepPos : 0 < deep := hgeom.1.trans hdeep.1
  have hcoord : tailPhysicalRadius right T.entrance = deep :=
    tailPhysicalRadius_log right hdeepPos
  have hm : μ.restrict (Icc a c)ᶜ = outerOutwardTailMeasure D T right := by
    calc
      μ.restrict (Icc a c)ᶜ = outerWholeMeasure D right deep :=
        outerWholeMeasure_restrict_deep hentry hdeep horder
      _ = outerWholeMeasure D right (tailPhysicalRadius right T.entrance) :=
        congrArg (outerWholeMeasure D right) hcoord.symm
      _ = _ := outerWholeMeasure_tail D T right
  obtain ⟨B, hBn, hBk, hBr⟩ :=
    F.exists_outwardGreenInverse hD hdeepPos hT hphysical hj hη hK hKinv
  have hP' : MemLp F.P 2 (μ.restrict (Icc a c)ᶜ) := by
    rw [hm]
    exact hP
  let A := l2OperatorMeasureCongr hm.symm B
  let p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ) := hP'.toLp F.P
  refine ⟨A, p, ?_, hP'.coeFn_toLp, ?_, ?_, ?_⟩
  · change ‖l2OperatorMeasureCongr hm.symm B‖ ≤ 64 / (j : ℝ) ^ 4
    rw [norm_l2OperatorMeasureCongr]
    exact hBn
  · change ‖hP'.toLp F.P‖ = ‖hP.toLp F.P‖
    rw [Lp.norm_toLp, Lp.norm_toLp, hm]
  · intro r hr
    rw [hm]
    apply hBr r
    simpa only [outerOutwardRadius_eq_sign] using hr
  · intro f
    exact l2OperatorMeasureCongr_kernel hm.symm B
      (fun r t => F.Q (min r t) * F.P (max r t)) hBk f

end ContinuousFlexibility.Radial
