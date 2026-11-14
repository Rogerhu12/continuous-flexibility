module

public import ContinuousFlexibility.Radial.SelectedWholeGreenKernel
public import ContinuousFlexibility.Radial.OuterWholeNaturalVector
public import ContinuousFlexibility.Radial.OuterWholeMeasure

/-!
# The same whole Green inverse and its natural L² vector

This is the original full-source Green construction expressed in the
canonical whole-tail measure. The natural vector is supplied by the
existing core/deep assembly, for the very same fundamental pair.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem outerWholeMeasure_eq_outwardInterval {D : ReferenceData} {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D) :
    outerWholeMeasure D right cut =
      outerOutwardIntervalMeasure D right (radialTailInterval D right cut) := by
  rw [outerWholeMeasure_eq_density hcut, outerOutwardIntervalMeasure,
    outerOutward_tail_image]

theorem MorsePhysicalTailBasis.exists_matchedWholeGreenOperator
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
    {entrance η K cut lam : ℝ}
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : IsAccumulatingProfile D) (hcut : cut ∈ radialCore D)
    (hentry : entrance ∈ radialCore D)
    (hac : outerOutwardRadius right cut ≤ outerOutwardRadius right entrance)
    (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K) :
    ∃ H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerOutwardRadius right cut) (outerOutwardRadius right entrance)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)),
      ∃ R : OuterWholeL2 D right cut →L[ℝ] OuterWholeL2 D right cut,
        MemLp H.V 2 (outerWholeMeasure D right cut) ∧
        (∀ f : OuterWholeL2 D right cut, (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right cut]
          fun x => ∫ y, outerGreenKernel lam H.U H.V x y * f y
            ∂outerWholeMeasure D right cut) ∧
        ∀ (f : OuterWholeL2 D right cut) (x : ℝ),
          x ∈ Ico (outerOutwardRadius right cut)
            (outerOutwardRadius right (tailPhysicalEndpoint D right)) →
          Integrable (fun y => outerGreenKernel lam H.U H.V x y * f y)
            (outerWholeMeasure D right cut) := by
  have hm := outerWholeMeasure_eq_outwardInterval (right := right) hcut
  have hex := F.exists_selectedWholeGreenOperator hD hcut hentry
    (by simpa only [outerOutwardRadius_eq_sign] using hac) hlam hT hphysical hη hK hKinv
  rw [← hm, ← outerOutwardRadius_eq_sign right cut,
    ← outerOutwardRadius_eq_sign right entrance,
    ← outerOutwardRadius_eq_sign right (tailPhysicalEndpoint D right)] at hex
  obtain ⟨H, R, hR, hrow⟩ := hex
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let μ := outerWholeMeasure D right cut
  have hg := matchingProfileGeometry hD
  have hep : 0 < entrance := hg.1.trans hentry.1
  have hcb := outerWhole_interval (right := right) hentry
  have her : tailPhysicalRadius right T.entrance = entrance :=
    tailPhysicalRadius_log right hep
  have hP : MemLp F.P 2
      (μ.restrict (Icc (outerOutwardRadius right cut) (outerOutwardRadius right entrance))ᶜ) := by
    change MemLp F.P 2 ((outerWholeMeasure D right cut).restrict
      (Icc (outerOutwardRadius right cut) (outerOutwardRadius right entrance))ᶜ)
    have hdeep : outerWholeMeasure D right entrance = outerOutwardTailMeasure D T right := by
      calc
        _ = outerWholeMeasure D right (tailPhysicalRadius right T.entrance) :=
          congrArg (outerWholeMeasure D right) her.symm
        _ = _ := outerWholeMeasure_tail D T right
    rw [outerWholeMeasure_restrict_deep hcut hentry hac, hdeep]
    exact morsePhysicalDeepTail_outward_lift_memLp hg hep hT F.P_natural
  let p := hP.toLp F.P
  letI : IsFiniteMeasure μ := outerWholeMeasure_isFinite hD right cut
  letI : IsFiniteMeasure (compactIntervalMeasure μ
      (outerOutwardRadius right cut) (outerOutwardRadius right entrance)) :=
    isFiniteMeasure_compactIntervalMeasure μ hac
  have hμ : ∀ᵐ x ∂μ, x ∈ Ico (outerOutwardRadius right cut)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) :=
    (outerWholeMeasure_ae_mem (right := right) hcut).mono fun _ hx => Ioo_subset_Ico_self hx
  have hPc : F.P (outerOutwardRadius right entrance) = 1 := by
    simpa only [outerOutwardRadius_eq_sign] using F.P_entrance
  exact ⟨H, R, H.V_memLp μ hac hcb hPc hμ p hP.coeFn_toLp, hR, hrow⟩

end ContinuousFlexibility.Radial
