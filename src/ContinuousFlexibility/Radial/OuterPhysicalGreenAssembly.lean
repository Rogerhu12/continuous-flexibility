module

public import ContinuousFlexibility.Radial.OuterPhysicalBlocks

/-!
# The actual whole-outer Green operator

The deep inverse, Poisson vector, compact core kernel, and normalized
homogeneous pair are placed in the same physical Hilbert space.  The
resulting bounded operator has the single manuscript kernel for every L²
source.  Its bound uses only the core and Poisson estimates supplied by
the preceding transition-input lemma.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem MorsePhysicalTailBasis.exists_wholeGreenOperator
    {M : MorseChainData} {D : ReferenceData}
    {right : Bool} {j start : ℕ} {entry deep η K lam : ℝ}
    (F : MorsePhysicalTailBasis M D right j start deep η K)
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerOutwardRadius right entry) (outerOutwardRadius right deep)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hD : IsAccumulatingProfile D)
    (hentry : entry ∈ radialCore D) (hdeep : deep ∈ radialCore D)
    (horder : outerOutwardRadius right entry ≤ outerOutwardRadius right deep)
    (hlam : 0 < lam)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start deep η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start deep η K) right j start)
    (hj : 2 ≤ j) (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K)
    (hP : MemLp F.P 2 (outerOutwardTailMeasure D
      (morsePhysicalDeepTail M D right j start deep η K) right)) :
    ∃ R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry,
      (∀ f : OuterWholeL2 D right entry,
        (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] fun x =>
          ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂outerWholeMeasure D right entry) ∧
      ∀ A Kcore : ℝ, 0 ≤ A → 0 ≤ Kcore →
        (∀ x ∈ Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep),
          |H.U x| ≤ Kcore) →
        (∀ x ∈ Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep),
          |H.V x| ≤ Kcore) →
        (outerWholeMeasure D right entry).real
          (Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep)) ≤ lam * A ^ 2 →
        ‖hP.toLp F.P‖ ≤ sqrt lam * A →
        ‖R‖ ≤ 2 * (64 / (j : ℝ) ^ 4 + 2 * A ^ 2 * Kcore ^ 2) := by
  let μ := outerWholeMeasure D right entry
  let a := outerOutwardRadius right entry
  let c := outerOutwardRadius right deep
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  letI : IsFiniteMeasure μ := outerWholeMeasure_isFinite hD right entry
  letI : IsFiniteMeasure (compactIntervalMeasure μ a c) :=
    isFiniteMeasure_compactIntervalMeasure μ horder
  have hcb : c < b := outerWhole_interval hdeep
  have hPc : F.P c = 1 := by
    simpa only [c, outerOutwardRadius_eq_sign] using F.P_entrance
  have hQc : F.Q c = 0 := by
    simpa only [c, outerOutwardRadius_eq_sign] using F.Q_entrance
  have hZQc : F.ZQ lam c = 1 / lam := by
    simpa only [c, outerOutwardRadius_eq_sign] using F.ZQ_entrance lam
  have hμ : ∀ᵐ x ∂μ, x ∈ Ico a b :=
    (outerWholeMeasure_ae_mem hentry).mono (fun _ hx => ⟨hx.1.le, hx.2⟩)
  obtain ⟨B, p, hBn, hp, hpn, hrow, hBk⟩ :=
    F.exists_wholeDeepBlocks hD hentry hdeep horder hT hphysical hj hη hK hKinv hP
  let R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := H.greenOperator μ horder hcb lam B p
  refine ⟨R, ?_, ?_⟩
  · intro f
    exact H.greenOperator_ae_eq_integral μ horder hlam.ne' hcb hPc hQc hZQc
      hμ B p hp hrow hBk f
  · intro A Kcore hA hKcore hU hV hmass hPbound
    have hmass' : (measureUnivNNReal (compactIntervalMeasure μ a c) : ℝ) ≤ lam * A ^ 2 := by
      have hm := congrArg ENNReal.toReal (coe_measureUnivNNReal (compactIntervalMeasure μ a c))
      rw [ENNReal.coe_toReal, compactIntervalMeasure_univ μ horder] at hm
      exact hm.trans_le hmass
    have hpbound : ‖p‖ ≤ sqrt lam * A := hpn.trans_le hPbound
    exact norm_outerWholeGreenOperator_le μ (Icc a c) measurableSet_Icc
      (compactIntervalMeasure μ a c) (l2CompactIntervalEquiv μ horder)
      hlam hA hKcore (by positivity) ⟨c, horder, le_rfl⟩
      (outerCoreRestriction H.U (H.continuousOn_core hcb).1)
      (outerCoreRestriction H.V (H.continuousOn_core hcb).2) B p
      (fun x => hU x x.property) (fun x => hV x x.property) hmass' hBn hpbound

end ContinuousFlexibility.Radial
