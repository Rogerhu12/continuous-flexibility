module

public import ContinuousFlexibility.Radial.OuterWholeNaturalVector
public import ContinuousFlexibility.Radial.OuterPhysicalFundamentalPair

/-!
# The norm of the same physical whole natural solution

The full natural vector from the Green assembly is exactly H.V almost
everywhere. The exact deep-measure identity transports the already
constructed Poisson vector without changing its norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem MorsePhysicalTailBasis.wholeNatural_memLp_norm
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
    (hP : MemLp F.P 2 (outerOutwardTailMeasure D
      (morsePhysicalDeepTail M D right j start deep η K) right)) :
    ∃ hV : MemLp H.V 2 (outerWholeMeasure D right entry),
      ∀ A Kcore : ℝ, 0 ≤ A → 0 ≤ Kcore →
        (∀ x ∈ Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep),
          |H.V x| ≤ Kcore) →
        (outerWholeMeasure D right entry).real
          (Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep)) ≤
            lam * A ^ 2 →
        ‖hP.toLp F.P‖ ≤ sqrt lam * A →
        ‖hV.toLp H.V‖ ≤ 2 * (sqrt lam * A * Kcore) := by
  let μ := outerWholeMeasure D right entry
  let a := outerOutwardRadius right entry
  let c := outerOutwardRadius right deep
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let T := morsePhysicalDeepTail M D right j start deep η K
  letI : IsFiniteMeasure μ := outerWholeMeasure_isFinite hD right entry
  letI : IsFiniteMeasure (compactIntervalMeasure μ a c) :=
    isFiniteMeasure_compactIntervalMeasure μ horder
  have hgeom := matchingProfileGeometry hD
  have hcoord : tailPhysicalRadius right T.entrance = deep :=
    tailPhysicalRadius_log right (hgeom.1.trans hdeep.1)
  have hm : μ.restrict (Icc a c)ᶜ = outerOutwardTailMeasure D T right := by
    calc
      _ = outerWholeMeasure D right deep := outerWholeMeasure_restrict_deep hentry hdeep horder
      _ = outerWholeMeasure D right (tailPhysicalRadius right T.entrance) :=
        congrArg (outerWholeMeasure D right) hcoord.symm
      _ = _ := outerWholeMeasure_tail D T right
  have hP' : MemLp F.P 2 (μ.restrict (Icc a c)ᶜ) := by
    rw [hm]
    exact hP
  let p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ) := hP'.toLp F.P
  have hpn : ‖p‖ = ‖hP.toLp F.P‖ := by
    change ‖hP'.toLp F.P‖ = ‖hP.toLp F.P‖
    rw [Lp.norm_toLp, Lp.norm_toLp, hm]
  have hcb : c < b := outerWhole_interval hdeep
  have hPc : F.P c = 1 := by
    simpa only [c, outerOutwardRadius_eq_sign] using F.P_entrance
  have hμ : ∀ᵐ x ∂μ, x ∈ Ico a b :=
    (outerWholeMeasure_ae_mem hentry).mono (fun _ hx => ⟨hx.1.le, hx.2⟩)
  have hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] F.P := hP'.coeFn_toLp
  have hV : MemLp H.V 2 μ := H.V_memLp μ horder hcb hPc hμ p hp
  have heq : hV.toLp H.V = H.naturalVector μ horder hcb p :=
    Lp.ext (hV.coeFn_toLp.trans (H.naturalVector_ae μ horder hcb hPc hμ p hp).symm)
  refine ⟨hV, ?_⟩
  intro A Kcore hA hKcore hVbound hmass hPbound
  have hmass' : (measureUnivNNReal (compactIntervalMeasure μ a c) : ℝ) ≤
      lam * A ^ 2 := by
    have hmassEq := congrArg ENNReal.toReal
      (coe_measureUnivNNReal (compactIntervalMeasure μ a c))
    rw [ENNReal.coe_toReal, compactIntervalMeasure_univ μ horder] at hmassEq
    exact hmassEq.trans_le hmass
  rw [heq]
  exact H.norm_naturalVector_le μ horder hcb hlam hA hKcore p hVbound hmass'
    (hpn.trans_le hPbound)

end ContinuousFlexibility.Radial
