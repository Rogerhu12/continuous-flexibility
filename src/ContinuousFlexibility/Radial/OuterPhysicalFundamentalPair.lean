import ContinuousFlexibility.Radial.OuterWholeMeasure
import ContinuousFlexibility.Radial.OuterPhysicalInverseGauge
import ContinuousFlexibility.Radial.OuterGreenAssembly

/-!
# The actual homogeneous pair on a physical outer interval

Smoothness and nonvanishing of the core coefficients follow from the
original profile.  The finite ODE construction therefore applies to the
same physical natural and Dirichlet states on both ends.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem outerWhole_weight_smooth {D : ReferenceData} (hD : RadialProfileGeometry D)
    (right : Bool) : ContDiff ℝ ∞ (outerTailOutwardWeight D right) :=
  hD.2.2.1.1.comp (contDiff_const.mul contDiff_id)

theorem outerWhole_weight_pos {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {entry x : ℝ} (hentry : entry ∈ radialCore D)
    (hx : x ∈ Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    0 < outerTailOutwardWeight D right x := by
  have hc := outerWhole_coordinate_core hentry hx
  rw [outerOutwardRadius_eq_sign] at hc
  exact hD.2.2.2.2.1 _ hc

theorem outerWhole_coordinate_ne_zero {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {entry x : ℝ} (hentry : entry ∈ radialCore D)
    (hx : x ∈ Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) : x ≠ 0 := by
  have hp : 0 < outerOutwardRadius right x :=
    hD.1.trans (outerWhole_coordinate_core hentry hx).1
  intro hz
  rw [hz] at hp
  have hp' : (0 : ℝ) < 0 := by
    simpa only [outerOutwardRadius, neg_zero, ite_self] using hp
  exact (lt_irrefl (0 : ℝ)) hp'

/-- Both actual coefficients are smooth throughout the half-open outer interval. -/
theorem outerWhole_coefficients_smooth {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {entry lam J : ℝ} (hentry : entry ∈ radialCore D) (hlam : lam ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => lam / outerTailOutwardWeight D right x)
        (Ico (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right))) ∧
      ContDiffOn ℝ ∞ (fun x => J * deriv (outerTailOutwardWeight D right) x / (lam * x))
        (Ico (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right))) := by
  have hw := outerWhole_weight_smooth hD right
  have hdw := (contDiff_infty_iff_deriv.mp hw).2
  constructor
  · exact contDiffOn_const.div hw.contDiffOn
      (fun x hx => (outerWhole_weight_pos hD hentry hx).ne')
  · exact (contDiffOn_const.mul hdw.contDiffOn).div (contDiffOn_const.mul contDiffOn_id)
      (fun x hx => mul_ne_zero hlam (outerWhole_coordinate_ne_zero hD hentry hx))

/-- The actual tail basis and actual profile produce the normalized full
pair; no core solution, transfer bound, or nonzero boundary value is assumed. -/
theorem exists_outerPhysicalFundamentalStatePair
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entry deep η K lam : ℝ}
    (F : MorsePhysicalTailBasis M D right j start deep η K)
    (hentry : entry ∈ radialCore D) (hdeep : deep ∈ radialCore D)
    (horder : outerOutwardRadius right entry ≤ outerOutwardRadius right deep)
    (hlam : 0 < lam)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start deep η K)) :
    Nonempty (OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerOutwardRadius right entry) (outerOutwardRadius right deep)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) := by
  have hcb := outerWhole_interval (right := right) hdeep
  have hcoeff := outerWhole_coefficients_smooth (right := right) (J := (j : ℝ) ^ 2)
    hD hentry hlam.ne'
  have hsub : Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep) ⊆
      Ico (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)) :=
    fun _ hx => ⟨hx.1, hx.2.trans_lt hcb⟩
  apply exists_outerFundamentalStatePair horder hcb
    (hcoeff.1.continuousOn.mono hsub) (hcoeff.2.continuousOn.mono hsub)
  · simpa only [outerOutwardRadius_eq_sign] using
      F.P_system hD (hD.1.trans hdeep.1) hlam.ne' hT
  · simpa only [outerOutwardRadius_eq_sign] using
      F.Q_system hD (hD.1.trans hdeep.1) hlam.ne' hT
  · simpa only [outerOutwardRadius_eq_sign] using F.P_entrance
  · simpa only [outerOutwardRadius_eq_sign] using F.Q_entrance
  · rw [outerOutwardRadius_eq_sign, F.ZQ_entrance]
    exact one_div_ne_zero hlam.ne'

end ContinuousFlexibility.Radial
