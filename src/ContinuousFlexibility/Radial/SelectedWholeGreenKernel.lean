import ContinuousFlexibility.Radial.SelectedPhysicalGreenKernel
import ContinuousFlexibility.Radial.OuterGreenAssembly

/-!
# The actual Green operator from the matching cut to the singular end

The bounded deep inverse and its proved kernel are joined to the finite
regular core through the existing four-block construction. All measures
are the actual restrictions of the radial Hilbert measure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K cut lam : ℝ}
  (F : MorsePhysicalTailBasis M D right j start entrance η K)

local notation "a" => outerTailSign right * cut
local notation "c" => outerTailSign right * entrance
local notation "b" => outerTailSign right * tailPhysicalEndpoint D right
local notation "T" => morsePhysicalDeepTail M D right j start entrance η K
local notation "w" => outerTailOutwardWeight D right
local notation "μ" => outerOutwardIntervalMeasure D right (radialTailInterval D right cut)
local notation "α" => (fun x => lam / w x)
local notation "β" => (fun x => (j : ℝ) ^ 2 * deriv w x / (lam * x))

theorem exists_wholeGreenOperator
    (hD : IsAccumulatingProfile D) (hcut : cut ∈ radialCore D)
    (hentry : entrance ∈ radialCore D) (hac : a ≤ c) (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K) :
    ∃ H : OuterFundamentalStatePair α β F.P (F.ZP lam) F.Q (F.ZQ lam) a c b,
      ∃ R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
        (∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ]
          fun x => ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂μ) ∧
        ∀ (f : Lp ℝ 2 μ) (x : ℝ), x ∈ Ico a b →
          Integrable (fun y => outerGreenKernel lam H.U H.V x y * f y) μ := by
  have hg := matchingProfileGeometry hD
  have hep : 0 < entrance := hg.1.trans hentry.1
  have hcb : c < b := by
    cases right
    · simpa [outerTailSign, tailPhysicalEndpoint] using neg_lt_neg hentry.1
    · simpa [outerTailSign, tailPhysicalEndpoint] using hentry.2
  have hcore (x : ℝ) (hx : x ∈ Icc a c) : outerOutwardRadius right x ∈ radialCore D :=
    outerOutwardRadius_mem_core hcut (by
      simpa only [outerOutwardRadius_eq_sign] using
        (show x ∈ Ico a b from ⟨hx.1, hx.2.trans_lt hcb⟩))
  have hw : ContDiff ℝ ∞ w := hg.2.2.1.1.comp (contDiff_const.mul contDiff_id)
  have hwn (x : ℝ) (hx : x ∈ Icc a c) : w x ≠ 0 := by
    change D.w (outerTailSign right * x) ≠ 0
    rw [← outerOutwardRadius_eq_sign]
    exact (hg.2.2.2.2.1 _ (hcore x hx)).ne'
  have hr (x : ℝ) (hx : x ∈ Icc a c) : x ≠ 0 := by
    have hp := hg.1.trans (hcore x hx).1
    intro hz
    rw [hz, outerOutwardRadius_eq_sign, mul_zero] at hp
    exact (lt_irrefl 0) hp
  have hα : ContinuousOn α (Icc a c) :=
    continuousOn_const.div hw.continuous.continuousOn hwn
  have hβ : ContinuousOn β (Icc a c) :=
    (continuousOn_const.mul (contDiff_infty_iff_deriv.mp hw).2.continuous.continuousOn).div
      (continuousOn_const.mul continuousOn_id) (fun x hx => mul_ne_zero hlam (hr x hx))
  obtain ⟨H⟩ := exists_outerFundamentalStatePair hac hcb hα hβ
    (F.P_system hg hep hlam hT) (F.Q_system hg hep hlam hT) F.P_entrance F.Q_entrance
      (by rw [F.ZQ_entrance]; exact div_ne_zero one_ne_zero hlam)
  obtain ⟨Ddeep, hDdeep, hrow⟩ := F.exists_physicalGreenOperator hD hep hT hphysical hη hK hKinv
  have her : tailPhysicalRadius right (T).entrance = entrance := tailPhysicalRadius_log right hep
  have horder : outerOutwardRadius right cut ≤
      outerOutwardRadius right (tailPhysicalRadius right (T).entrance) := by
    simpa only [her, outerOutwardRadius_eq_sign] using hac
  have hm := outerOutwardRegion_restrict_deep hD hphysical horder
  simp only [her, outerOutwardRadius_eq_sign] at hm
  let Rdeep := l2OperatorMeasureCongr hm.symm Ddeep
  have hRd : ∀ f : Lp ℝ 2 (Measure.restrict μ (Icc a c)ᶜ),
      (Rdeep f : ℝ → ℝ) =ᵐ[Measure.restrict μ (Icc a c)ᶜ] fun x =>
        ∫ y in (Icc a c)ᶜ, F.Q (min x y) * F.P (max x y) * f y ∂μ :=
    l2OperatorMeasureCongr_kernel hm.symm Ddeep
      (fun x y => F.Q (min x y) * F.P (max x y)) hDdeep
  have hrows : ∀ x ∈ Ico c b,
      MemLp (fun y => F.Q (min x y) * F.P (max x y)) 2 (Measure.restrict μ (Icc a c)ᶜ) := by
    intro x hx
    rw [hm]
    exact hrow x hx
  have hP : MemLp F.P 2 (Measure.restrict μ (Icc a c)ᶜ) := by
    rw [hm]
    exact morsePhysicalDeepTail_outward_lift_memLp hg hep hT F.P_natural
  let p := hP.toLp F.P
  letI : IsFiniteMeasure μ := isFiniteMeasure_outerOutwardRegion hD hcut
  letI : IsFiniteMeasure (compactIntervalMeasure μ a c) :=
    isFiniteMeasure_compactIntervalMeasure μ hac
  have hfull : ∀ᵐ x ∂μ, x ∈ Ico a b := by
    apply (outerOutwardRegion_ae_iff hD hcut).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [outerOutwardRadius_eq_sign] using Ioo_subset_Ico_self hx
  refine ⟨H, H.greenOperator μ hac hcb lam Rdeep p, ?_, ?_⟩
  · exact H.greenOperator_ae_eq_integral μ hac hlam hcb F.P_entrance F.Q_entrance
      (F.ZQ_entrance lam) hfull Rdeep p hP.coeFn_toLp hrows hRd
  · intro f x hx
    by_cases hxc : x ≤ c
    · exact H.integrable_kernel_core μ hac hcb F.P_entrance hfull p hP.coeFn_toLp
        f ⟨hx.1, hxc⟩
    · have hcx : c ≤ x := (lt_of_not_ge hxc).le
      exact H.integrable_kernel_deep μ hac hlam hcb F.P_entrance F.Q_entrance
        (F.ZQ_entrance lam) hfull p hP.coeFn_toLp f ⟨hcx, hx.2⟩ (hrows x ⟨hcx, hx.2⟩)

end MorsePhysicalTailBasis

end ContinuousFlexibility.Radial
