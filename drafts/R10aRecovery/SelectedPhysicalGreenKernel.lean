import ContinuousFlexibility.Radial.SelectedOutwardRegionMeasure
import ContinuousFlexibility.Radial.TailGreenAllSources
import ContinuousFlexibility.Radial.OuterFirstOrderRegularity
import ContinuousFlexibility.Analysis.CoordinateGaugeKernel

/-!
# The actual weighted physical Dirichlet kernel

The exact logarithmic isometry transports the proved Friedrichs inverse
and its all-source representation. The factor twelve is retained, giving
the physical unit-flux kernel Q(min x y) P(max x y).
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

private theorem selected_outward_logRadius_strictMono (right : Bool) :
    StrictMono (fun x => outerOutwardRadius right (tailPhysicalRadius right x)) := by
  intro x y hxy
  cases right
  · change -exp (-x) < -exp (-y)
    exact neg_lt_neg (exp_lt_exp.mpr (neg_lt_neg hxy))
  · exact exp_lt_exp.mpr hxy

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K : ℝ}
  (F : MorsePhysicalTailBasis M D right j start entrance η K)

local notation "T" => morsePhysicalDeepTail M D right j start entrance η K
local notation "c" => outerTailSign right * entrance
local notation "b" => outerTailSign right * tailPhysicalEndpoint D right
local notation "μ" => outerOutwardTailMeasure D T right

/-- Every physical kernel row lies in the actual weighted L² space.
Only a compact part of Q occurs in each individual row. -/
theorem physical_kernel_memLp_row (hD : IsAccumulatingProfile D)
    (hentry : 0 < entrance) (hT : DeepTailHypotheses T)
    (hphysical : TailPhysicalRelation D T right j start)
    {x : ℝ} (hx : x ∈ Ico c b) :
    MemLp (fun y => F.Q (min x y) * F.P (max x y)) 2 μ := by
  letI : IsFiniteMeasure (radialHilbertMeasure D) := radialHilbertMeasure_isFinite hD
  letI : IsFiniteMeasure μ := by unfold outerOutwardTailMeasure; infer_instance
  have hQ := (F.Q_system (matchingProfileGeometry hD) hentry one_ne_zero hT).continuousOn.1
  have hQc : ContinuousOn F.Q (Icc c x) :=
    hQ.mono (fun y hy => ⟨hy.1, hy.2.trans_lt hx.2⟩)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hQc.norm
  have hQLp : MemLp F.Q 2 (μ.restrict (Icc c x)) := by
    apply MemLp.of_bound (hQc.aestronglyMeasurable measurableSet_Icc) C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hC (mem_image_of_mem _ hy)
  have hP : MemLp F.P 2 μ :=
    morsePhysicalDeepTail_outward_lift_memLp (matchingProfileGeometry hD) hentry hT F.P_natural
  have hleft := (memLp_indicator_iff_restrict measurableSet_Icc).mpr
    (hQLp.const_mul (F.P x))
  have hright := (hP.const_mul (F.Q x)).indicator measurableSet_Ioi
  have hfull : ∀ᵐ y ∂μ, y ∈ Ioo c b := by
    rw [outerOutwardTailMeasure_eq_density hD hphysical]
    have her : tailPhysicalRadius right T.entrance = entrance := tailPhysicalRadius_log right hentry
    simpa only [her, outerOutwardRadius_eq_sign] using
      (withDensity_absolutelyContinuous
        (volume.restrict (Ioo (outerOutwardRadius right (tailPhysicalRadius right T.entrance))
          (outerOutwardRadius right (tailPhysicalEndpoint D right))))
        (fun y => ENNReal.ofReal (12 * D.w (outerOutwardRadius right y) / y ^ 2))).ae_le
          (ae_restrict_mem measurableSet_Ioo)
  apply (memLp_congr_ae ?_).mp (hleft.add hright)
  filter_upwards [hfull] with y hy
  by_cases hyx : y ≤ x
  · have hyL : y ∈ Icc c x := ⟨hy.1.le, hyx⟩
    have hyR : y ∉ Ioi x := not_lt.mpr hyx
    rw [indicator_of_mem hyL, indicator_of_notMem hyR,
      min_eq_right hyx, max_eq_left hyx, add_zero]
    exact mul_comm _ _
  · have hxy : x < y := lt_of_not_ge hyx
    have hyL : y ∉ Icc c x := fun h => hyx h.2
    rw [indicator_of_notMem hyL, indicator_of_mem hxy,
      min_eq_left hxy.le, max_eq_right hxy.le, zero_add]

/-- The deep physical inverse is constructed, with an actual kernel
formula for every source and no kernel-representation hypothesis. -/
theorem exists_physicalGreenOperator (hD : IsAccumulatingProfile D)
    (hentry : 0 < entrance) (hT : DeepTailHypotheses T)
    (hphysical : TailPhysicalRelation D T right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K) :
    ∃ R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      (∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ]
        fun x => ∫ y, F.Q (min x y) * F.P (max x y) * f y ∂μ) ∧
      ∀ x ∈ Ico c b, MemLp (fun y => F.Q (min x y) * F.P (max x y)) 2 μ := by
  letI : IsFiniteMeasure (deepTailMeasure T) :=
    isFiniteMeasure_deepTailMeasure_of_physical hD hT hphysical
  have hη' : T.η ≤ 1 / 10 := by change η ≤ 1 / 10; linarith
  obtain ⟨G, _, hG, _⟩ :=
    exists_tailDeepInverse T hT hη' hKinv T.endpoint (Or.inl rfl)
  have hend := tailPhysicalEndpoint_pos hD right
  have hua : F.logP T.entrance ≠ 0 := by
    change F.logP (tailPhysicalLog right entrance) ≠ 0
    rw [F.P_log_entry]
    exact inv_ne_zero (rpow_pos_of_pos (div_pos hentry hend) _).ne'
  have hQc : ContinuousOn F.logQ (Ico T.entrance T.endpoint) :=
    F.Q_smooth.continuousOn.mono (fun _ hx => hx.2)
  let Klog := tailFundamentalGreenKernel T.entrance T.endpoint F.logQ F.logP 1
  have hGK : ∀ f : DeepTailL2 T, (G f : ℝ → ℝ) =ᵐ[deepTailMeasure T]
      fun x => ∫ y, Klog x y * f y ∂deepTailMeasure T :=
    tailFundamentalGreen_representation_L2 hT hη hK G hG F.P_natural hua F.P_node_ne
      hQc F.P_log_system F.Q_log_system F.Q_log_entry F.log_wronskian
  let Rcoord : ℝ → ℝ := fun x => outerOutwardRadius right (tailPhysicalRadius right x)
  let amp := outerPhysicalAmplitude D right j
  let E := l2EquivCompose (outerOutwardTailEquiv D T right) (outerPhysicalTailEquiv hD hphysical)
  have hRm : MeasurableEmbedding Rcoord :=
    (measurableEmbedding_outerOutwardRadius right).comp (measurableEmbedding_tailPhysicalRadius right)
  have hmeasure : Measure.map Rcoord (squareDensityMeasure (deepTailMeasure T) amp) = μ := by
    rw [← outerPhysicalPullbackMeasure_eq_squareDensity hD hphysical]
    change Measure.map (outerOutwardRadius right ∘ tailPhysicalRadius right)
      (outerPhysicalPullbackMeasure D T right) = _
    rw [← Measure.map_map (measurableEmbedding_outerOutwardRadius right).measurable
      (measurableEmbedding_tailPhysicalRadius right).measurable,
      outerPhysicalPullbackMeasure_map_radial hD hphysical]
    rfl
  have hE (f : Lp ℝ 2 μ) :
      (E f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => amp x * f (Rcoord x) := by
    have hr := outerOutwardTailEquiv_ae D T right f
    have hr' :
        (outerOutwardTailEquiv D T right f : ℝ → ℝ) =ᵐ[
          Measure.map (tailPhysicalRadius right) (outerPhysicalPullbackMeasure D T right)]
          fun r => f (outerOutwardRadius right r) := by
      rwa [outerPhysicalPullbackMeasure_map_radial hD hphysical]
    have hc := outerPhysicalPullback_ae_eq hD hphysical
      (ae_eq_comp (measurableEmbedding_tailPhysicalRadius right).measurable.aemeasurable hr')
    have hg := outerPhysicalTailEquiv_ae hD hphysical (outerOutwardTailEquiv D T right f)
    filter_upwards [hc, hg] with x hx hgx
    change outerPhysicalTailEquiv hD hphysical (outerOutwardTailEquiv D T right f) x = _
    exact hgx.trans (congrArg (fun q => amp x * q) hx)
  let R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    E.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (G.comp ((12 : ℝ) • E.toContinuousLinearEquiv.toContinuousLinearMap))
  have hconj (f : Lp ℝ 2 μ) : E (R f) = G ((12 : ℝ) • E f) :=
    E.apply_symm_apply _
  have hfull : ∀ᵐ x ∂deepTailMeasure T, x ∈ Ioo T.entrance T.endpoint :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)
  have hkernel : ∀ᵐ x ∂deepTailMeasure T, ∀ᵐ y ∂deepTailMeasure T,
      amp x * amp y * (F.Q (min (Rcoord x) (Rcoord y)) *
        F.P (max (Rcoord x) (Rcoord y))) = 12 * Klog x y := by
    filter_upwards [hfull] with x hx
    filter_upwards [hfull] with y hy
    have hmono := (selected_outward_logRadius_strictMono right).monotone
    have hsqrt : sqrt 12 * sqrt 12 = (12 : ℝ) := by
      nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
    change amp x * amp y * (F.Q (min (Rcoord x) (Rcoord y)) *
      F.P (max (Rcoord x) (Rcoord y))) =
      12 * tailFundamentalGreenKernel T.entrance T.endpoint F.logQ F.logP 1 x y
    rw [tailFundamentalGreenKernel_eq hx hy, div_one]
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left (hmono hxy), max_eq_right (hmono hxy),
        min_eq_left hxy, max_eq_right hxy]
      dsimp only [P, Q, Rcoord]
      rw [outerTailOutwardLift_reflect, outerTailOutwardLift_reflect,
        tailPhysicalLift_radius, tailPhysicalLift_radius,
        ← outerLogGauge_eq_rpow, ← outerLogGauge_eq_rpow]
      dsimp only [amp, outerPhysicalAmplitude]
      calc
        _ = (sqrt 12 * sqrt 12) * (F.logQ x * F.logP y) := by
          field_simp [(outerLogGauge_pos hend j x).ne', (outerLogGauge_pos hend j y).ne'] <;> ring
        _ = _ := by rw [hsqrt]
    · rw [min_eq_right (hmono hyx), max_eq_left (hmono hyx),
        min_eq_right hyx, max_eq_left hyx]
      dsimp only [P, Q, Rcoord]
      rw [outerTailOutwardLift_reflect, outerTailOutwardLift_reflect,
        tailPhysicalLift_radius, tailPhysicalLift_radius,
        ← outerLogGauge_eq_rpow, ← outerLogGauge_eq_rpow]
      dsimp only [amp, outerPhysicalAmplitude]
      calc
        _ = (sqrt 12 * sqrt 12) * (F.logQ y * F.logP x) := by
          field_simp [(outerLogGauge_pos hend j x).ne', (outerLogGauge_pos hend j y).ne'] <;> ring
        _ = _ := by rw [hsqrt]
  refine ⟨R, ?_, fun x hx => F.physical_kernel_memLp_row hD hentry hT hphysical hx⟩
  exact coordinateGauge_operator_kernel hRm
    (continuous_outerPhysicalAmplitude hend j).measurable (outerPhysicalAmplitude_pos hend j)
    hmeasure E hE G R hconj hGK hkernel

end MorsePhysicalTailBasis

end ContinuousFlexibility.Radial
