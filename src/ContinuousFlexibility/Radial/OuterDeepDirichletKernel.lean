import ContinuousFlexibility.Radial.OuterOutwardGreenTransport
import ContinuousFlexibility.Radial.TailGreenL2Representation

/-!
# The actual deep Dirichlet kernel used by the whole outer inverse

The natural and Dirichlet states are the actual recurrence solutions.
The inverse is the actual Friedrichs inverse.  Their all-L² kernel
identity is proved and transported to the outward physical measure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K : ℝ}

theorem MorsePhysicalTailBasis.logDirichletRow_memLp
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {x : ℝ} (hx : x ∈ Ico
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint) :
    MemLp (fun y => F.logQ (min x y) * F.logP (max x y)) 2
      (deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K)) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hqa : F.logQ T.entrance = 0 := F.Q_log_entry
  rcases eq_or_lt_of_le hx.1 with heq | hlt
  · subst x
    refine (memLp_congr_ae ?_).mp
      (MemLp.zero : MemLp (fun _ : ℝ => (0 : ℝ)) 2 (deepTailMeasure T))
    filter_upwards [deepTailMeasure_ae_mem T] with y hy
    change (0 : ℝ) = F.logQ (min T.entrance y) * F.logP (max T.entrance y)
    rw [min_eq_left hy.1.le, max_eq_right hy.1.le, hqa, zero_mul]
  · have hrow := tailFundamentalGreenKernel_memLp_row (W := (1 : ℝ))
      (deepTail_contDiffOn hT)
      (fun y hy => (deepTail_pos hT y hy))
      (F.Q_smooth.continuousOn.mono (fun _ hy => hy.2))
      (F.P_smooth.continuousOn.mono (fun _ hy => hy.2)) F.P_natural.2.2.1 x
    refine (memLp_congr_ae ?_).mp hrow
    filter_upwards [deepTailMeasure_ae_mem T] with y hy
    rw [tailFundamentalGreenKernel_eq ⟨hlt, hx.2⟩ hy, div_one]

theorem MorsePhysicalTailBasis.logGreen_kernel
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (G : DeepTailL2 (morsePhysicalDeepTail M D right j start entrance η K) →L[ℝ]
      DeepTailL2 (morsePhysicalDeepTail M D right j start entrance η K))
    (hG : ∀ f, TailFriedrichsGraph (morsePhysicalDeepTail M D right j start entrance η K)
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint (G f)
      (f + (morsePhysicalDeepTail M D right j start entrance η K).Λ • G f))
    (f : DeepTailL2 (morsePhysicalDeepTail M D right j start entrance η K)) :
    (G f : ℝ → ℝ) =ᵐ[
      deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K)] fun x =>
      ∫ y, F.logQ (min x y) * F.logP (max x y) * f y
        ∂deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  letI : IsFiniteMeasure (deepTailMeasure T) :=
    isFiniteMeasure_deepTailMeasure_of_physical hD hT hphysical
  have hI : TailFormIdentification T T.endpoint := tailFormIdentification
    ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
    (fun x hx => deepTail_pos hT x (Ioo_subset_Ico_self hx)) le_rfl
  have hua : F.logP T.entrance ≠ 0 := by
    intro hz
    have hqa : F.logQ T.entrance = 0 := F.Q_log_entry
    have hW := F.log_wronskian T.entrance ⟨le_rfl, hT.1⟩
    rw [hz, hqa, mul_zero, zero_mul, sub_self] at hW
    norm_num at hW
  have hUnique : ∀ v, TailNaturalEquation T v → ∃ C : ℝ,
      ∀ x ∈ Ioo T.entrance T.endpoint, v x = C * F.logP x := by
    intro v hv
    refine ⟨v (T.node 0) / F.logP (T.node 0), ?_⟩
    exact tailNaturalEquation_eq_mul hT hη hK F.P_natural hv F.P_node_ne
  have hrep := tailFundamentalGreen_L2_representation hT hI G hG
    F.P_natural hua hUnique (F.Q_smooth.continuousOn.mono (fun _ hx => hx.2))
    F.P_log_system F.Q_log_system F.Q_log_entry F.log_wronskian f
  filter_upwards [hrep, deepTailMeasure_ae_mem T] with x hx hxi
  refine hx.trans (integral_congr_ae ?_)
  filter_upwards [deepTailMeasure_ae_mem T] with y hy
  change tailFundamentalGreenKernel T.entrance T.endpoint F.logQ F.logP 1 x y * f y =
    F.logQ (min x y) * F.logP (max x y) * f y
  rw [tailFundamentalGreenKernel_eq hxi hy, div_one]

/-- The actual bounded deep inverse, actual all-source Dirichlet kernel,
and actual L² rows in the same outward physical measure. -/
theorem MorsePhysicalTailBasis.exists_outwardGreenInverse
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : IsAccumulatingProfile D) (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    (hj : 2 ≤ j) (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K) :
    ∃ A : OuterOutwardTailL2 D (morsePhysicalDeepTail M D right j start entrance η K) right →L[ℝ]
        OuterOutwardTailL2 D (morsePhysicalDeepTail M D right j start entrance η K) right,
      ‖A‖ ≤ 64 / (j : ℝ) ^ 4 ∧
      (∀ f, (A f : ℝ → ℝ) =ᵐ[
        outerOutwardTailMeasure D (morsePhysicalDeepTail M D right j start entrance η K) right]
        fun r => ∫ t, F.Q (min r t) * F.P (max r t) * f t
          ∂outerOutwardTailMeasure D (morsePhysicalDeepTail M D right j start entrance η K) right) ∧
      (∀ r ∈ Ico (outerTailSign right * entrance)
          (outerTailSign right * tailPhysicalEndpoint D right),
        MemLp (fun t => F.Q (min r t) * F.P (max r t)) 2
          (outerOutwardTailMeasure D (morsePhysicalDeepTail M D right j start entrance η K) right)) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hgeom : RadialProfileGeometry D := by
    obtain ⟨C, hC⟩ := hD
    exact hC.1
  have hη' : T.η ≤ 1 / 10 := by change η ≤ 1 / 10; linarith
  have hK' : 10 * tailSmoothStepConstant + 2 ≤ T.K := hKinv
  obtain ⟨G, hGn, hGe, _⟩ := exists_tailDeepInverse T hT hη' hK' T.endpoint (Or.inl rfl)
  refine ⟨outerOutwardGreenInverse hD hphysical G, ?_, ?_, ?_⟩
  · calc
      _ ≤ ‖outerPhysicalDirichletInverse hD hphysical G‖ :=
        outerOutwardOperator_norm_le D T right _
      _ ≤ 12 * (4 / T.Λ) := outerPhysicalDirichletInverse_norm_le hD hphysical G
        (div_nonneg (by norm_num) hT.2.2.1.le) hGn
      _ = 48 / ((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) := by rw [hphysical.1]; ring
      _ ≤ _ := deepTail_physical_frequency_bound hj
  · intro f
    exact outerOutwardGreenInverse_kernel hD hphysical G F.logQ F.logP
      (F.logGreen_kernel hD hT hphysical hη hK G hGe) f
  · intro r hr
    have hcoord := outerTail_outward_log_mem hgeom right hentry hr
    let x := tailPhysicalLog right (outerTailSign right * r)
    have hx : x ∈ Ico T.entrance T.endpoint := hcoord.2
    have hxr : outerOutwardLogRadius right x = r := by
      change outerOutwardRadius right
        (tailPhysicalRadius right (tailPhysicalLog right (outerTailSign right * r))) = r
      rw [tailPhysicalRadius_log right hcoord.1,
        outerOutwardRadius_eq_sign, ← mul_assoc, outerTailSign_mul_self, one_mul]
    have hh := outerOutwardDirichletKernel_row_memLp hD hphysical F.logQ F.logP x
      (F.logDirichletRow_memLp hT hx)
    rw [hxr] at hh
    exact hh

end ContinuousFlexibility.Radial
