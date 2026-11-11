import ContinuousFlexibility.Analysis.CoordinateGaugeKernel
import ContinuousFlexibility.Radial.OuterPhysicalInverseGauge

/-!
# The actual deep inverse and kernel in outward coordinates

The physical inverse and its measure are reflected together.  Its
logarithmic gauge is exact, and transports the same Dirichlet kernel
with its two physical gauge factors.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

def outerOutwardLogRadius (right : Bool) (x : ℝ) : ℝ :=
  outerOutwardRadius right (tailPhysicalRadius right x)

theorem measurableEmbedding_outerOutwardLogRadius (right : Bool) :
    MeasurableEmbedding (outerOutwardLogRadius right) :=
  (measurableEmbedding_outerOutwardRadius right).comp (measurableEmbedding_tailPhysicalRadius right)

theorem strictMono_outerOutwardLogRadius (right : Bool) :
    StrictMono (outerOutwardLogRadius right) := by
  intro x y hxy
  cases right
  · change -exp (-x) < -exp (-y)
    exact neg_lt_neg (exp_lt_exp.mpr (neg_lt_neg hxy))
  · change exp x < exp y
    exact exp_lt_exp.mpr hxy

theorem outerOutwardLogRadius_min (right : Bool) (x y : ℝ) :
    min (outerOutwardLogRadius right x) (outerOutwardLogRadius right y) =
      outerOutwardLogRadius right (min x y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left ((strictMono_outerOutwardLogRadius right).monotone h)]
  · rw [min_eq_right h, min_eq_right ((strictMono_outerOutwardLogRadius right).monotone h)]

theorem outerOutwardLogRadius_max (right : Bool) (x y : ℝ) :
    max (outerOutwardLogRadius right x) (outerOutwardLogRadius right y) =
      outerOutwardLogRadius right (max x y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right ((strictMono_outerOutwardLogRadius right).monotone h)]
  · rw [max_eq_left h, max_eq_left ((strictMono_outerOutwardLogRadius right).monotone h)]

theorem outerTailOutwardLift_logRadius (D : ReferenceData) (right : Bool)
    (j : ℕ) (u : ℝ → ℝ) (x : ℝ) :
    outerTailOutwardLift D right j u (outerOutwardLogRadius right x) =
      outerLogGauge D right j x * u x := by
  rw [outerOutwardLogRadius, outerTailOutwardLift_reflect, tailPhysicalLift_radius,
    ← outerLogGauge_eq_rpow]

/-- The exact outward-to-logarithmic isometry. -/
def outerOutwardLogEquiv
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start) :
    OuterOutwardTailL2 D T right ≃ₗᵢ[ℝ] DeepTailL2 T :=
  (outerOutwardTailEquiv D T right).trans (outerPhysicalTailEquiv hD hphysical)

theorem outerOutwardLogEquiv_apply
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (f : OuterOutwardTailL2 D T right) :
    outerOutwardLogEquiv hD hphysical f =
      outerPhysicalTailEquiv hD hphysical (outerOutwardTailEquiv D T right f) := by
  rw [outerOutwardLogEquiv, LinearIsometryEquiv.trans_apply]

theorem outerOutwardLogEquiv_ae
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (f : OuterOutwardTailL2 D T right) :
    (outerOutwardLogEquiv hD hphysical f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x =>
      outerPhysicalAmplitude D right j x * f (outerOutwardLogRadius right x) := by
  have hr := outerOutwardTailEquiv_ae D T right f
  have hrmap := ae_eq_of_measure_eq (outerPhysicalPullbackMeasure_map_radial hD hphysical).symm hr
  have hp := ae_eq_comp (measurableEmbedding_tailPhysicalRadius right).measurable.aemeasurable hrmap
  have hp' := outerPhysicalPullback_ae_eq hD hphysical hp
  exact l2Equiv_trans_coordinate_mul_ae (outerOutwardTailEquiv D T right)
    (outerPhysicalTailEquiv hD hphysical) f (outerPhysicalAmplitude D right j)
    (tailPhysicalRadius right) (fun x => f (outerOutwardLogRadius right x)) hp'
    (outerPhysicalTailEquiv_ae hD hphysical (outerOutwardTailEquiv D T right f))

theorem outerOutwardLogRadius_map_squareDensity
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start) :
    Measure.map (outerOutwardLogRadius right)
      (squareDensityMeasure (deepTailMeasure T) (outerPhysicalAmplitude D right j)) =
      outerOutwardTailMeasure D T right := by
  rw [← outerPhysicalPullbackMeasure_eq_squareDensity hD hphysical]
  change Measure.map ((outerOutwardRadius right) ∘ (tailPhysicalRadius right))
    (outerPhysicalPullbackMeasure D T right) = _
  rw [← Measure.map_map (measurableEmbedding_outerOutwardRadius right).measurable
    (measurableEmbedding_tailPhysicalRadius right).measurable,
    outerPhysicalPullbackMeasure_map_radial hD hphysical]
  rfl

/-- The same already constructed physical Dirichlet inverse, reflected outward. -/
def outerOutwardGreenInverse
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T) :
    OuterOutwardTailL2 D T right →L[ℝ] OuterOutwardTailL2 D T right :=
  outerOutwardOperator D T right (outerPhysicalDirichletInverse hD hphysical G)

theorem outerOutwardGreenInverse_conjugacy
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T) (f : OuterOutwardTailL2 D T right) :
    outerOutwardLogEquiv hD hphysical (outerOutwardGreenInverse hD hphysical G f) =
      G ((12 : ℝ) • outerOutwardLogEquiv hD hphysical f) := by
  rw [outerOutwardLogEquiv_apply, outerOutwardGreenInverse,
    outerOutwardOperator_apply, outerPhysicalDirichletInverse_apply,
    outerOutwardLogEquiv_apply]

/-- The actual Dirichlet kernel in outward radial coordinates. -/
def outerOutwardDirichletKernel (D : ReferenceData) (right : Bool) (j : ℕ)
    (w u : ℝ → ℝ) (r t : ℝ) : ℝ :=
  outerTailOutwardLift D right j w (min r t) *
    outerTailOutwardLift D right j u (max r t)

private theorem outer_amplitude_pair {D : ReferenceData} {right : Bool}
    (hend : 0 < tailPhysicalEndpoint D right) (j : ℕ) (x y q p : ℝ) :
    outerPhysicalAmplitude D right j x * outerPhysicalAmplitude D right j y *
      ((outerLogGauge D right j x * q) * (outerLogGauge D right j y * p)) = 12 * (q * p) := by
  calc
    _ = (sqrt 12) ^ 2 * (q * p) := by
      unfold outerPhysicalAmplitude
      field_simp [(outerLogGauge_pos hend j x).ne', (outerLogGauge_pos hend j y).ne'] <;> ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]

theorem outerOutwardDirichletKernel_gauge {D : ReferenceData} {right : Bool}
    (hend : 0 < tailPhysicalEndpoint D right) (j : ℕ)
    (w u : ℝ → ℝ) (x y : ℝ) :
    outerPhysicalAmplitude D right j x * outerPhysicalAmplitude D right j y *
      outerOutwardDirichletKernel D right j w u
        (outerOutwardLogRadius right x) (outerOutwardLogRadius right y) =
      12 * (w (min x y) * u (max x y)) := by
  rw [outerOutwardDirichletKernel, outerOutwardLogRadius_min, outerOutwardLogRadius_max,
    outerTailOutwardLift_logRadius, outerTailOutwardLift_logRadius]
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy, max_eq_right hxy]
    exact outer_amplitude_pair hend j x y (w x) (u y)
  · rw [min_eq_right hyx, max_eq_left hyx,
      mul_comm (outerPhysicalAmplitude D right j x) (outerPhysicalAmplitude D right j y)]
    exact outer_amplitude_pair hend j y x (w y) (u x)

/-- All logarithmic L² source kernels transport to the actual outward inverse. -/
theorem outerOutwardGreenInverse_kernel
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T) (w u : ℝ → ℝ)
    (hG : ∀ f : DeepTailL2 T, (G f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x =>
      ∫ y, w (min x y) * u (max x y) * f y ∂deepTailMeasure T)
    (f : OuterOutwardTailL2 D T right) :
    (outerOutwardGreenInverse hD hphysical G f : ℝ → ℝ) =ᵐ[
      outerOutwardTailMeasure D T right] fun r =>
      ∫ t, outerOutwardDirichletKernel D right j w u r t * f t
        ∂outerOutwardTailMeasure D T right := by
  exact coordinateGauge_operator_kernel
    (measurableEmbedding_outerOutwardLogRadius right)
    (continuous_outerPhysicalAmplitude (tailPhysicalEndpoint_pos hD right) j).measurable
    (outerPhysicalAmplitude_pos (tailPhysicalEndpoint_pos hD right) j)
    (outerOutwardLogRadius_map_squareDensity hD hphysical)
    (outerOutwardLogEquiv hD hphysical) (outerOutwardLogEquiv_ae hD hphysical) G
    (outerOutwardGreenInverse hD hphysical G) (outerOutwardGreenInverse_conjugacy hD hphysical G)
    hG (Eventually.of_forall (fun x => Eventually.of_forall
      (outerOutwardDirichletKernel_gauge (tailPhysicalEndpoint_pos hD right) j w u x))) f

/-- Actual deep row integrability is preserved by the same exact gauge. -/
theorem outerOutwardDirichletKernel_row_memLp
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (w u : ℝ → ℝ) (x : ℝ)
    (hrow : MemLp (fun y => w (min x y) * u (max x y)) 2 (deepTailMeasure T)) :
    MemLp (outerOutwardDirichletKernel D right j w u (outerOutwardLogRadius right x))
      2 (outerOutwardTailMeasure D T right) :=
  coordinateGauge_kernel_row_memLp
    (measurableEmbedding_outerOutwardLogRadius right)
    (continuous_outerPhysicalAmplitude (tailPhysicalEndpoint_pos hD right) j).measurable
    (outerPhysicalAmplitude_pos (tailPhysicalEndpoint_pos hD right) j)
    (outerOutwardLogRadius_map_squareDensity hD hphysical) x
    (Eventually.of_forall
      (outerOutwardDirichletKernel_gauge (tailPhysicalEndpoint_pos hD right) j w u x)) hrow

end ContinuousFlexibility.Radial
