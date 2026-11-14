module

public import ContinuousFlexibility.Radial.OuterPhysicalInverse

/-!
# The physical inverse in the outward radial coordinate

At the left endpoint the outward coordinate is minus the original
radius. Both the measure and the operator are reflected together.
The reflection has absolute Jacobian one and gives an actual L2 isometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def outerOutwardRadius (right : Bool) (r : ℝ) : ℝ := if right then r else -r

@[simp] theorem outerOutwardRadius_twice (right : Bool) (r : ℝ) :
    outerOutwardRadius right (outerOutwardRadius right r) = r := by
  cases right <;> simp [outerOutwardRadius]

theorem measurableEmbedding_outerOutwardRadius (right : Bool) :
    MeasurableEmbedding (outerOutwardRadius right) := by
  cases right
  · exact (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  · exact MeasurableEmbedding.id

theorem outerOutwardRadius_lintegral_change (right : Bool) {s : Set ℝ}
    (hs : MeasurableSet s) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in outerOutwardRadius right '' s, f x) =
      ∫⁻ r in s, f (outerOutwardRadius right r) := by
  have hd (r : ℝ) : HasDerivAt (outerOutwardRadius right) (if right then 1 else -1) r := by
    cases right
    · exact hasDerivAt_neg r
    · exact hasDerivAt_id r
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun r _ => (hd r).hasDerivWithinAt) (measurableEmbedding_outerOutwardRadius right).injective.injOn f
  have hc : |if right then (1 : ℝ) else -1| = 1 := by cases right <;> norm_num
  simpa only [hc, ENNReal.ofReal_one, one_mul] using hh

def outerOutwardIntervalMeasure (D : ReferenceData) (right : Bool) (s : Set ℝ) : Measure ℝ :=
  (volume.restrict (outerOutwardRadius right '' s)).withDensity
    (fun x => ENNReal.ofReal (12 * D.w (outerOutwardRadius right x) / x ^ 2))

theorem outerOutwardIntervalMeasure_map (D : ReferenceData) (right : Bool)
    {s : Set ℝ} (hs : MeasurableSet s) :
    Measure.map (outerOutwardRadius right) (outerRadialIntervalMeasure D s) =
      outerOutwardIntervalMeasure D right s := by
  ext t ht
  have he := measurableEmbedding_outerOutwardRadius right
  have hpre := he.measurable ht
  rw [Measure.map_apply he.measurable ht, outerRadialIntervalMeasure, withDensity_apply _ hpre]
  calc
    _ = ∫⁻ r in s, t.indicator
        (fun x => ENNReal.ofReal (12 * D.w (outerOutwardRadius right x) / x ^ 2))
          (outerOutwardRadius right r) := by
      rw [← lintegral_indicator hpre]
      apply lintegral_congr
      intro r
      by_cases hr : outerOutwardRadius right r ∈ t
      · rw [indicator_of_mem (show r ∈ outerOutwardRadius right ⁻¹' t from hr),
          indicator_of_mem hr, outerOutwardRadius_twice]
        congr 1
        cases right <;> simp [outerOutwardRadius]
      · rw [indicator_of_notMem (show r ∉ outerOutwardRadius right ⁻¹' t from hr),
          indicator_of_notMem hr]
    _ = ∫⁻ x in outerOutwardRadius right '' s,
        t.indicator (fun x => ENNReal.ofReal (12 * D.w (outerOutwardRadius right x) / x ^ 2)) x :=
      (outerOutwardRadius_lintegral_change right hs _).symm
    _ = _ := by
      rw [lintegral_indicator ht, outerOutwardIntervalMeasure, withDensity_apply _ ht]

def outerOutwardTailMeasure (D : ReferenceData) (T : DeepTailData) (right : Bool) : Measure ℝ :=
  Measure.map (outerOutwardRadius right) ((radialHilbertMeasure D).restrict
    (radialTailInterval D right (tailPhysicalRadius right T.entrance)))

abbrev OuterOutwardTailL2 (D : ReferenceData) (T : DeepTailData) (right : Bool) :=
  Lp ℝ 2 (outerOutwardTailMeasure D T right)

theorem outerOutward_tail_image (D : ReferenceData) (right : Bool) (entry : ℝ) :
    outerOutwardRadius right '' radialTailInterval D right entry =
      Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)) := by
  cases right
  · change Neg.neg '' Ioo D.a entry = Ioo (-entry) (-D.a)
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      constructor <;> linarith [hr.1, hr.2]
    · intro hx
      exact ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, neg_neg x⟩
  · change id '' Ioo entry D.b = Ioo entry D.b
    exact Set.image_id _

/-- The outward measure has the actual density 12 w_o/r_o² on its
increasing outward interval, with no orientation sign in the measure. -/
theorem outerOutwardTailMeasure_eq_density
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start) :
    outerOutwardTailMeasure D T right =
      (volume.restrict (Ioo (outerOutwardRadius right (tailPhysicalRadius right T.entrance))
        (outerOutwardRadius right (tailPhysicalEndpoint D right)))).withDensity
          (fun x => ENNReal.ofReal (12 * D.w (outerOutwardRadius right x) / x ^ 2)) := by
  have hi := outerPhysicalPullbackMeasure_map D T right
  rw [tailPhysicalRadius_image hD hphysical] at hi
  have hm : outerRadialIntervalMeasure D
      (radialTailInterval D right (tailPhysicalRadius right T.entrance)) =
        (radialHilbertMeasure D).restrict
          (radialTailInterval D right (tailPhysicalRadius right T.entrance)) :=
    hi.symm.trans (outerPhysicalPullbackMeasure_map_radial hD hphysical)
  have hs : MeasurableSet (radialTailInterval D right (tailPhysicalRadius right T.entrance)) := by
    cases right <;> exact measurableSet_Ioo
  rw [outerOutwardTailMeasure, ← hm, outerOutwardIntervalMeasure_map D right hs,
    outerOutwardIntervalMeasure, outerOutward_tail_image]

def outerOutwardTailEquiv (D : ReferenceData) (T : DeepTailData) (right : Bool) :
    OuterOutwardTailL2 D T right ≃ₗᵢ[ℝ] OuterPhysicalTailL2 D T right :=
  coordinateL2Equiv _ (outerOutwardRadius right) (outerOutwardRadius right)
    (measurableEmbedding_outerOutwardRadius right) (outerOutwardRadius_twice right)

theorem outerOutwardTailEquiv_ae (D : ReferenceData) (T : DeepTailData) (right : Bool)
    (f : OuterOutwardTailL2 D T right) :
    outerOutwardTailEquiv D T right f =ᵐ[(radialHilbertMeasure D).restrict
      (radialTailInterval D right (tailPhysicalRadius right T.entrance))]
        fun r => f (outerOutwardRadius right r) :=
  coordinateL2Equiv_ae _ (outerOutwardRadius right) (outerOutwardRadius right)
    (measurableEmbedding_outerOutwardRadius right) (outerOutwardRadius_twice right) f

def outerOutwardOperator (D : ReferenceData) (T : DeepTailData) (right : Bool)
    (A : OuterPhysicalTailL2 D T right →L[ℝ] OuterPhysicalTailL2 D T right) :
    OuterOutwardTailL2 D T right →L[ℝ] OuterOutwardTailL2 D T right :=
  (outerOutwardTailEquiv D T right).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp (outerOutwardTailEquiv D T right).toContinuousLinearEquiv.toContinuousLinearMap)

theorem outerOutwardOperator_apply (D : ReferenceData) (T : DeepTailData) (right : Bool)
    (A : OuterPhysicalTailL2 D T right →L[ℝ] OuterPhysicalTailL2 D T right)
    (f : OuterOutwardTailL2 D T right) :
    outerOutwardTailEquiv D T right (outerOutwardOperator D T right A f) =
      A (outerOutwardTailEquiv D T right f) :=
  (outerOutwardTailEquiv D T right).apply_symm_apply _

theorem outerOutwardOperator_norm_le (D : ReferenceData) (T : DeepTailData) (right : Bool)
    (A : OuterPhysicalTailL2 D T right →L[ℝ] OuterPhysicalTailL2 D T right) :
    ‖outerOutwardOperator D T right A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  rw [← (outerOutwardTailEquiv D T right).norm_map (outerOutwardOperator D T right A f),
    outerOutwardOperator_apply]
  exact (A.le_opNorm _).trans_eq
    (congrArg (fun t => ‖A‖ * t) ((outerOutwardTailEquiv D T right).norm_map f))

/-- The same constructed Dirichlet inverse, in the outward Hilbert space. -/
theorem exists_outerOutwardDirichletInverse
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hT : DeepTailHypotheses T)
    (hphysical : TailPhysicalRelation D T right j start) (hj : 2 ≤ j)
    (hη : T.η ≤ 1 / 10) (hK : 10 * tailSmoothStepConstant + 2 ≤ T.K) :
    ∃ A : OuterOutwardTailL2 D T right →L[ℝ] OuterOutwardTailL2 D T right,
      ‖A‖ ≤ 64 / (j : ℝ) ^ 4 ∧
      (∀ f, OuterPhysicalDirichletGraph hD hphysical
        (outerOutwardTailEquiv D T right (A f)) (outerOutwardTailEquiv D T right f)) ∧
      (∀ u f, OuterPhysicalDirichletGraph hD hphysical
        (outerOutwardTailEquiv D T right u) (outerOutwardTailEquiv D T right f) → A f = u) := by
  obtain ⟨A, hA, he, hu⟩ := exists_outerPhysicalDirichletInverse hD hT hphysical hj hη hK
  refine ⟨outerOutwardOperator D T right A,
    (outerOutwardOperator_norm_le D T right A).trans hA, ?_, ?_⟩
  · intro f
    rw [outerOutwardOperator_apply]
    exact he _
  · intro u f hf
    apply (outerOutwardTailEquiv D T right).injective
    rw [outerOutwardOperator_apply]
    exact hu _ _ hf

end ContinuousFlexibility.Radial
