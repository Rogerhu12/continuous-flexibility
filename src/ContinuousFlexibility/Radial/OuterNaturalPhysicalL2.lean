import ContinuousFlexibility.Radial.OuterNaturalPhysicalPoisson
import ContinuousFlexibility.Radial.OuterPhysicalMeasure

/-!
# The natural solution in the original radial Hilbert space

The change of variables uses the actual physical density 12w/r².
The signed logarithmic gauge is handled by exact measure transport,
and the resulting function is proved to belong to the physical L² space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Positivity of the actual logarithmic density places its entire
half-open tail inside the original positive radial annulus. -/
theorem morsePhysicalDeepTail_radius_mem_core
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ}
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {x : ℝ} (hx : x ∈ Ico
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint) :
    tailPhysicalRadius right x ∈ radialCore D := by
  have hp := (deepTail_pos hT x hx).ne'
  have hw : D.w (tailPhysicalRadius right x) ≠ 0 := by
    intro hz
    apply hp
    change (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (2 * j ^ 2) *
      D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x = 0
    rw [hz, mul_zero, zero_div]
  constructor
  · by_contra h
    exact hw (hD.2.2.1.2 _ (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hw (hD.2.2.1.2 _ (Or.inr (le_of_not_gt h)))

theorem morsePhysicalDeepTail_square_density (M : MorseChainData) (D : ReferenceData)
    (right : Bool) (j start : ℕ) (entrance η K : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    (12 * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x) *
        tailPhysicalLift D right j u (tailPhysicalRadius right x) ^ 2 =
      12 * ((morsePhysicalDeepTail M D right j start entrance η K).p x * u x ^ 2) := by
  rw [tailPhysicalLift_radius]
  have hcast : (j : ℝ) ^ 2 = ((j ^ 2 : ℕ) : ℝ) := by simp
  rw [hcast, rpow_natCast, mul_pow, ← pow_mul, Nat.mul_comm (j ^ 2) 2]
  change (12 * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x) *
      ((tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (2 * j ^ 2) * u x ^ 2) =
    12 * (((tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (2 * j ^ 2) *
      D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x) * u x ^ 2)
  ring

/-- Exact squared-norm transport, with the factor twelve and both
orientations retained. -/
theorem morsePhysicalDeepTail_integral_lift_sq
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ}
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (u : ℝ → ℝ) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    (∫ r, tailPhysicalLift D right j u r ^ 2 ∂outerRadialIntervalMeasure D
      (tailPhysicalRadius right '' Ioo T.entrance T.endpoint)) =
      12 * (∫ x, u x ^ 2 ∂deepTailMeasure T) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let q : ℝ → ℝ := fun x => 12 * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x
  have hq : Continuous q :=
    (continuous_const.mul (hD.2.2.1.1.continuous.comp
      (continuous_tailPhysicalRadius right))).div
        (continuous_tailPhysicalRadius right) (fun x => (tailPhysicalRadius_pos right x).ne')
  have hqpos (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) : 0 < q x :=
    div_pos (mul_pos (by norm_num) (hD.2.2.2.2.1 _
      (morsePhysicalDeepTail_radius_mem_core hD hT (Ioo_subset_Ico_self hx))))
      (tailPhysicalRadius_pos right x)
  calc
    _ = ∫ x, tailPhysicalLift D right j u (tailPhysicalRadius right x) ^ 2
        ∂outerPhysicalPullbackMeasure D T right := by
      rw [← outerPhysicalPullbackMeasure_map]
      exact (measurableEmbedding_tailPhysicalRadius right).integral_map _
    _ = ∫ x in Ioo T.entrance T.endpoint,
        q x * tailPhysicalLift D right j u (tailPhysicalRadius right x) ^ 2 := by
      rw [outerPhysicalPullbackMeasure, integral_withDensity_eq_integral_toReal_smul₀
        hq.measurable.ennreal_ofReal.aemeasurable (by simp)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simp only [ENNReal.toReal_ofReal (hqpos x hx).le, smul_eq_mul]
    _ = ∫ x in Ioo T.entrance T.endpoint, 12 * (T.p x * u x ^ 2) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (morsePhysicalDeepTail_square_density M D right j start entrance η K u)
    _ = 12 * (∫ x, u x ^ 2 ∂deepTailMeasure T) := by
      rw [integral_const_mul, tail_integral_density
        ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
        (fun x hx => deepTail_pos hT x (Ioo_subset_Ico_self hx))]

/-- Square integrability is transported as an actual integrability
statement, so the norm identity cannot be vacuous through a zero
integral of a nonintegrable function. -/
theorem morsePhysicalDeepTail_integrable_lift_sq
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ}
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u : ℝ → ℝ}
    (hu : MemLp u 2 (deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K))) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    Integrable (fun r => tailPhysicalLift D right j u r ^ 2)
      (outerRadialIntervalMeasure D
        (tailPhysicalRadius right '' Ioo T.entrance T.endpoint)) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let q : ℝ → ℝ := fun x => 12 * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x
  have hq : Continuous q :=
    (continuous_const.mul (hD.2.2.1.1.continuous.comp
      (continuous_tailPhysicalRadius right))).div
        (continuous_tailPhysicalRadius right) (fun x => (tailPhysicalRadius_pos right x).ne')
  have hqpos (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) : 0 < q x :=
    div_pos (mul_pos (by norm_num) (hD.2.2.2.2.1 _
      (morsePhysicalDeepTail_radius_mem_core hD hT (Ioo_subset_Ico_self hx))))
      (tailPhysicalRadius_pos right x)
  have hi : IntegrableOn (fun x => T.p x * u x ^ 2) (Ioo T.entrance T.endpoint) :=
    (tail_integrable_density_iff ((deepTail_contDiffOn hT).mono Ioo_subset_Ico_self)
      (fun x hx => deepTail_pos hT x (Ioo_subset_Ico_self hx)) _).mp hu.integrable_sq
  rw [← outerPhysicalPullbackMeasure_map,
    (measurableEmbedding_tailPhysicalRadius right).integrable_map_iff,
    outerPhysicalPullbackMeasure, integrable_withDensity_iff_integrable_smul'
      hq.measurable.ennreal_ofReal (by simp)]
  apply (hi.const_mul 12).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (hqpos x hx).le, smul_eq_mul]
  exact (morsePhysicalDeepTail_square_density M D right j start entrance η K u x).symm

theorem morsePhysicalDeepTail_lift_memLp
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ}
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u : ℝ → ℝ}
    (hu : TailNaturalEquation (morsePhysicalDeepTail M D right j start entrance η K) u) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    MemLp (tailPhysicalLift D right j u) 2
      (outerRadialIntervalMeasure D
        (tailPhysicalRadius right '' Ioo T.entrance T.endpoint)) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let s := tailPhysicalRadius right '' Ioo T.entrance T.endpoint
  have hs : MeasurableSet s :=
    (measurableEmbedding_tailPhysicalRadius right).measurableSet_image.mpr measurableSet_Ioo
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hc : ContinuousOn (tailPhysicalLift D right j u) s := by
    rintro r ⟨x, hx, rfl⟩
    apply ContinuousAt.continuousWithinAt
    apply ContDiffAt.continuousAt
    apply contDiffAt_tailPhysicalLift hend.ne' (tailPhysicalRadius_pos right x)
    simpa only [tailPhysicalLog_radius] using tailNatural_contDiffAt hu hx
  have hm : AEStronglyMeasurable (tailPhysicalLift D right j u)
      (outerRadialIntervalMeasure D s) :=
    AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous (volume.restrict s)
        (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2)))
      (hc.aestronglyMeasurable hs)
  exact (memLp_two_iff_integrable_sq hm).mpr
    (morsePhysicalDeepTail_integrable_lift_sq hD hT hu.2.2.1)

theorem outerNatural_toLp_norm_sq {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, pow_two]


theorem outerNatural_toLp_norm_le {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) {scale exponent : ℝ} (hscale : 0 ≤ scale) (n : ℕ)
    (hbound : (∫ x, f x ^ 2 ∂μ) ≤ scale * exp (exponent * (n : ℝ) ^ 2)) :
    ‖hf.toLp f‖ ≤ sqrt scale * exp ((exponent / 2) * (n : ℝ) ^ 2) := by
  have hsquare : (sqrt scale * exp ((exponent / 2) * (n : ℝ) ^ 2)) ^ 2 =
      scale * exp (exponent * (n : ℝ) ^ 2) := by
    rw [mul_pow, sq_sqrt hscale, pow_two, ← exp_add]
    congr 2
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (exp_pos _).le)).mp
  rw [hsquare, outerNatural_toLp_norm_sq]
  exact hbound

/-- The physical L² norm follows from the actual integral after the
change of variables. -/
theorem morsePhysicalDeepTail_lift_norm_le
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ}
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u : ℝ → ℝ}
    (hu : TailNaturalEquation (morsePhysicalDeepTail M D right j start entrance η K) u)
    {scale exponent : ℝ} (hscale : 0 ≤ scale) (n : ℕ)
    (hbound : 12 * (∫ x, u x ^ 2
      ∂deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K)) ≤
        scale * exp (exponent * (n : ℝ) ^ 2)) :
    ‖(morsePhysicalDeepTail_lift_memLp hD hT hu).toLp (tailPhysicalLift D right j u)‖ ≤
      sqrt scale * exp ((exponent / 2) * (n : ℝ) ^ 2) := by
  apply outerNatural_toLp_norm_le _ hscale n
  rw [morsePhysicalDeepTail_integral_lift_sq hD hT]
  exact hbound


/-- The image measure is exactly the original radial Hilbert measure
restricted to the selected tail; no physical localization assumption
is needed for the actual data. -/
theorem morsePhysicalDeepTail_interval_measure_eq
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ} (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K)) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    outerRadialIntervalMeasure D (tailPhysicalRadius right '' Ioo T.entrance T.endpoint) =
      (radialHilbertMeasure D).restrict (radialTailInterval D right entrance) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have himage : tailPhysicalRadius right '' Ioo T.entrance T.endpoint =
      radialTailInterval D right entrance := by
    cases right with
    | true =>
        change exp '' Ioo (log entrance) (log D.b) = Ioo entrance D.b
        rw [image_exp_Ioo, exp_log hentry, exp_log (hD.1.trans hD.2.1)]
    | false =>
        have hn : Neg.neg '' Ioo (-log entrance) (-log D.a) =
            Ioo (log D.a) (log entrance) := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            constructor <;> linarith only [hy.1, hy.2]
          · intro hx
            refine ⟨-x, ⟨by linarith only [hx.2], by linarith only [hx.1]⟩, neg_neg x⟩
        change (exp ∘ Neg.neg) '' Ioo (-log entrance) (-log D.a) = Ioo D.a entrance
        calc
          _ = exp '' (Neg.neg '' Ioo (-log entrance) (-log D.a)) := by rw [Set.image_image]
          _ = _ := by rw [hn, image_exp_Ioo, exp_log hD.1, exp_log hentry]
  have hs : MeasurableSet (tailPhysicalRadius right '' Ioo T.entrance T.endpoint) :=
    (measurableEmbedding_tailPhysicalRadius right).measurableSet_image.mpr measurableSet_Ioo
  have hsub : tailPhysicalRadius right '' Ioo T.entrance T.endpoint ⊆ radialCore D := by
    rintro r ⟨x, hx, rfl⟩
    exact morsePhysicalDeepTail_radius_mem_core hD hT (Ioo_subset_Ico_self hx)
  rw [← himage, radialHilbertMeasure, restrict_withDensity hs,
    Measure.restrict_restrict hs, inter_eq_left.mpr hsub]
  rfl

theorem morsePhysicalDeepTail_lift_memLp_radial
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ} (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u : ℝ → ℝ}
    (hu : TailNaturalEquation (morsePhysicalDeepTail M D right j start entrance η K) u) :
    MemLp (tailPhysicalLift D right j u) 2
      ((radialHilbertMeasure D).restrict (radialTailInterval D right entrance)) := by
  rw [← morsePhysicalDeepTail_interval_measure_eq hD hentry hT]
  exact morsePhysicalDeepTail_lift_memLp hD hT hu

theorem morsePhysicalDeepTail_lift_radial_norm_le
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ} (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u : ℝ → ℝ}
    (hu : TailNaturalEquation (morsePhysicalDeepTail M D right j start entrance η K) u)
    {scale exponent : ℝ} (hscale : 0 ≤ scale) (n : ℕ)
    (hbound : 12 * (∫ x, u x ^ 2
      ∂deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K)) ≤
        scale * exp (exponent * (n : ℝ) ^ 2)) :
    ‖(morsePhysicalDeepTail_lift_memLp_radial hD hentry hT hu).toLp
      (tailPhysicalLift D right j u)‖ ≤
        sqrt scale * exp ((exponent / 2) * (n : ℝ) ^ 2) := by
  apply outerNatural_toLp_norm_le _ hscale n
  have hi := morsePhysicalDeepTail_integral_lift_sq hD hT u
  rw [morsePhysicalDeepTail_interval_measure_eq hD hentry hT] at hi
  rw [hi]
  exact hbound

end ContinuousFlexibility.Radial
