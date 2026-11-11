import ContinuousFlexibility.Radial.ReferenceCosineCoefficients

/-!
# Finite angular projections in the frozen weighted norms

A radial multiplier commutes with angular projection. Applying the fiber
contraction to each localized field proves contraction for every cell and
for either sign of the coefficient exponent.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

/-- A finite projection onto an arbitrary set of mean/cosine indices. -/
def referenceBasisProjection (I : Finset ℕ) (u : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  angularBasisProjection I (fun θ => u (x.1, θ)) x.2

theorem referenceBasisProjection_mul_radial (I : Finset ℕ) (a : ℝ → ℝ)
    (u : PolarPoint → ℝ) :
    referenceBasisProjection I (fun x => a x.1 * u x) =
      (fun x => a x.1 * referenceBasisProjection I u x) := by
  funext x
  simp only [referenceBasisProjection, angularBasisProjection,
    referenceAngularCoefficient_const_mul, Finset.mul_sum, mul_assoc]

theorem aestronglyMeasurable_referenceBasisProjection {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) (I : Finset ℕ) :
    AEStronglyMeasurable (referenceBasisProjection I u)
      (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  change AEStronglyMeasurable
    (fun x : PolarPoint => ∑ n ∈ I, referenceRadialCoefficient u n x.1 *
      referenceAngularBasis n x.2) _
  apply aestronglyMeasurable_fun_sum
  intro n _hn
  exact (aestronglyMeasurable_referenceRadialCoefficient hu n).comp_fst.mul
    (((contDiff_referenceAngularBasis n).continuous.comp continuous_snd).aestronglyMeasurable)

theorem integral_angularBasisProjection_sq_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (I : Finset ℕ) :
    (∫ θ, angularBasisProjection I f θ ^ 2
      ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) ≤
        ∫ θ, f θ ^ 2 ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)) := by
  have h := angularBasisProjection_sq_le hf I
  simp only [radialAngularMean,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] at h
  exact (mul_le_mul_left (show (0 : ℝ) < (2 * Real.pi)⁻¹ by positivity)).mp h

theorem memLp_referenceBasisProjection_prod {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) (I : Finset ℕ) :
    MemLp (referenceBasisProjection I u) 2
      (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  have hm := aestronglyMeasurable_referenceBasisProjection hu.aestronglyMeasurable I
  have hms := hm.pow_const 2
  have hinner : Integrable
      (fun r => ∫ θ, referenceBasisProjection I u (r, θ) ^ 2
        ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) μ := by
    apply hu.integrable_sq.integral_prod_left.mono' hms.integral_prod_right'
    filter_upwards [memLp_two_prod_sections hu] with r hr
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact integral_angularBasisProjection_sq_le hr I
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrable_prod_iff hms).mpr
  constructor
  · exact ae_of_all _ (fun r =>
      (memLp_referenceAngular_interval_of_continuous
        (continuous_angularBasisProjection I (fun θ => u (r, θ)))).integrable_sq)
  · simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hinner

theorem integral_referenceBasisProjection_sq_le_prod {μ : Measure ℝ} [SFinite μ]
    {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) (I : Finset ℕ) :
    (∫ x, referenceBasisProjection I u x ^ 2
      ∂μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) ≤
        ∫ x, u x ^ 2 ∂μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hp := memLp_referenceBasisProjection_prod hu I
  rw [integral_prod _ hp.integrable_sq, integral_prod _ hu.integrable_sq]
  apply integral_mono_ae hp.integrable_sq.integral_prod_left hu.integrable_sq.integral_prod_left
  filter_upwards [memLp_two_prod_sections hu] with r hr
  exact integral_angularBasisProjection_sq_le hr I

theorem referenceBasisProjection_cellIntegrable {D : ReferenceData}
    {u : PolarPoint → ℝ} (hu : RadialCellIntegrable D u) (I : Finset ℕ) :
    RadialCellIntegrable D (referenceBasisProjection I u) := by
  intro m
  have hm : MemLp (fun x : PolarPoint => D.localizer m x.1 * u x) 2
      ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hu m
  have hp := memLp_referenceBasisProjection_prod hm I
  simpa only [referenceBasisProjection_mul_radial, radialPhysicalMeasure_eq_prod] using hp

theorem referenceBasisProjection_cell_sq_le {D : ReferenceData} (hab : D.a ≤ D.b)
    {u : PolarPoint → ℝ} (hu : RadialCellIntegrable D u) (I : Finset ℕ) (m : ℕ) :
    referenceCellSquare D m (referenceBasisProjection I u) ≤ referenceCellSquare D m u := by
  have hm : MemLp (fun x : PolarPoint => D.localizer m x.1 * u x) 2
      ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hu m
  rw [referenceCellSquare_eq_integral hab m (referenceBasisProjection_cellIntegrable hu I),
    referenceCellSquare_eq_integral hab m hu, radialPhysicalMeasure_eq_prod]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [referenceBasisProjection_mul_radial] using
    integral_referenceBasisProjection_sq_le_prod hm I

theorem referenceCosineProjection_eq_basis (J : Finset ℕ) (u : PolarPoint → ℝ) :
    referenceCosineProjection J u = referenceBasisProjection (insert 0 (J.image Nat.succ)) u := by
  funext x
  exact congrFun (angularCosineProjection_eq_basis J (fun θ => u (x.1, θ))) x.2

theorem referenceCosineProjection_cellIntegrable {D : ReferenceData}
    {u : PolarPoint → ℝ} (hu : RadialCellIntegrable D u) (J : Finset ℕ) :
    RadialCellIntegrable D (referenceCosineProjection J u) := by
  rw [referenceCosineProjection_eq_basis]
  exact referenceBasisProjection_cellIntegrable hu _

theorem referenceCosineProjection_cell_sq_le {D : ReferenceData} (hab : D.a ≤ D.b)
    {u : PolarPoint → ℝ} (hu : RadialCellIntegrable D u) (J : Finset ℕ) (m : ℕ) :
    referenceCellSquare D m (referenceCosineProjection J u) ≤ referenceCellSquare D m u := by
  rw [referenceCosineProjection_eq_basis]
  exact referenceBasisProjection_cell_sq_le hab hu _ m

theorem referenceCosineProjection_source_summable {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {u : PolarPoint → ℝ} (hu : RadialCellIntegrable D u)
    (hs : Summable (sourceCellSquare D γ M u)) (J : Finset ℕ) :
    Summable (sourceCellSquare D γ M (referenceCosineProjection J u)) := by
  apply Summable.of_nonneg_of_le _ _ hs
  · intro m
    exact mul_nonneg (Real.exp_pos _).le
      (referenceCellSquare_nonneg hab m (referenceCosineProjection_cellIntegrable hu J))
  · intro m
    exact mul_le_mul_of_nonneg_left (referenceCosineProjection_cell_sq_le hab hu J m)
      (Real.exp_pos _).le

theorem referenceCosineProjection_output_summable {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {u : PolarPoint → ℝ} (hu : RadialCellIntegrable D u)
    (hs : Summable (outputCellSquare D γ M u)) (J : Finset ℕ) :
    Summable (outputCellSquare D γ M (referenceCosineProjection J u)) := by
  apply Summable.of_nonneg_of_le _ _ hs
  · intro m
    exact mul_nonneg (Real.exp_pos _).le
      (referenceCellSquare_nonneg hab m (referenceCosineProjection_cellIntegrable hu J))
  · intro m
    exact mul_le_mul_of_nonneg_left (referenceCosineProjection_cell_sq_le hab hu J m)
      (Real.exp_pos _).le

theorem referenceCosineProjection_source_tsum_le {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {u : PolarPoint → ℝ} (hu : RadialCellIntegrable D u)
    (hs : Summable (sourceCellSquare D γ M u)) (J : Finset ℕ) :
    (∑' m, sourceCellSquare D γ M (referenceCosineProjection J u) m) ≤
      ∑' m, sourceCellSquare D γ M u m := by
  apply Summable.tsum_le_tsum
    (fun m => mul_le_mul_of_nonneg_left (referenceCosineProjection_cell_sq_le hab hu J m)
      (Real.exp_pos _).le)
    (referenceCosineProjection_source_summable hab hu hs J) hs

theorem referenceCosineProjection_output_tsum_le {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {u : PolarPoint → ℝ} (hu : RadialCellIntegrable D u)
    (hs : Summable (outputCellSquare D γ M u)) (J : Finset ℕ) :
    (∑' m, outputCellSquare D γ M (referenceCosineProjection J u) m) ≤
      ∑' m, outputCellSquare D γ M u m := by
  apply Summable.tsum_le_tsum
    (fun m => mul_le_mul_of_nonneg_left (referenceCosineProjection_cell_sq_le hab hu J m)
      (Real.exp_pos _).le)
    (referenceCosineProjection_output_summable hab hu hs J) hs

end

end ContinuousFlexibility.Radial
