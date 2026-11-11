import ContinuousFlexibility.Radial.ReferenceCellL2
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Hilbert realization of the reference cell norms

The measure is the sum of the actual localized measures, including the
normalization of angular averaging. Its L² norm is exactly the frozen
sum of cell squares. The output remainder uses the same construction
with the negative coefficient exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace

/-- The square weight, including the normalization of angular averaging. -/
def referenceCellMeasureWeight (D : ReferenceData) (γ M : ℝ) (m : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    Real.exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))

theorem referenceCellMeasureWeight_pos (D : ReferenceData) (γ M : ℝ) (m : ℕ) :
    0 < referenceCellMeasureWeight D γ M m := by
  unfold referenceCellMeasureWeight
  positivity

def referenceCellMeasureDensity (D : ReferenceData) (γ M : ℝ) (m : ℕ)
    (x : PolarPoint) : ℝ≥0∞ :=
  ENNReal.ofReal (referenceCellMeasureWeight D γ M m * (D.localizer m x.1) ^ 2)

def referenceWeightedCellMeasure (D : ReferenceData) (γ M : ℝ) (m : ℕ) :
    Measure PolarPoint :=
  (radialPhysicalMeasure D).withDensity (referenceCellMeasureDensity D γ M m)

def referenceWeightedMeasure (D : ReferenceData) (γ M : ℝ) : Measure PolarPoint :=
  Measure.sum (referenceWeightedCellMeasure D γ M)

theorem referenceCellMeasureDensity_measurable {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) (m : ℕ) :
    Measurable (referenceCellMeasureDensity D γ M m) := by
  have hm : Measurable (fun x : PolarPoint => D.localizer m x.1) :=
    (hD.1 m).continuous.measurable.comp measurable_fst
  exact (measurable_const.mul (hm.pow_const 2)).ennreal_ofReal

theorem referenceCellMeasureDensity_lt_top (D : ReferenceData)
    (γ M : ℝ) (m : ℕ) (x : PolarPoint) :
    referenceCellMeasureDensity D γ M m x < ∞ :=
  ENNReal.ofReal_lt_top

theorem referenceCellMeasureDensity_mul_sq (D : ReferenceData)
    (γ M : ℝ) (m : ℕ) (f : PolarPoint → ℝ) (x : PolarPoint) :
    (referenceCellMeasureDensity D γ M m x).toReal * f x ^ 2 =
      referenceCellMeasureWeight D γ M m * (D.localizer m x.1 * f x) ^ 2 := by
  unfold referenceCellMeasureDensity
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (referenceCellMeasureWeight_pos D γ M m).le (sq_nonneg _))]
  ring

theorem integral_sq_referenceWeightedCellMeasure {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) (m : ℕ) (f : PolarPoint → ℝ) :
    (∫ x, f x ^ 2 ∂referenceWeightedCellMeasure D γ M m) =
      referenceCellMeasureWeight D γ M m *
        ∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D := by
  unfold referenceWeightedCellMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (referenceCellMeasureDensity_measurable hD γ M m)
    (ae_of_all _ (referenceCellMeasureDensity_lt_top D γ M m))]
  simp only [smul_eq_mul, referenceCellMeasureDensity_mul_sq]
  exact integral_const_mul _ _

theorem integrable_sq_referenceWeightedCellMeasure {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) (m : ℕ)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) :
    Integrable (fun x => f x ^ 2) (referenceWeightedCellMeasure D γ M m) := by
  unfold referenceWeightedCellMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (referenceCellMeasureDensity_measurable hD γ M m)
    (ae_of_all _ (referenceCellMeasureDensity_lt_top D γ M m))]
  simpa only [smul_eq_mul, referenceCellMeasureDensity_mul_sq] using
    (hf m).integrable_sq.const_mul (referenceCellMeasureWeight D γ M m)

theorem integral_sq_referenceWeightedCellMeasure_eq {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) (γ M : ℝ) (m : ℕ)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) :
    (∫ x, f x ^ 2 ∂referenceWeightedCellMeasure D γ M m) =
      sourceCellSquare D γ M f m := by
  rw [integral_sq_referenceWeightedCellMeasure hD]
  unfold sourceCellSquare referenceCellMeasureWeight
  rw [referenceCellSquare_eq_integral hab m hf]
  ring

/-- Summability in the frozen definition is integrability for the sum measure. -/
theorem integrable_sq_referenceWeightedMeasure {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ}
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (hs : Summable (sourceCellSquare D γ M f)) :
    Integrable (fun x => f x ^ 2) (referenceWeightedMeasure D γ M) := by
  apply integrable_sum_measure
    (fun m => integrable_sq_referenceWeightedCellMeasure hD γ M m hf)
  simpa only [Real.norm_of_nonneg (sq_nonneg _),
    integral_sq_referenceWeightedCellMeasure_eq hab hD γ M _ hf] using hs

theorem RadialCellIntegrable.aestronglyMeasurable_weighted {D : ReferenceData}
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (hD : RadialPartition D)
    (γ M : ℝ) : AEStronglyMeasurable f (referenceWeightedMeasure D γ M) := by
  apply aestronglyMeasurable_sum_measure_iff.mpr
  intro m
  exact (hf.aestronglyMeasurable hD).mono_ac
    (withDensity_absolutelyContinuous (radialPhysicalMeasure D)
      (referenceCellMeasureDensity D γ M m))

theorem memLp_referenceWeightedMeasure {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ}
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (hs : Summable (sourceCellSquare D γ M f)) :
    MemLp f 2 (referenceWeightedMeasure D γ M) :=
  (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable_weighted hD γ M)).2
    (integrable_sq_referenceWeightedMeasure hab hD hf hs)

theorem integral_sq_referenceWeightedMeasure_eq {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ}
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (hs : Summable (sourceCellSquare D γ M f)) :
    (∫ x, f x ^ 2 ∂referenceWeightedMeasure D γ M) =
      ∑' m, sourceCellSquare D γ M f m := by
  rw [integral_sum_measure (integrable_sq_referenceWeightedMeasure hab hD hf hs)]
  exact tsum_congr (fun m => integral_sq_referenceWeightedCellMeasure_eq hab hD γ M m hf)

/-- The actual Hilbert-space representative of a source field. -/
def referenceWeightedL2 {D : ReferenceData} (hab : D.a ≤ D.b)
    (hD : RadialPartition D) {γ M : ℝ} (f : PolarPoint → ℝ)
    (hf : RadialCellIntegrable D f) (hs : Summable (sourceCellSquare D γ M f)) :
    Lp ℝ 2 (referenceWeightedMeasure D γ M) :=
  (memLp_referenceWeightedMeasure hab hD hf hs).toLp f

theorem referenceWeightedL2_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    (hD : RadialPartition D) {γ M : ℝ} (f : PolarPoint → ℝ)
    (hf : RadialCellIntegrable D f) (hs : Summable (sourceCellSquare D γ M f)) :
    (referenceWeightedL2 hab hD f hf hs : PolarPoint → ℝ) =ᵐ[referenceWeightedMeasure D γ M] f :=
  (memLp_referenceWeightedMeasure hab hD hf hs).coeFn_toLp

theorem referenceWeightedL2_norm_sq {D : ReferenceData} (hab : D.a ≤ D.b)
    (hD : RadialPartition D) {γ M : ℝ} (f : PolarPoint → ℝ)
    (hf : RadialCellIntegrable D f) (hs : Summable (sourceCellSquare D γ M f)) :
    ‖referenceWeightedL2 hab hD f hf hs‖ ^ 2 =
      ∑' m, sourceCellSquare D γ M f m := by
  have hnorm : ‖referenceWeightedL2 hab hD f hf hs‖ ^ 2 =
      ∫ x, (referenceWeightedL2 hab hD f hf hs x) ^ 2
        ∂referenceWeightedMeasure D γ M := by
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using
      L2.inner_def (𝕜 := ℝ) (referenceWeightedL2 hab hD f hf hs)
        (referenceWeightedL2 hab hD f hf hs)
  rw [hnorm, ← integral_sq_referenceWeightedMeasure_eq hab hD hf hs]
  apply integral_congr_ae
  filter_upwards [referenceWeightedL2_ae hab hD f hf hs] with x hx
  exact congrArg (fun z : ℝ => z ^ 2) hx


/-- The weighted and physical measures have exactly the same null sets.
Positivity follows from the actual partition, not from a lower bound
assumed for the weight. -/
theorem referenceWeightedMeasure_ae_iff {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) {p : PolarPoint → Prop} :
    (∀ᵐ x ∂referenceWeightedMeasure D γ M, p x) ↔
      ∀ᵐ x ∂radialPhysicalMeasure D, p x := by
  constructor
  · intro h
    have hcell := Measure.ae_sum_iff.mp h
    have hbase (m : ℕ) : ∀ᵐ x ∂radialPhysicalMeasure D,
        referenceCellMeasureDensity D γ M m x ≠ 0 → p x :=
      (ae_withDensity_iff (referenceCellMeasureDensity_measurable hD γ M m)).mp (hcell m)
    have hall : ∀ᵐ x ∂radialPhysicalMeasure D, ∀ m,
        referenceCellMeasureDensity D γ M m x ≠ 0 → p x := ae_all_iff.2 hbase
    have hmem : ∀ᵐ x ∂radialPhysicalMeasure D,
        x ∈ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
    filter_upwards [hall, hmem] with x hx hxmem
    obtain ⟨m, hm⟩ := hD.exists_localizer_ne_zero hxmem.1
    apply hx m
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr
      (mul_pos (referenceCellMeasureWeight_pos D γ M m) (sq_pos_of_ne_zero hm))
  · intro h
    apply Measure.ae_sum_iff.mpr
    intro m
    apply (ae_withDensity_iff (referenceCellMeasureDensity_measurable hD γ M m)).mpr
    exact h.mono (fun _ hp _ => hp)

theorem radialPhysicalMeasure_absolutelyContinuous_weighted {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) :
    radialPhysicalMeasure D ≪ referenceWeightedMeasure D γ M := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  have hnot : ∀ᵐ x ∂referenceWeightedMeasure D γ M, x ∉ s := by
    simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hs0
  have hp := (referenceWeightedMeasure_ae_iff hD γ M).mp hnot
  simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hp

theorem radialCellIntegrable_of_memLp_weighted {D : ReferenceData}
    (hD : RadialPartition D) {γ M : ℝ} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (referenceWeightedMeasure D γ M)) :
    RadialCellIntegrable D f := by
  have hfm : AEStronglyMeasurable f (radialPhysicalMeasure D) :=
    hf.aestronglyMeasurable.mono_ac (radialPhysicalMeasure_absolutelyContinuous_weighted hD γ M)
  intro m
  have hm : AEStronglyMeasurable (fun x : PolarPoint => D.localizer m x.1 * f x)
      (radialPhysicalMeasure D) :=
    ((hD.1 m).continuous.comp continuous_fst).aestronglyMeasurable.mul hfm
  apply (memLp_two_iff_integrable_sq hm).mpr
  have hi : Integrable (fun x => f x ^ 2) (referenceWeightedCellMeasure D γ M m) :=
    hf.integrable_sq.mono_measure (Measure.le_sum (referenceWeightedCellMeasure D γ M) m)
  have hmul := (integrable_withDensity_iff_integrable_smul'
    (referenceCellMeasureDensity_measurable hD γ M m)
    (ae_of_all _ (referenceCellMeasureDensity_lt_top D γ M m))).mp hi
  have hscale := hmul.const_mul (referenceCellMeasureWeight D γ M m)⁻¹
  simpa only [smul_eq_mul, referenceCellMeasureDensity_mul_sq, ← mul_assoc,
    inv_mul_cancel₀ (referenceCellMeasureWeight_pos D γ M m).ne', one_mul] using hscale

theorem memLp_referenceWeightedMeasure_iff {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ} {f : PolarPoint → ℝ} :
    MemLp f 2 (referenceWeightedMeasure D γ M) ↔
      RadialCellIntegrable D f ∧ Summable (sourceCellSquare D γ M f) := by
  constructor
  · intro hf
    have hl := radialCellIntegrable_of_memLp_weighted hD hf
    refine ⟨hl, ?_⟩
    have hs := hf.integrable_sq.summable_integral
    simpa only [Real.norm_of_nonneg (sq_nonneg _),
      integral_sq_referenceWeightedCellMeasure_eq hab hD γ M _ hl] using hs
  · rintro ⟨hf, hs⟩
    exact memLp_referenceWeightedMeasure hab hD hf hs

theorem sourceCellSquare_neg (D : ReferenceData) (γ M : ℝ)
    (f : PolarPoint → ℝ) (m : ℕ) :
    sourceCellSquare D γ (-M) f m = outputCellSquare D γ M f m := by
  simp only [sourceCellSquare, outputCellSquare, mul_neg, neg_mul]

theorem SourceMember.memLp_weighted {D : ReferenceData} (hab : D.a ≤ D.b)
    (hD : RadialPartition D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) :
    MemLp F.1 2 (referenceWeightedMeasure D γ M) :=
  memLp_referenceWeightedMeasure hab hD hF.1 hF.2.1

theorem OutputRealization.memLp_weighted {D : ReferenceData} (hab : D.a ≤ D.b)
    (hD : RadialPartition D) {γ M aL : ℝ} {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) :
    MemLp (outputRemainder D aL U) 2 (referenceWeightedMeasure D γ (-M)) := by
  apply memLp_referenceWeightedMeasure hab hD hU.1
  simpa only [sourceCellSquare_neg] using hU.2.1

theorem outputRealization_iff_memLp_weighted {D : ReferenceData} (hab : D.a ≤ D.b)
    (hD : RadialPartition D) {γ M aL : ℝ} {U : RadialUnknown} :
    OutputRealization D γ M aL U ↔
      MemLp (outputRemainder D aL U) 2 (referenceWeightedMeasure D γ (-M)) ∧
        Function.Periodic U.1 (0, Real.pi) ∧
        (∀ r θ, U.1 (r, -θ) = U.1 (r, θ)) := by
  constructor
  · intro hU
    exact ⟨hU.memLp_weighted hab hD, hU.2.2⟩
  · rintro ⟨hU, hp, he⟩
    obtain ⟨hl, hs⟩ := (memLp_referenceWeightedMeasure_iff hab hD).mp hU
    refine ⟨hl, ?_, hp, he⟩
    simpa only [sourceCellSquare_neg] using hs

end ContinuousFlexibility.Statements
