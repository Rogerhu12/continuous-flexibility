import ContinuousFlexibility.Statements.Radial
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual local `L²` fields in the reference spaces

Local membership includes measurability of the field itself. The partition
of unity then reconstructs an almost everywhere strongly measurable field
on the physical annulus. Cell squares are genuine two-dimensional `L²`
quantities, rather than integrals of a possibly nonmeasurable representative.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace

theorem RadialCellIntegrable.integrableOn_sq {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (m : ℕ) :
    IntegrableOn (fun x : PolarPoint => (D.localizer m x.1 * f x) ^ 2)
      (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume :=
  (hf m).integrable_sq

theorem RadialCellIntegrable.local_aestronglyMeasurable
    {D : ReferenceData} {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (m : ℕ) :
    AEStronglyMeasurable (fun x : PolarPoint => D.localizer m x.1 * f x)
      (radialPhysicalMeasure D) :=
  (hf m).aestronglyMeasurable

theorem RadialCellIntegrable.zero (D : ReferenceData) :
    RadialCellIntegrable D (fun _ => 0) := by
  intro m
  simpa only [mul_zero] using
    (MemLp.zero' : MemLp (fun _ : PolarPoint => (0 : ℝ)) 2 (radialPhysicalMeasure D))

theorem RadialCellIntegrable.add {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g) :
    RadialCellIntegrable D (fun x => f x + g x) := by
  intro m
  have h := (hf m).add (hg m)
  change MemLp (fun x : PolarPoint =>
    D.localizer m x.1 * f x + D.localizer m x.1 * g x) 2
      (radialPhysicalMeasure D) at h
  simpa only [mul_add] using h

theorem RadialCellIntegrable.const_mul {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (c : ℝ) :
    RadialCellIntegrable D (fun x => c * f x) := by
  intro m
  simpa only [mul_assoc, mul_left_comm] using (hf m).const_mul c

theorem RadialCellIntegrable.neg {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) : RadialCellIntegrable D (fun x => -f x) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)

theorem RadialCellIntegrable.sub {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g) :
    RadialCellIntegrable D (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem RadialCellIntegrable.congr_ae {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hfg : f =ᵐ[radialPhysicalMeasure D] g) :
    RadialCellIntegrable D g := by
  intro m
  apply (memLp_congr_ae ?_).mp (hf m)
  filter_upwards [hfg] with x hx
  exact congrArg (fun z : ℝ => D.localizer m x.1 * z) hx

theorem RadialPartition.tsum_localizer_mul {D : ReferenceData} (hD : RadialPartition D)
    {r : ℝ} (hr : r ∈ radialCore D) (c : ℝ) :
    (∑' m, D.localizer m r * c) = c := by
  rw [tsum_mul_right, (hD.2.2.2.2.1 r hr).2, one_mul]

/-- Measurability of every localized field and the actual partition identity
give measurability of the whole field on the physical annulus. -/
theorem RadialCellIntegrable.aestronglyMeasurable
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hD : RadialPartition D) :
    AEStronglyMeasurable f (radialPhysicalMeasure D) := by
  have hsum : AEMeasurable (fun x : PolarPoint => ∑' m, D.localizer m x.1 * f x)
      (radialPhysicalMeasure D) :=
    AEMeasurable.tsum (fun m => (hf m).aestronglyMeasurable.aemeasurable)
  apply hsum.aestronglyMeasurable.congr
  have hmem : ∀ᵐ x ∂radialPhysicalMeasure D,
      x ∈ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hmem] with x hx
  exact hD.tsum_localizer_mul hx.1 (f x)

/-- The actual `L²` equivalence class of one localized reference field. -/
def referenceCellL2 (D : ReferenceData) (m : ℕ) (f : PolarPoint → ℝ)
    (hf : RadialCellIntegrable D f) : Lp ℝ 2 (radialPhysicalMeasure D) :=
  (hf m).toLp (fun x => D.localizer m x.1 * f x)

theorem referenceCellL2_ae (D : ReferenceData) (m : ℕ) (f : PolarPoint → ℝ)
    (hf : RadialCellIntegrable D f) :
    (referenceCellL2 D m f hf : PolarPoint → ℝ) =ᵐ[radialPhysicalMeasure D]
      (fun x => D.localizer m x.1 * f x) :=
  (hf m).coeFn_toLp

theorem integral_referenceCell_sq_eq_norm_sq (D : ReferenceData) (m : ℕ)
    (f : PolarPoint → ℝ) (hf : RadialCellIntegrable D f) :
    (∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D) =
      ‖referenceCellL2 D m f hf‖ ^ 2 := by
  have heq : (∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D) =
      ∫ x, (referenceCellL2 D m f hf x) ^ 2 ∂radialPhysicalMeasure D := by
    apply integral_congr_ae
    filter_upwards [referenceCellL2_ae D m f hf] with x hx
    exact congrArg (fun z : ℝ => z ^ 2) hx.symm
  rw [heq]
  simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using
    (L2.inner_def (𝕜 := ℝ) (referenceCellL2 D m f hf) (referenceCellL2 D m f hf)).symm


/-- The physical annulus measure is the product of the two restricted
Lebesgue measures. -/
theorem radialPhysicalMeasure_eq_prod (D : ReferenceData) :
    radialPhysicalMeasure D = (volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  exact (Measure.prod_restrict (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (radialCore D)
    (Ioc (0 : ℝ) (2 * Real.pi))).symm

/-- Fubini identifies the frozen iterated cell square with the actual
two-dimensional square integral, including its angular normalization. -/
theorem referenceCellSquare_eq_integral {D : ReferenceData} (hab : D.a ≤ D.b)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) :
    referenceCellSquare D m f = (2 * Real.pi)⁻¹ *
      ∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D := by
  have hsq : Integrable (fun x : PolarPoint => (D.localizer m x.1 * f x) ^ 2)
      ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using (hf m).integrable_sq
  have hFub := integral_prod
    (fun x : PolarPoint => (D.localizer m x.1 * f x) ^ 2) hsq
  unfold referenceCellSquare radialAngularMean
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  simp_rw [intervalIntegral.integral_of_le
    (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
  simpa only [radialCore, radialPhysicalMeasure_eq_prod] using hFub.symm

theorem referenceCellSquare_eq_norm_sq {D : ReferenceData} (hab : D.a ≤ D.b)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) :
    referenceCellSquare D m f =
      (2 * Real.pi)⁻¹ * ‖referenceCellL2 D m f hf‖ ^ 2 := by
  rw [referenceCellSquare_eq_integral hab m hf,
    integral_referenceCell_sq_eq_norm_sq]

theorem referenceCellSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (m : ℕ) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) :
    0 ≤ referenceCellSquare D m f := by
  rw [referenceCellSquare_eq_norm_sq hab m hf]
  exact mul_nonneg (by positivity) (sq_nonneg _)

theorem sourceCellSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (m : ℕ) :
    0 ≤ sourceCellSquare D γ M f m :=
  mul_nonneg (Real.exp_pos _).le (referenceCellSquare_nonneg hab m hf)

theorem outputCellSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (m : ℕ) :
    0 ≤ outputCellSquare D γ M f m :=
  mul_nonneg (Real.exp_pos _).le (referenceCellSquare_nonneg hab m hf)

theorem referenceCellSquare_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    (m : ℕ) {f g : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (hfg : f =ᵐ[radialPhysicalMeasure D] g) :
    referenceCellSquare D m f = referenceCellSquare D m g := by
  rw [referenceCellSquare_eq_integral hab m hf,
    referenceCellSquare_eq_integral hab m (hf.congr_ae hfg)]
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  exact congrArg (fun z : ℝ => (D.localizer m x.1 * z) ^ 2) hx

end ContinuousFlexibility.Statements
