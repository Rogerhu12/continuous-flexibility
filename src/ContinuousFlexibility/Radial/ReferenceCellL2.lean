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
    (memLp_zero : MemLp (fun _ : PolarPoint => (0 : ℝ)) 2 (radialPhysicalMeasure D))

theorem RadialCellIntegrable.add {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g) :
    RadialCellIntegrable D (fun x => f x + g x) := by
  intro m
  simpa only [Pi.add_apply, mul_add] using (hf m).add (hg m)

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

end ContinuousFlexibility.Statements
