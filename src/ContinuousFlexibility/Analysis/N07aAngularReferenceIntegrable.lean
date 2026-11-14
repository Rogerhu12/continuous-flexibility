module

public import ContinuousFlexibility.Analysis.N07aAngularReferenceDecomposition
public import ContinuousFlexibility.Radial.R11bRadialTests

/-!
# Actual piecewise reference jets supply the physical integrability

Only genuine first and second derivatives are bounded here. The two
Borel sources are obtained by the displayed differential expressions;
their L¹ membership follows from the finite physical annulus measure.
The continuous first derivative inherits the same bound at interfaces
from the original a.e. radial cover.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_reference_firstJet_bound_on_core
    (h04 : N04Properties D T S C L K base loss ε) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ 1 v (annularOpen D)) {B : ℝ}
    (hB : ∀ m p, p ∈ referencePhysicalPieceOpen S K m → |radialPartial v p| ≤ B) :
    ∀ r ∈ radialCore D, ∀ θ, |radialPartial v (r, θ)| ≤ B := by
  have hdf : ContinuousOn (fderiv ℝ v) (annularOpen D) :=
    hv.continuousOn_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) le_rfl
  intro r hr θ
  exact n07a_physicalPiece_bound h04 (hdf.clm_apply continuousOn_const).abs
    continuousOn_const hB (r, θ) ⟨hr, mem_univ _⟩

theorem n07a_referenceCoefficient_bound (hgeom : RadialProfileGeometry D) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r ∈ radialCore D,
      |deriv D.w r| + |D.w r| + |deriv D.w r / r| ≤ A := by
  let coeff : ℝ → ℝ := fun r => |deriv D.w r| + |D.w r| + |deriv D.w r / r|
  have hc : Continuous coeff :=
    (((contDiff_infty_iff_deriv.mp hgeom.2.2.1.1).2.continuous.abs).add
      hgeom.2.2.1.1.continuous.abs).add
        (r11b_continuous_flat_deriv_div hgeom.1 hgeom.2.2.1).abs
  obtain ⟨A, hA⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn
    (s := Icc D.a D.b))
  exact ⟨max A 0, le_max_right _ _, fun r hr =>
    (hA ⟨r, Ioo_subset_Icc_self hr, rfl⟩).trans (le_max_left _ _)⟩

theorem n07a_referenceDifferential_abs_le {v : PolarPoint → ℝ} {p : PolarPoint} {B : ℝ}
    (h₁ : |radialPartial v p| ≤ B) (h₂ : |radialPartial (radialPartial v) p| ≤ B)
    (h₃ : |angularPartial (angularPartial v) p| ≤ B) :
    |n07aReferenceDifferential D v p| ≤
      (|deriv D.w p.1| + |D.w p.1| + |deriv D.w p.1 / p.1|) * B := by
  unfold n07aReferenceDifferential
  calc
    _ ≤ |deriv D.w p.1 * radialPartial v p| +
        |D.w p.1 * radialPartial (radialPartial v) p| +
        |deriv D.w p.1 / p.1 * angularPartial (angularPartial v) p| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |deriv D.w p.1| * B + |D.w p.1| * B + |deriv D.w p.1 / p.1| * B := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h₂ (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left h₃ (abs_nonneg _))
    _ = _ := by ring

theorem n07a_referenceSources_integrable_of_jet_bounds
    (h04 : N04Properties D T S C L K base loss ε)
    (hgeom : RadialProfileGeometry D) {v : PolarPoint → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      |radialPartial v p| ≤ B ∧ |radialPartial (radialPartial v) p| ≤ B ∧
        |angularPartial (angularPartial v) p| ≤ B) :
    Integrable (n07aReferenceNormalSource D K v) (radialPhysicalMeasure D) ∧
      Integrable (n07aReferenceInteriorDifferential D K v) (radialPhysicalMeasure D) := by
  let coeff : ℝ → ℝ := fun r => |deriv D.w r| + |D.w r| + |deriv D.w r / r|
  obtain ⟨A, hA0, hA⟩ := n07a_referenceCoefficient_bound hgeom
  have hcoef {p : PolarPoint} (hp : p ∈ n07aReferencePieceInterior K) :
      coeff p.1 ≤ A := by
    obtain ⟨m, hm⟩ := mem_iUnion.mp hp
    have hr := (h04.1.referenceBounds m).2.2 hm.1
    exact hA p.1 hr
  have hbound (p : PolarPoint) :
      |n07aReferenceNormalSource D K v p| ≤ A * B ∧
        |n07aReferenceInteriorDifferential D K v p| ≤ A * B := by
    by_cases hp : p ∈ n07aReferencePieceInterior K
    · obtain ⟨m, hm⟩ := mem_iUnion.mp hp
      obtain ⟨hr, hrr, hθθ⟩ := hB m p hm
      have hn : |deriv D.w p.1 * radialPartial v p +
          D.w p.1 * radialPartial (radialPartial v) p| ≤
          (|deriv D.w p.1| + |D.w p.1|) * B := by
        calc
          _ ≤ |deriv D.w p.1| * |radialPartial v p| +
              |D.w p.1| * |radialPartial (radialPartial v) p| := by
            simpa only [abs_mul] using abs_add_le
              (deriv D.w p.1 * radialPartial v p)
              (D.w p.1 * radialPartial (radialPartial v) p)
          _ ≤ |deriv D.w p.1| * B + |D.w p.1| * B :=
            add_le_add (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hrr (abs_nonneg _))
          _ = _ := by ring
      have hnc : |deriv D.w p.1| + |D.w p.1| ≤ coeff p.1 :=
        le_add_of_nonneg_right (abs_nonneg _)
      constructor
      · rw [n07aReferenceNormalSource, indicator_of_mem hp]
        exact hn.trans (mul_le_mul_of_nonneg_right (hnc.trans (hcoef hp)) hB0)
      · rw [n07aReferenceInteriorDifferential, indicator_of_mem hp]
        exact (n07a_referenceDifferential_abs_le hr hrr hθθ).trans
          (mul_le_mul_of_nonneg_right (hcoef hp) hB0)
    · simp only [n07aReferenceNormalSource, n07aReferenceInteriorDifferential,
        indicator_of_notMem hp, abs_zero]
      exact ⟨mul_nonneg hA0 hB0, mul_nonneg hA0 hB0⟩
  letI : IsFiniteMeasure (radialPhysicalMeasure D) := ⟨r11b_radialPhysicalMeasure_finite D⟩
  have hconst : Integrable (fun _ : PolarPoint => A * B) (radialPhysicalMeasure D) :=
    integrable_const _
  exact ⟨hconst.mono' (n07aReferenceNormalSource_measurable K
      hgeom.2.2.1.1.continuous.measurable v).aestronglyMeasurable
        (Eventually.of_forall fun p => (hbound p).1),
    hconst.mono' (n07aReferenceInteriorDifferential_measurable K
      hgeom.2.2.1.1.continuous.measurable v).aestronglyMeasurable
        (Eventually.of_forall fun p => (hbound p).2)⟩

end ContinuousFlexibility.Analysis
