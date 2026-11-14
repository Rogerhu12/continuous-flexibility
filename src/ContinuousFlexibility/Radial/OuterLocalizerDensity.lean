module

public import ContinuousFlexibility.Radial.OuterCellDensity

/-!
# The localized unweighted operator on the actual annulus

Each reciprocal square-root density is cut off to the support of the
actual smooth localizer. The profile supplies its bound. Conjugating
the weighted localized operator then preserves the actual integral
kernel and costs only the two coefficient powers.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def outerReciprocalLocalizerDensity (D : ReferenceData) (m : ℕ) : ℝ → ℝ :=
  (Function.support (D.localizer m)).indicator (fun r => (outerRadialSqrtDensity D r)⁻¹)

theorem measurable_outerReciprocalLocalizerDensity {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (m : ℕ) :
    Measurable (outerReciprocalLocalizerDensity D m) := by
  obtain ⟨C, hC⟩ := hD
  exact (measurable_outerRadialSqrtDensity ⟨C, hC⟩).inv.indicator
    (measurableSet_support (hC.2.1.1 m).continuous.measurable)

theorem outerReciprocalLocalizerDensity_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {m : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells m, |(outerRadialSqrtDensity D r)⁻¹| ≤ B) :
    ∀ r, |outerReciprocalLocalizerDensity D m r| ≤ B := by
  obtain ⟨C, hC⟩ := hD
  intro r
  by_cases hr : r ∈ Function.support (D.localizer m)
  · rw [outerReciprocalLocalizerDensity, indicator_of_mem hr]
    exact hbound r (hC.2.1.2.2.1 m hr)
  · rw [outerReciprocalLocalizerDensity, indicator_of_notMem hr, abs_zero]
    exact hB

theorem outerReciprocalLocalizerDensity_cancel {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (m : ℕ) (r : ℝ) :
    outerReciprocalLocalizerDensity D m r * outerRadialSqrtDensity D r *
      D.localizer m r = D.localizer m r := by
  by_cases hr : r ∈ Function.support (D.localizer m)
  · rw [outerReciprocalLocalizerDensity, indicator_of_mem hr,
      inv_mul_cancel₀ (outerRadialSqrtDensity_pos hD r).ne', one_mul]
  · have hz : D.localizer m r = 0 := Function.notMem_support.mp hr
    rw [hz, mul_zero]

def outerLocalizedKernel (D : ReferenceData) (k m : ℕ) (K : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  D.localizer k x * K x y * D.localizer m y

/-- The valid localized form of the manuscript's passage to L2(dr).
Its hypotheses concern the already constructed weighted localized
operator; the unweighted operator and its same-kernel representation
are conclusions. -/
theorem outerLocalizedDensity_transport {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ C : ℝ, 0 < C ∧ ∀ k m : ℕ, 1 ≤ D.cellIndex k → 1 ≤ D.cellIndex m →
      ∀ R : Lp ℝ 2 (radialHilbertMeasure D) →L[ℝ] Lp ℝ 2 (radialHilbertMeasure D),
      ∀ K : ℝ → ℝ → ℝ, ∀ B : ℝ, ‖R‖ ≤ B →
      (∀ f : Lp ℝ 2 (radialHilbertMeasure D), (R f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        fun x => ∫ y, outerLocalizedKernel D k m K x y * f y ∂radialHilbertMeasure D) →
      ∃ G : Lp ℝ 2 (volume.restrict (radialCore D)) →L[ℝ]
          Lp ℝ 2 (volume.restrict (radialCore D)),
        ‖G‖ ≤ radialE (D.cellIndex k) ^ C * B * radialE (D.cellIndex m) ^ C ∧
        ∀ f : Lp ℝ 2 (volume.restrict (radialCore D)),
          (G f : ℝ → ℝ) =ᵐ[volume.restrict (radialCore D)] fun x =>
            -(∫ y, outerLocalizedKernel D k m K x y * f y ∂volume.restrict (radialCore D)) := by
  obtain ⟨C, hC, hcell⟩ := outerCell_inverse_sqrt_density_bound hD
  refine ⟨C, hC, fun k m hk hm R K B hRn hRkernel => ?_⟩
  let μ := volume.restrict (radialCore D)
  let a := outerRadialSqrtDensity D
  let bk := outerReciprocalLocalizerDensity D k
  let bm := outerReciprocalLocalizerDensity D m
  have ha : Measurable a := measurable_outerRadialSqrtDensity hD
  have hap : ∀ x, 0 < a x := outerRadialSqrtDensity_pos hD
  have hbk : AEStronglyMeasurable bk μ :=
    (measurable_outerReciprocalLocalizerDensity hD k).aestronglyMeasurable
  have hbm : AEStronglyMeasurable bm μ :=
    (measurable_outerReciprocalLocalizerDensity hD m).aestronglyMeasurable
  have hkp : 0 ≤ radialE (D.cellIndex k) ^ C := (rpow_pos_of_pos (exp_pos _) _).le
  have hmp : 0 ≤ radialE (D.cellIndex m) ^ C := (rpow_pos_of_pos (exp_pos _) _).le
  have hkb : ∀ᵐ x ∂μ, |bk x| ≤ radialE (D.cellIndex k) ^ C :=
    Eventually.of_forall (outerReciprocalLocalizerDensity_bound hD hkp (hcell k hk))
  have hmb : ∀ᵐ x ∂μ, |bm x| ≤ radialE (D.cellIndex m) ^ C :=
    Eventually.of_forall (outerReciprocalLocalizerDensity_bound hD hmp (hcell m hm))
  let R' := l2OperatorMeasureCongr (radialHilbertMeasure_eq_squareDensity hD) R
  have hR' : ‖R'‖ ≤ B := by
    dsimp only [R']
    rw [norm_l2OperatorMeasureCongr]
    exact hRn
  refine ⟨localizedDensityInverse μ ha hap hbk hbm hkb hmb R',
    norm_localizedDensityInverse_le μ ha hap hbk hbm hkb hmb R' hkp hmp
      ((norm_nonneg R).trans hRn) hR', ?_⟩
  intro f
  apply localizedDensityInverse_kernel μ ha hap hbk hbm hkb hmb R'
    (outerLocalizedKernel D k m K)
    (l2OperatorMeasureCongr_kernel (radialHilbertMeasure_eq_squareDensity hD)
      R _ hRkernel)
  · intro x y
    change bk x * a x * (D.localizer k x * K x y * D.localizer m y) =
      D.localizer k x * K x y * D.localizer m y
    calc
      _ = (bk x * a x * D.localizer k x) * K x y * D.localizer m y := by ring
      _ = _ := by rw [outerReciprocalLocalizerDensity_cancel hD k x]
  · intro x y
    change a y * bm y * (D.localizer k x * K x y * D.localizer m y) =
      D.localizer k x * K x y * D.localizer m y
    calc
      _ = D.localizer k x * K x y * (bm y * a y * D.localizer m y) := by ring
      _ = _ := by rw [outerReciprocalLocalizerDensity_cancel hD m y]

end ContinuousFlexibility.Radial
