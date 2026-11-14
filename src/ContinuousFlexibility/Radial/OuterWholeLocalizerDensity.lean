module

public import ContinuousFlexibility.Radial.OuterLocalizerDensity
public import ContinuousFlexibility.Radial.OuterWholeMeasure

/-!
# Localized ordinary kernels on the actual whole outer interval

The weighted and ordinary operators use the same increasing outward
coordinate and the same open outer interval. Two reciprocal square-root
density multipliers preserve the actual localized kernel, with the
minus sign of the manuscript's ordinary inverse. Their coefficient loss
depends only on the common profile bounds and the common outer radius.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ENNReal

theorem outerWholeMeasure_eq_squareDensity
    {D : ReferenceData} (hD : IsAccumulatingProfile D) {right : Bool} {entry : ℝ}
    (hentry : entry ∈ radialCore D) :
    outerWholeMeasure D right entry =
      squareDensityMeasure
        (volume.restrict (Ioo (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right))))
        (fun x => outerRadialSqrtDensity D (outerOutwardRadius right x)) := by
  rw [outerWholeMeasure_eq_density hentry]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hcore := outerWhole_coordinate_core (right := right) (x := x) hentry ⟨hx.1.le, hx.2⟩
  rw [outerRadialSqrtDensity_sq hD hcore]
  congr 1
  unfold outerRadialDensity
  cases right <;> simp only [outerOutwardRadius, Bool.false_eq_true, ite_false, ite_true, neg_sq]

def outerWholeLocalizedKernel (D : ReferenceData) (right : Bool) (k m : ℕ)
    (K : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  D.localizer k (outerOutwardRadius right x) * K x y *
    D.localizer m (outerOutwardRadius right y)

/-- The same localized whole kernel gives an ordinary bounded operator.
The exponent is the explicit function of the common `C` and common `b`,
so it can be fixed before choosing a profile in the parameter family. -/
theorem outerWholeLocalizedDensity_transport
    {D : ReferenceData} {C : ℕ → ℝ} (hC : AccumulatingProfileBounds D C)
    {b : ℝ} (hb : D.b = b) (right : Bool) {entry : ℝ} (hentry : entry ∈ radialCore D)
    (k m : ℕ) (hk : 1 ≤ D.cellIndex k) (hm : 1 ≤ D.cellIndex m)
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry)
    (K : ℝ → ℝ → ℝ) {B : ℝ} (hRn : ‖R‖ ≤ B)
    (hRkernel : ∀ f : OuterWholeL2 D right entry,
      (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] fun x =>
        ∫ y, outerWholeLocalizedKernel D right k m K x y * f y ∂outerWholeMeasure D right entry) :
    ∃ G : Lp ℝ 2 (volume.restrict (Ioo (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right)))) →L[ℝ]
        Lp ℝ 2 (volume.restrict (Ioo (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right)))),
      ‖G‖ ≤ radialE (D.cellIndex k) ^ outerCellDensityExponent b C * B *
        radialE (D.cellIndex m) ^ outerCellDensityExponent b C ∧
      ∀ f : Lp ℝ 2 (volume.restrict (Ioo (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right)))),
        (G f : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right)))] fun x =>
            -(∫ y, outerWholeLocalizedKernel D right k m K x y * f y
              ∂volume.restrict (Ioo (outerOutwardRadius right entry)
                (outerOutwardRadius right (tailPhysicalEndpoint D right)))) := by
  have hD : IsAccumulatingProfile D := ⟨C, hC⟩
  have hcell (q : ℕ) (hq : 1 ≤ D.cellIndex q) :
      ∀ r ∈ D.cells q, |(outerRadialSqrtDensity D r)⁻¹| ≤
        radialE (D.cellIndex q) ^ outerCellDensityExponent b C := by
    simpa only [hb] using outerCell_inverse_sqrt_density_bound_of_bounds hC q hq
  let μ := volume.restrict (Ioo (outerOutwardRadius right entry)
    (outerOutwardRadius right (tailPhysicalEndpoint D right)))
  let a := fun x => outerRadialSqrtDensity D (outerOutwardRadius right x)
  let bk := fun x => outerReciprocalLocalizerDensity D k (outerOutwardRadius right x)
  let bm := fun x => outerReciprocalLocalizerDensity D m (outerOutwardRadius right x)
  have href := (measurableEmbedding_outerOutwardRadius right).measurable
  have ha : Measurable a := (measurable_outerRadialSqrtDensity hD).comp href
  have hap : ∀ x, 0 < a x := fun x => outerRadialSqrtDensity_pos hD _
  have hbk : AEStronglyMeasurable bk μ :=
    ((measurable_outerReciprocalLocalizerDensity hD k).comp href).aestronglyMeasurable
  have hbm : AEStronglyMeasurable bm μ :=
    ((measurable_outerReciprocalLocalizerDensity hD m).comp href).aestronglyMeasurable
  have hkp : 0 ≤ radialE (D.cellIndex k) ^ outerCellDensityExponent b C :=
    (rpow_pos_of_pos (exp_pos _) _).le
  have hmp : 0 ≤ radialE (D.cellIndex m) ^ outerCellDensityExponent b C :=
    (rpow_pos_of_pos (exp_pos _) _).le
  have hkb : ∀ᵐ x ∂μ, |bk x| ≤ radialE (D.cellIndex k) ^ outerCellDensityExponent b C :=
    Eventually.of_forall fun x =>
      outerReciprocalLocalizerDensity_bound hD hkp (hcell k hk) (outerOutwardRadius right x)
  have hmb : ∀ᵐ x ∂μ, |bm x| ≤ radialE (D.cellIndex m) ^ outerCellDensityExponent b C :=
    Eventually.of_forall fun x =>
      outerReciprocalLocalizerDensity_bound hD hmp (hcell m hm) (outerOutwardRadius right x)
  let R' := l2OperatorMeasureCongr (outerWholeMeasure_eq_squareDensity hD hentry) R
  have hR' : ‖R'‖ ≤ B := by
    dsimp only [R']
    rw [norm_l2OperatorMeasureCongr]
    exact hRn
  refine ⟨localizedDensityInverse μ ha hap hbk hbm hkb hmb R',
    norm_localizedDensityInverse_le μ ha hap hbk hbm hkb hmb R' hkp hmp
      ((norm_nonneg R).trans hRn) hR', ?_⟩
  intro f
  apply localizedDensityInverse_kernel μ ha hap hbk hbm hkb hmb R'
    (outerWholeLocalizedKernel D right k m K)
    (l2OperatorMeasureCongr_kernel (outerWholeMeasure_eq_squareDensity hD hentry) R _ hRkernel)
  · intro x y
    change bk x * a x * (D.localizer k (outerOutwardRadius right x) * K x y *
      D.localizer m (outerOutwardRadius right y)) = _
    calc
      _ = (bk x * a x * D.localizer k (outerOutwardRadius right x)) * K x y *
          D.localizer m (outerOutwardRadius right y) := by ring
      _ = _ := by
        rw [outerReciprocalLocalizerDensity_cancel hD k (outerOutwardRadius right x)]
        rfl
  · intro x y
    change a y * bm y * (D.localizer k (outerOutwardRadius right x) * K x y *
      D.localizer m (outerOutwardRadius right y)) = _
    calc
      _ = D.localizer k (outerOutwardRadius right x) * K x y *
          (bm y * a y * D.localizer m (outerOutwardRadius right y)) := by ring
      _ = _ := by
        rw [outerReciprocalLocalizerDensity_cancel hD m (outerOutwardRadius right y)]
        rfl

end ContinuousFlexibility.Radial
