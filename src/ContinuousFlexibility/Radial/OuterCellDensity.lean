import ContinuousFlexibility.Radial.OuterEnvelope
import ContinuousFlexibility.Radial.OuterPhysicalHilbert
import ContinuousFlexibility.Analysis.LocalizedDensityTransport

/-!
# The actual cellwise density factors

The square-root density is positive on the physical annulus and is
extended by one outside it. Its square gives exactly the original
radial Hilbert measure. The reciprocal, restricted to each cell, is
bounded by a coefficient power from the actual profile estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def outerRadialDensity (D : ReferenceData) (r : ℝ) : ℝ := 12 * D.w r / r ^ 2

def outerRadialSqrtDensity (D : ReferenceData) (r : ℝ) : ℝ :=
  if r ∈ radialCore D then sqrt (outerRadialDensity D r) else 1

theorem outerRadialDensity_pos {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {r : ℝ} (hr : r ∈ radialCore D) : 0 < outerRadialDensity D r := by
  obtain ⟨C, hC⟩ := hD
  have hrpos : 0 < r := hC.1.1.trans hr.1
  exact div_pos (mul_pos (by norm_num) (hC.1.2.2.2.2.1 r hr)) (pow_pos hrpos _)

theorem measurable_outerRadialSqrtDensity {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    Measurable (outerRadialSqrtDensity D) := by
  obtain ⟨C, hC⟩ := hD
  have hρ : Measurable (outerRadialDensity D) :=
    (measurable_const.mul hC.1.2.2.1.1.continuous.measurable).div
      (measurable_id.pow_const 2)
  exact (continuous_sqrt.measurable.comp hρ).piecewise measurableSet_Ioo measurable_const

theorem outerRadialSqrtDensity_pos {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (r : ℝ) : 0 < outerRadialSqrtDensity D r := by
  by_cases hr : r ∈ radialCore D
  · rw [outerRadialSqrtDensity, if_pos hr]
    exact sqrt_pos.mpr (outerRadialDensity_pos hD hr)
  · rw [outerRadialSqrtDensity, if_neg hr]
    norm_num

theorem outerRadialSqrtDensity_sq {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {r : ℝ} (hr : r ∈ radialCore D) :
    outerRadialSqrtDensity D r ^ 2 = outerRadialDensity D r := by
  rw [outerRadialSqrtDensity, if_pos hr, sq_sqrt (outerRadialDensity_pos hD hr).le]

/-- This is precisely the original physical Hilbert measure. -/
theorem radialHilbertMeasure_eq_squareDensity {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    radialHilbertMeasure D =
      squareDensityMeasure (volume.restrict (radialCore D)) (outerRadialSqrtDensity D) := by
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [outerRadialSqrtDensity_sq hD hr]
  rfl

def outerRadialDensityEquiv {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    Lp ℝ 2 (radialHilbertMeasure D) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume.restrict (radialCore D)) :=
  (l2MeasureCongr (radialHilbertMeasure_eq_squareDensity hD)).trans
    (squareDensityEquiv _ (measurable_outerRadialSqrtDensity hD) (outerRadialSqrtDensity_pos hD))

/-- The coefficient power is uniform over all cells and all points in
each cell. It is derived from the profile's reciprocal coefficient bound. -/
theorem outerCell_inverse_sqrt_density_bound {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ D.cellIndex m →
      ∀ r ∈ D.cells m, |(outerRadialSqrtDensity D r)⁻¹| ≤ radialE (D.cellIndex m) ^ C := by
  obtain ⟨C₀, hC⟩ := hD
  have hD' : IsAccumulatingProfile D := ⟨C₀, hC⟩
  rcases hC with ⟨hgeom, hpart, hCpos, _, _, _, _, _, _, hinv, _, _, _⟩
  have hC0 : 0 < C₀ 0 := hCpos 0
  let L : ℝ := 1 + D.b ^ 2 * C₀ 0 / 12
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨L + C₀ 0, add_pos hL (hCpos 0), fun m hm r hr => ?_⟩
  have hrCore : r ∈ radialCore D := hpart.2.2.2.1 m hr
  have hrpos : 0 < r := hgeom.1.trans hrCore.1
  have hbpos : 0 < D.b := hrpos.trans hrCore.2
  have hwpos : 0 < D.w r := hgeom.2.2.2.2.1 r hrCore
  have ha := outerRadialSqrtDensity_pos hD' r
  have hs : (outerRadialSqrtDensity D r)⁻¹ ^ 2 = r ^ 2 / (12 * D.w r) := by
    rw [← inv_pow, outerRadialSqrtDensity_sq hD' hrCore, outerRadialDensity, inv_div]
  have hwi : (D.w r)⁻¹ ≤ C₀ 0 * radialE (D.cellIndex m) ^ (C₀ 0) := by
    simpa only [radialJet, abs_of_pos (inv_pos.mpr hwpos)] using hinv m r hr 0
  have hQ : 1 ≤ radialQ (D.cellIndex m) := by
    have hnR : 1 ≤ (D.cellIndex m : ℝ) := by exact_mod_cast hm
    have hn2 : 1 ≤ (D.cellIndex m : ℝ) ^ 2 := by nlinarith
    exact hn2.trans (outer_nat_sq_le_radialQ hm)
  have hE : 1 ≤ radialE (D.cellIndex m) ^ (C₀ 0) := by
    rw [outer_radialE_rpow]
    apply one_le_exp_iff.mpr
    exact mul_nonneg (hCpos 0).le (zero_le_one.trans hQ)
  have hlocal : |(outerRadialSqrtDensity D r)⁻¹| ≤
      L * radialE (D.cellIndex m) ^ (C₀ 0) := by
    rw [abs_of_pos (inv_pos.mpr ha)]
    calc
      _ ≤ 1 + (outerRadialSqrtDensity D r)⁻¹ ^ 2 := by
        nlinarith [sq_nonneg ((outerRadialSqrtDensity D r)⁻¹ - 1)]
      _ = 1 + (r ^ 2 / 12) * (D.w r)⁻¹ := by rw [hs]; ring
      _ ≤ 1 + (D.b ^ 2 / 12) * (C₀ 0 * radialE (D.cellIndex m) ^ (C₀ 0)) := by
        apply add_le_add_left
        exact mul_le_mul (by nlinarith : r ^ 2 / 12 ≤ D.b ^ 2 / 12) hwi
          (inv_nonneg.mpr hwpos.le) (by positivity)
      _ ≤ L * radialE (D.cellIndex m) ^ (C₀ 0) := by
        dsimp only [L]
        nlinarith
  have hconstant : L ≤ radialE (D.cellIndex m) ^ L := by
    rw [outer_radialE_rpow]
    calc
      L ≤ exp L := by linarith [add_one_le_exp L]
      _ ≤ _ := exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ L * radialE (D.cellIndex m) ^ (C₀ 0) := hlocal
    _ ≤ radialE (D.cellIndex m) ^ L * radialE (D.cellIndex m) ^ (C₀ 0) :=
      mul_le_mul_of_nonneg_right hconstant (rpow_pos_of_pos (exp_pos _) _).le
    _ = _ := (rpow_add (exp_pos _) L (C₀ 0)).symm

end ContinuousFlexibility.Radial
