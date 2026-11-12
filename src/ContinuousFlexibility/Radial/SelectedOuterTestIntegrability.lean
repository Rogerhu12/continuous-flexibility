import ContinuousFlexibility.Radial.SelectedOutwardRegionMeasure
import ContinuousFlexibility.Radial.SelectedReferenceTransport

/-!
# Actual L² Jacobi tests in outward coordinates

The existing global Glaeser estimate is transported through the reflection.
Thus the test may approach the singular endpoint; no bounded reciprocal
of the vanishing profile is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem radialJacobi_outward (D : ReferenceData) (right : Bool)
    (J : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    radialJacobi J (outerTailOutwardWeight D right)
      (fun t => u (outerOutwardRadius right t)) x =
      radialJacobi J D.w u (outerOutwardRadius right x) := by
  cases right
  · have hweight : radialRadiusScale (-1) 1 D.w = outerTailOutwardWeight D false := by
      funext t
      simp [radialRadiusScale, outerTailOutwardWeight, outerTailSign, div_neg]
    have hfield : radialRadiusScale (-1) 1 u = fun t => u (-t) := by
      funext t
      simp [radialRadiusScale, div_neg]
    simpa [hweight, hfield, outerTailSign, outerOutwardRadius]
      using radialJacobi_radialRadiusScale (by norm_num : (-1 : ℝ) ≠ 0)
        J 1 (-1) D.w u (-x)
  · have hweight : radialRadiusScale 1 1 D.w = outerTailOutwardWeight D true := by
      funext t
      simp [radialRadiusScale, outerTailOutwardWeight, outerTailSign]
    have hfield : radialRadiusScale 1 1 u = u := by
      funext t
      simp [radialRadiusScale]
    simpa [hweight, hfield, outerTailSign, outerOutwardRadius]
      using radialJacobi_radialRadiusScale one_ne_zero J 1 1 D.w u x

theorem radialJacobi_outward_pullback (D : ReferenceData) (right : Bool)
    (J : ℝ) (u : ℝ → ℝ) (r : ℝ) :
    radialJacobi J (outerTailOutwardWeight D right)
      (fun t => u (outerOutwardRadius right t)) (outerOutwardRadius right r) =
      radialJacobi J D.w u r := by
  rw [radialJacobi_outward, outerOutwardRadius_twice]

def selectedOutwardJacobiTest (D : ReferenceData) (right : Bool)
    (j : ℕ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  radialJacobi ((j : ℝ) ^ 2) (outerTailOutwardWeight D right) φ x /
    selectedOutwardDensity D right x

theorem selectedOutwardSmooth_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    MemLp φ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) := by
  rw [outerOutwardRegionMeasure_eq_map hcut]
  apply (measurableEmbedding_outerOutwardRadius right).memLp_map_measure_iff.mpr
  have hc : Continuous (fun r => φ (outerOutwardRadius right r)) :=
    hφ.continuous.comp (contDiff_outerOutwardRadius right).continuous
  exact (matching_memLp_of_continuousOn hD hc.measurable hc.continuousOn 2).restrict _

theorem selectedOutwardJacobiTest_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : ℕ) :
    MemLp (selectedOutwardJacobiTest D right j φ) 2
      (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) := by
  rw [outerOutwardRegionMeasure_eq_map hcut]
  apply (measurableEmbedding_outerOutwardRadius right).memLp_map_measure_iff.mpr
  have htest := (matchingJacobiTest_memLp hD
    (hφ.comp (contDiff_outerOutwardRadius right)) j).restrict (radialTailInterval D right cut)
  have heq :
      (selectedOutwardJacobiTest D right j φ ∘ outerOutwardRadius right) =
        matchingJacobiTest D j (fun r => φ (outerOutwardRadius right r)) := by
    funext r
    have hcov := radialJacobi_outward_pullback D right ((j : ℝ) ^ 2)
      (fun x => φ (outerOutwardRadius right x)) r
    have htwice : (fun t => φ (outerOutwardRadius right (outerOutwardRadius right t))) = φ := by
      funext t
      rw [outerOutwardRadius_twice]
    change radialJacobi ((j : ℝ) ^ 2) (outerTailOutwardWeight D right)
      (fun t => φ (outerOutwardRadius right (outerOutwardRadius right t)))
        (outerOutwardRadius right r) =
      radialJacobi ((j : ℝ) ^ 2) D.w (fun x => φ (outerOutwardRadius right x)) r at hcov
    rw [htwice] at hcov
    simp only [Function.comp_def, selectedOutwardJacobiTest,
      selectedOutwardDensity_reflect, matchingJacobiTest, hcov]
  rw [heq]
  exact htest

end ContinuousFlexibility.Radial
