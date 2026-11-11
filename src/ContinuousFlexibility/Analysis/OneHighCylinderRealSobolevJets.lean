import ContinuousFlexibility.Analysis.OneHighCylinderRealSobolev
import ContinuousFlexibility.Analysis.OneHighCylinderSobolevJets

/-!
# Finite Sobolev control of the actual real cylinder derivatives

These are canonical real specializations of the same mixed Fourier
derivative theorem. Only base L² and the stated finite high norm are assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

theorem CylinderSmoothJet.real_memLp_derivative (u : CylinderSmoothJet P ℝ)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s i j : ℕ} (hs : u.MemRealSobolev s hu2) (hij : i + j ≤ s) :
    MemLp (u.jet i j) 2 (cylinderPhysicalMeasure P) := by
  have h : MemLp (cylinderComplexify (u.jet i j)) 2 (cylinderPhysicalMeasure P) :=
    u.complexify.memLp_derivative (cylinderComplexify_memLp (u.continuous 0 0) hu2) hs hij
  rw [memLp_iff, cylinder_eLpNorm_complexify (u.jet i j) (u.continuous i j) 2] at h
  exact h

theorem CylinderSmoothJet.real_derivative_l2_le_sobolev (u : CylinderSmoothJet P ℝ)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s i j : ℕ} (hs : u.MemRealSobolev s hu2) (hij : i + j ≤ s) :
    (eLpNorm (u.jet i j) 2 (cylinderPhysicalMeasure P)).toReal ≤
      cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 := by
  have h :
      (eLpNorm (cylinderComplexify (u.jet i j)) 2 (cylinderPhysicalMeasure P)).toReal ≤
        cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 :=
    u.complexify.derivative_l2_le_sobolev
      (cylinderComplexify_memLp (u.continuous 0 0) hu2) hs hij
  rw [cylinder_eLpNorm_complexify (u.jet i j) (u.continuous i j) 2] at h
  exact h

end ContinuousFlexibility.Analysis
