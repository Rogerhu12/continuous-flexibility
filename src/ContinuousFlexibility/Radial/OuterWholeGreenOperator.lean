import ContinuousFlexibility.Radial.OuterActualGreenOperator
import ContinuousFlexibility.Analysis.L2RestrictionSplit
import ContinuousFlexibility.Analysis.L2CompactInterval

/-!
# The constructed Green operator on the whole weighted outer region

The finite-core kernel and the deep Dirichlet inverse are assembled on the
original weighted measure.  Restriction, the actual compact-core isometry,
and extension by zero identify the four blocks with an operator on one L²
space.  All norm estimates refer to that whole-space operator.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousLinearMap
open ContinuousFlexibility.Analysis

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderClosedTopology X]
  [CompactSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s)
  (ν : Measure X) [IsFiniteMeasure ν]
  (e : Lp ℝ 2 (μ.restrict s) ≃ₗᵢ[ℝ] Lp ℝ 2 ν)

/-- Actual source coordinates: compact core and restricted deep tail. -/
def outerCoreCoordinates :
    Lp ℝ 2 μ →L[ℝ] (Lp ℝ 2 ν × Lp ℝ 2 (μ.restrict sᶜ)) :=
  (e.toContinuousLinearEquiv.toContinuousLinearMap.comp (l2Restrict μ s)).prod
    (l2Restrict μ sᶜ)

theorem outerCoreCoordinates_apply (f : Lp ℝ 2 μ) :
    outerCoreCoordinates μ s ν e f = (e (l2Restrict μ s f), l2Restrict μ sᶜ f) := by
  simp only [outerCoreCoordinates, prod_apply, comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]

/-- Actual gluing after returning the compact core to its ambient restriction. -/
def outerCoreAssemble :
    (Lp ℝ 2 ν × Lp ℝ 2 (μ.restrict sᶜ)) →L[ℝ] Lp ℝ 2 μ :=
  (l2Glue μ s hs).comp
    (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.prodMap (id ℝ _))

theorem outerCoreAssemble_apply (f : Lp ℝ 2 ν × Lp ℝ 2 (μ.restrict sᶜ)) :
    outerCoreAssemble μ s hs ν e f = l2Glue μ s hs (e.symm f.1, f.2) := by
  simp only [outerCoreAssemble, comp_apply, prodMap_apply, id_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]

theorem outerCoreAssemble_coordinates (f : Lp ℝ 2 μ) :
    outerCoreAssemble μ s hs ν e (outerCoreCoordinates μ s ν e f) = f := by
  rw [outerCoreCoordinates_apply, outerCoreAssemble_apply, e.symm_apply_apply,
    ← l2Split_apply, l2Glue_split]

theorem outerCoreCoordinates_assemble (f : Lp ℝ 2 ν × Lp ℝ 2 (μ.restrict sᶜ)) :
    outerCoreCoordinates μ s ν e (outerCoreAssemble μ s hs ν e f) = f := by
  rw [outerCoreAssemble_apply, outerCoreCoordinates_apply]
  have h := l2Split_glue μ s hs (e.symm f.1, f.2)
  rw [l2Split_apply] at h
  apply Prod.ext
  · rw [congrArg Prod.fst h, e.apply_symm_apply]
  · exact congrArg Prod.snd h

theorem norm_outerCoreCoordinates_apply_le (f : Lp ℝ 2 μ) :
    ‖outerCoreCoordinates μ s ν e f‖ ≤ ‖f‖ := by
  rw [outerCoreCoordinates_apply, Prod.norm_def, e.norm_map]
  apply max_le
  · exact ((l2Restrict μ s).le_opNorm f).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (norm_l2Restrict_le μ s) (norm_nonneg f))
  · exact ((l2Restrict μ sᶜ).le_opNorm f).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (norm_l2Restrict_le μ sᶜ) (norm_nonneg f))

theorem norm_outerCoreAssemble_apply_le (f : Lp ℝ 2 ν × Lp ℝ 2 (μ.restrict sᶜ)) :
    ‖outerCoreAssemble μ s hs ν e f‖ ≤ 2 * ‖f‖ := by
  rw [outerCoreAssemble_apply]
  simpa only [Prod.norm_def, e.symm.norm_map] using
    norm_l2Glue_apply_le μ s hs (e.symm f.1, f.2)

/-- The actual outer Green operator on the original full weighted L² space. -/
def outerWholeGreenOperator (lam : ℝ) (c : X) (U V : C(X, ℝ))
    (D : Lp ℝ 2 (μ.restrict sᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict sᶜ))
    (p : Lp ℝ 2 (μ.restrict sᶜ)) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (outerCoreAssemble μ s hs ν e).comp
    ((outerActualGreenOperator ν lam c U V D p).comp (outerCoreCoordinates μ s ν e))

theorem outerWholeGreenOperator_apply (lam : ℝ) (c : X) (U V : C(X, ℝ))
    (D : Lp ℝ 2 (μ.restrict sᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict sᶜ))
    (p : Lp ℝ 2 (μ.restrict sᶜ)) (f : Lp ℝ 2 μ) :
    outerWholeGreenOperator μ s hs ν e lam c U V D p f =
      outerCoreAssemble μ s hs ν e
        (outerActualGreenOperator ν lam c U V D p (outerCoreCoordinates μ s ν e f)) := by
  rw [outerWholeGreenOperator, comp_apply, comp_apply]

theorem outerWholeGreenOperator_coordinates (lam : ℝ) (c : X) (U V : C(X, ℝ))
    (D : Lp ℝ 2 (μ.restrict sᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict sᶜ))
    (p : Lp ℝ 2 (μ.restrict sᶜ)) (f : Lp ℝ 2 μ) :
    outerCoreCoordinates μ s ν e (outerWholeGreenOperator μ s hs ν e lam c U V D p f) =
      outerActualGreenOperator ν lam c U V D p (outerCoreCoordinates μ s ν e f) := by
  rw [outerWholeGreenOperator_apply, outerCoreCoordinates_assemble]

/-- The full weighted norm bound, with the actual core mass cancelling λ. -/
theorem norm_outerWholeGreenOperator_le {lam A K d : ℝ}
    (hlam : 0 < lam) (hA : 0 ≤ A) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (c : X) (U V : C(X, ℝ))
    (D : Lp ℝ 2 (μ.restrict sᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict sᶜ))
    (p : Lp ℝ 2 (μ.restrict sᶜ))
    (hU : ∀ x, |U x| ≤ K) (hV : ∀ x, |V x| ≤ K)
    (hmass : (measureUnivNNReal ν : ℝ) ≤ lam * A ^ 2)
    (hD : ‖D‖ ≤ d) (hp : ‖p‖ ≤ Real.sqrt lam * A) :
    ‖outerWholeGreenOperator μ s hs ν e lam c U V D p‖ ≤
      2 * (d + 2 * A ^ 2 * K ^ 2) := by
  have hblock := norm_outerActualGreenOperator_le ν hlam hA hK hd c U V D p hU hV hmass hD hp
  apply opNorm_le_bound _ (by positivity)
  intro f
  rw [outerWholeGreenOperator_apply]
  calc
    _ ≤ 2 * ‖outerActualGreenOperator ν lam c U V D p (outerCoreCoordinates μ s ν e f)‖ :=
      norm_outerCoreAssemble_apply_le μ s hs ν e _
    _ ≤ 2 * (‖outerActualGreenOperator ν lam c U V D p‖ *
        ‖outerCoreCoordinates μ s ν e f‖) :=
      mul_le_mul_of_nonneg_left ((outerActualGreenOperator ν lam c U V D p).le_opNorm _) (by norm_num)
    _ ≤ 2 * ((d + 2 * A ^ 2 * K ^ 2) * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hblock (norm_outerCoreCoordinates_apply_le μ s ν e f)
          (norm_nonneg _) (by positivity)) (by norm_num)
    _ = (2 * (d + 2 * A ^ 2 * K ^ 2)) * ‖f‖ := (mul_assoc _ _ _).symm

/-- The deep/deep block of the full operator is exactly the deep Dirichlet
inverse plus the actual Green diagonal times the Poisson rank-one map. -/
theorem outerWholeGreenOperator_deep_block (lam : ℝ) (c : X) (U V : C(X, ℝ))
    (D : Lp ℝ 2 (μ.restrict sᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict sᶜ))
    (p g : Lp ℝ 2 (μ.restrict sᶜ)) :
    (outerCoreCoordinates μ s ν e
      (outerWholeGreenOperator μ s hs ν e lam c U V D p
        (outerCoreAssemble μ s hs ν e (0, g)))).2 =
      D g + outerGreenKernel lam U V c c • (inner ℝ p g • p) := by
  rw [outerWholeGreenOperator_coordinates, outerCoreCoordinates_assemble]
  exact outerActualGreenOperator_tail ν lam c U V D p g

end ContinuousFlexibility.Radial
