module

public import ContinuousFlexibility.Analysis.SpacesTorusCell
public import ContinuousFlexibility.Analysis.SpacesLpRestriction

/-!
# Actual `L²` transport between physical cells and the normalized torus

The inverse charts induce inverse linear isometries on the original
almost-everywhere classes. Restriction from the cylinder is contractive;
extension back to the cylinder keeps the fixed factor coming from `6π`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev SpacesCellL2 (n : ℤ) := Lp E 2 (spacesPhysicalCellMeasure n)

abbrev SpacesTorusValueL2 :=
  Lp E 2 (Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle)))

/-- Pull a normalized physical-cell class back to the torus. -/
def spacesPhysicalCellToTorus (n : ℤ) : SpacesCellL2 E n →ₗᵢ[ℝ] SpacesTorusValueL2 E :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (spacesPhysicalCellChart_preserving n)

/-- Pull a torus class back to the normalized physical cell. -/
def spacesTorusToPhysicalCell (n : ℤ) : SpacesTorusValueL2 E →ₗᵢ[ℝ] SpacesCellL2 E n :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (spacesPhysicalCellQuotient_preserving n)

theorem spacesPhysicalCellToTorus_ae (n : ℤ) (u : SpacesCellL2 E n) :
    (spacesPhysicalCellToTorus E n u : SpacesTorus → E) =ᵐ[
      Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)]
      u ∘ spacesPhysicalCellChart n :=
  Lp.coeFn_compMeasurePreserving u (spacesPhysicalCellChart_preserving n)

theorem spacesTorusToPhysicalCell_ae (n : ℤ) (u : SpacesTorusValueL2 E) :
    (spacesTorusToPhysicalCell E n u : PolarPoint → E) =ᵐ[spacesPhysicalCellMeasure n]
      u ∘ spacesPhysicalCellQuotient n :=
  Lp.coeFn_compMeasurePreserving u (spacesPhysicalCellQuotient_preserving n)

theorem spacesTorusToPhysicalCell_leftInverse (n : ℤ) (u : SpacesCellL2 E n) :
    spacesTorusToPhysicalCell E n (spacesPhysicalCellToTorus E n u) = u := by
  apply Lp.ext
  have hq := (spacesPhysicalCellQuotient_preserving n).quasiMeasurePreserving.ae_eq_comp
    (spacesPhysicalCellToTorus_ae E n u)
  filter_upwards [spacesTorusToPhysicalCell_ae E n (spacesPhysicalCellToTorus E n u), hq,
    spacesPhysicalCellMeasure_ae_mem n] with p hp hq hmem
  exact hp.trans (hq.trans (congrArg u (spacesPhysicalCellChart_quotient n hmem)))

theorem spacesPhysicalCellToTorus_leftInverse (n : ℤ) (u : SpacesTorusValueL2 E) :
    spacesPhysicalCellToTorus E n (spacesTorusToPhysicalCell E n u) = u := by
  apply Lp.ext
  have hc := (spacesPhysicalCellChart_preserving n).quasiMeasurePreserving.ae_eq_comp
    (spacesTorusToPhysicalCell_ae E n u)
  filter_upwards [spacesPhysicalCellToTorus_ae E n (spacesTorusToPhysicalCell E n u), hc]
    with t ht hc
  exact ht.trans (hc.trans (congrArg u (spacesPhysicalCellQuotient_chart n t)))

/-- The cell and normalized torus carry the same Hilbert space. -/
def spacesPhysicalCellTorusEquiv (n : ℤ) :
    SpacesCellL2 E n ≃ₗᵢ[ℝ] SpacesTorusValueL2 E where
  toFun := spacesPhysicalCellToTorus E n
  map_add' := (spacesPhysicalCellToTorus E n).map_add
  map_smul' := (spacesPhysicalCellToTorus E n).map_smul
  norm_map' := (spacesPhysicalCellToTorus E n).norm_map
  invFun := spacesTorusToPhysicalCell E n
  left_inv := spacesTorusToPhysicalCell_leftInverse E n
  right_inv := spacesPhysicalCellToTorus_leftInverse E n

/-- The radial domain used when extending a local class back to the cylinder. -/
def spacesPhysicalCellRadialSet (n : ℤ) : Set PolarPoint :=
  Ioc ((n : ℝ) - 3) (n + 3) ×ˢ univ

theorem spacesPhysicalCellRadialSet_measurable (n : ℤ) :
    MeasurableSet (spacesPhysicalCellRadialSet n) :=
  measurableSet_Ioc.prod MeasurableSet.univ

/-- Actual cylinder restriction with the normalized cell measure. -/
def spacesCylinderToPhysicalCell (n : ℤ) :
    Lp E 2 materialCylinderMeasure →L[ℝ] SpacesCellL2 E n :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using spacesPhysicalCellMeasure_le_cylinder n)

theorem spacesCylinderToPhysicalCell_ae (n : ℤ) (u : Lp E 2 materialCylinderMeasure) :
    (spacesCylinderToPhysicalCell E n u : PolarPoint → E) =ᵐ[spacesPhysicalCellMeasure n] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

theorem spacesCylinderToPhysicalCell_norm_le (n : ℤ) (u : Lp E 2 materialCylinderMeasure) :
    ‖spacesCylinderToPhysicalCell E n u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (spacesCylinderToPhysicalCell_ae E n u), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (spacesPhysicalCellMeasure_le_cylinder n))

private def spacesCellRestoreMeasure (n : ℤ) : SpacesCellL2 E n →L[ℝ]
    Lp E 2 (materialCylinderMeasure.restrict (spacesPhysicalCellRadialSet n)) :=
  Lp.LpToLpOfMeasureLeSMul (c := ENNReal.ofReal (6 * Real.pi)) ENNReal.ofReal_ne_top
    (le_of_eq (spacesPhysicalCellMeasure_scale n).symm)

private theorem spacesCellRestoreMeasure_ae (n : ℤ) (u : SpacesCellL2 E n) :
    (spacesCellRestoreMeasure E n u : PolarPoint → E) =ᵐ[
      materialCylinderMeasure.restrict (spacesPhysicalCellRadialSet n)] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

/-- Zero extension from a normalized physical cell to the actual cylinder. -/
def spacesPhysicalCellToCylinder (n : ℤ) :
    SpacesCellL2 E n →L[ℝ] Lp E 2 materialCylinderMeasure :=
  (spacesLpZeroExtension materialCylinderMeasure (spacesPhysicalCellRadialSet n)
    (spacesPhysicalCellRadialSet_measurable n)).toContinuousLinearMap.comp
    (spacesCellRestoreMeasure E n)

theorem spacesPhysicalCellToCylinder_ae (n : ℤ) (u : SpacesCellL2 E n) :
    (spacesPhysicalCellToCylinder E n u : PolarPoint → E) =ᵐ[materialCylinderMeasure]
      (spacesPhysicalCellRadialSet n).indicator u := by
  have hr := (ae_restrict_iff' (spacesPhysicalCellRadialSet_measurable n)).mp
    (spacesCellRestoreMeasure_ae E n u)
  filter_upwards [spacesLpZeroExtension_ae materialCylinderMeasure (spacesPhysicalCellRadialSet n)
    (spacesPhysicalCellRadialSet_measurable n) (spacesCellRestoreMeasure E n u), hr] with p hp hr
  change (spacesLpZeroExtension materialCylinderMeasure _
    (spacesPhysicalCellRadialSet_measurable n) (spacesCellRestoreMeasure E n u) :
    PolarPoint → E) p = _
  rw [hp]
  by_cases hmem : p ∈ spacesPhysicalCellRadialSet n
  · simp only [indicator_of_mem hmem]
    exact hr hmem
  · simp only [indicator_of_notMem hmem]

theorem spacesPhysicalCellToCylinder_ae_of_ae (n : ℤ) (u : SpacesCellL2 E n)
    (f : PolarPoint → E) (hf : (u : PolarPoint → E) =ᵐ[spacesPhysicalCellMeasure n] f) :
    (spacesPhysicalCellToCylinder E n u : PolarPoint → E) =ᵐ[materialCylinderMeasure]
      (spacesPhysicalCellRadialSet n).indicator f := by
  have hr : (u : PolarPoint → E) =ᵐ[
      materialCylinderMeasure.restrict (spacesPhysicalCellRadialSet n)] f := by
    rw [spacesPhysicalCellRadialSet, ← spacesPhysicalCellMeasure_scale n]
    exact hf.filter_mono (Measure.ae_smul_measure_le _)
  have hc := (ae_restrict_iff' (spacesPhysicalCellRadialSet_measurable n)).mp hr
  filter_upwards [spacesPhysicalCellToCylinder_ae E n u, hc] with p hp hc
  rw [hp]
  by_cases hmem : p ∈ spacesPhysicalCellRadialSet n
  · simp only [indicator_of_mem hmem]
    exact hc hmem
  · simp only [indicator_of_notMem hmem]

theorem spacesPhysicalCellToCylinder_norm_le (n : ℤ) (u : SpacesCellL2 E n) :
    ‖spacesPhysicalCellToCylinder E n u‖ ≤ (6 * Real.pi) ^ (1 / 2 : ℝ) * ‖u‖ := by
  change ‖spacesLpZeroExtension materialCylinderMeasure _
    (spacesPhysicalCellRadialSet_measurable n) (spacesCellRestoreMeasure E n u)‖ ≤ _
  rw [spacesLpZeroExtension_norm]
  have hn : ‖spacesCellRestoreMeasure E n‖ ≤ (6 * Real.pi) ^ (1 / 2 : ℝ) := by
    have h := Lp.norm_LpToLpOfMeasureLeSMul_le (E := E) (p := 2)
      (μ := materialCylinderMeasure.restrict (spacesPhysicalCellRadialSet n))
      (ν := spacesPhysicalCellMeasure n) (c := ENNReal.ofReal (6 * Real.pi)) ENNReal.ofReal_ne_top
      (le_of_eq (spacesPhysicalCellMeasure_scale n).symm)
    simpa only [spacesCellRestoreMeasure, ENNReal.toReal_ofReal (by positivity : 0 ≤ 6 * Real.pi),
      ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  exact ((spacesCellRestoreMeasure E n).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg u))

theorem spacesCylinderToPhysicalCell_leftInverse (n : ℤ) (u : SpacesCellL2 E n) :
    spacesCylinderToPhysicalCell E n (spacesPhysicalCellToCylinder E n u) = u := by
  apply Lp.ext
  have he := (spacesPhysicalCellToCylinder_ae E n u).filter_mono
    (ae_mono (spacesPhysicalCellMeasure_le_cylinder n))
  filter_upwards [spacesCylinderToPhysicalCell_ae E n (spacesPhysicalCellToCylinder E n u), he,
    spacesPhysicalCellMeasure_ae_mem n] with p hp he hmem
  refine hp.trans (he.trans ?_)
  exact indicator_of_mem (show p ∈ spacesPhysicalCellRadialSet n from ⟨hmem.1, mem_univ _⟩) u

end ContinuousFlexibility.Statements
