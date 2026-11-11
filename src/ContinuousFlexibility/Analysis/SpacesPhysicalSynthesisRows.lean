import ContinuousFlexibility.Analysis.SpacesPhysicalCellBands
import ContinuousFlexibility.Analysis.SpacesRadialWeightOverlap

/-!
# Weighted row operators for physical synthesis

The derivative of an envelope is combined with the ratio between the
actual material weight and its value at the cell center. Its square-sum
bound gives a bounded gluing map. The remaining center weight is placed
on the finite Fourier jet, where the joint spectral band controls it.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal NNReal BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

abbrev SpacesPhysicalIntegerRows := lp (fun _ : ℤ => CylinderL2) 2

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

def spacesPhysicalEnvelopeMultiplier (a c : ℕ) (n : ℤ) (p : PolarPoint) : ℝ :=
  iteratedDeriv a (spacesRadialEnvelope n) p.1 *
    (T.M (T.radius p.1) ^ c / T.M (T.radius n) ^ c)

include hT

theorem spacesPhysicalEnvelopeMultiplier_continuous (a c : ℕ) (n : ℤ) :
    Continuous (spacesPhysicalEnvelopeMultiplier (T := T) a c n) := by
  obtain ⟨hs, _, _, _, _, _, hr, hi, _⟩ := hT
  have hM : ContDiffOn ℝ ∞ T.M (Ioo D.a D.b) := hs T.M (by simp)
  have hm : Continuous (fun x => T.M (T.radius x)) :=
    (hM.comp_contDiff hr (fun x => (hi x).1)).continuous
  exact (((spacesRadialEnvelope_contDiff n).continuous_iteratedDeriv a (by simp)).comp
    continuous_fst).mul (((hm.comp continuous_fst).pow c).div_const _)

def spacesPhysicalEnvelopeConstant (a c : ℕ) : ℝ≥0 :=
  ⟨(spacesRadialEnvelope_weighted_derivative_overlap hT a c).choose,
    (spacesRadialEnvelope_weighted_derivative_overlap hT a c).choose_spec.1⟩

theorem spacesPhysicalEnvelopeConstant_bound (a c : ℕ) (s : Finset ℤ) (p : PolarPoint) :
    ∑ n ∈ s, spacesPhysicalEnvelopeMultiplier (T := T) a c n p ^ 2 ≤
      (spacesPhysicalEnvelopeConstant hT a c : ℝ) ^ 2 :=
  (spacesRadialEnvelope_weighted_derivative_overlap hT a c).choose_spec.2 s p.1

/-- Gluing by the weighted actual derivative of each radial envelope. -/
def spacesPhysicalEnvelopeSynthesis (a c : ℕ) : SpacesPhysicalIntegerRows →L[ℝ] CylinderL2 :=
  spacesLpOverlapSynthesis materialCylinderMeasure (spacesPhysicalEnvelopeMultiplier (T := T) a c)
    (fun n => (spacesPhysicalEnvelopeMultiplier_continuous hT a c n).aestronglyMeasurable)
    (spacesPhysicalEnvelopeConstant hT a c) (spacesPhysicalEnvelopeConstant hT a c).property
    (spacesPhysicalEnvelopeConstant_bound hT a c)

theorem spacesPhysicalEnvelopeSynthesis_norm_le (a c : ℕ) (u : SpacesPhysicalIntegerRows) :
    ‖spacesPhysicalEnvelopeSynthesis hT a c u‖ ≤ (spacesPhysicalEnvelopeConstant hT a c : ℝ) * ‖u‖ :=
  spacesLpOverlapSynthesis_norm_le _ _ _ _ _ _ u

theorem spacesPhysicalEnvelopeSynthesis_single_ae (a c : ℕ) (n : ℤ) (u : CylinderL2) :
    (spacesPhysicalEnvelopeSynthesis hT a c (lp.single 2 n u) : PolarPoint → ℝ) =ᵐ[
      materialCylinderMeasure] fun p => spacesPhysicalEnvelopeMultiplier (T := T) a c n p * u p := by
  rw [spacesPhysicalEnvelopeSynthesis, spacesLpOverlapSynthesis_single]
  exact spacesLpMultiplier_ae _ _ _ _ _ u

theorem spaces_material_M_one_le (x : ℝ) : 1 ≤ T.M (T.radius x) := by
  obtain ⟨_, hp, _, _, _, _, _, hi, _⟩ := hT
  exact (hp _ (hi x).1).2.2.2

def spacesPhysicalFourierGrowthConstant (s : ℕ) : ℝ≥0 :=
  ⟨(6 * Real.pi) ^ (1 / 2 : ℝ) * Real.exp (s : ℝ), by positivity⟩

/-- Coordinatewise projected mixed jets, carrying the center weight. -/
def spacesPhysicalSynthesisJetRows (a b c s : ℕ) (hord : a + b + c ≤ s) (k : ℕ) :
    SpacesPhysicalIntegerRows →L[ℝ] SpacesPhysicalIntegerRows :=
  lpSpectralDiagonal
    (fun n => T.M (T.radius n) ^ c • spacesPhysicalCellBand n (T.M (T.radius n)) k a b)
    (show 0 ≤ (spacesPhysicalFourierGrowthConstant s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) by positivity)
    (fun n u => spacesPhysicalCellBand_weighted_norm_le n (T.M (T.radius n))
      (spaces_material_M_one_le hT n) k a b c s hord u)

theorem spacesPhysicalSynthesisJetRows_apply (a b c s : ℕ) (hord : a + b + c ≤ s)
    (k : ℕ) (u : SpacesPhysicalIntegerRows) (n : ℤ) :
    spacesPhysicalSynthesisJetRows hT a b c s hord k u n =
      T.M (T.radius n) ^ c • spacesPhysicalCellBand n (T.M (T.radius n)) k a b (u n) := by
  rw [spacesPhysicalSynthesisJetRows, lpSpectralDiagonal_apply, smul_apply]

theorem spacesPhysicalSynthesisJetRows_norm_le (a b c s : ℕ) (hord : a + b + c ≤ s)
    (k : ℕ) (u : SpacesPhysicalIntegerRows) :
    ‖spacesPhysicalSynthesisJetRows hT a b c s hord k u‖ ≤
      (spacesPhysicalFourierGrowthConstant s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) * ‖u‖ :=
  lpSpectralDiagonal_norm_le _ _ _ u

theorem spacesPhysicalSynthesisJetRows_single (a b c s : ℕ) (hord : a + b + c ≤ s)
    (k : ℕ) (n : ℤ) (u : CylinderL2) :
    spacesPhysicalSynthesisJetRows hT a b c s hord k (lp.single 2 n u) =
      lp.single 2 n (T.M (T.radius n) ^ c • spacesPhysicalCellBand n (T.M (T.radius n)) k a b u) := by
  apply lp.ext
  funext m
  rw [spacesPhysicalSynthesisJetRows_apply]
  by_cases hm : m = n
  · subst m
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ hm, lp.single_apply_ne _ _ _ hm, map_zero, smul_zero]

end ContinuousFlexibility.Statements
