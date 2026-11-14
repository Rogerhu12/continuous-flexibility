module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Real and complex value maps on actual `L²` classes

Complexification is isometric and taking real parts is contractive. Their
composition is exactly the identity on the original real classes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter MeasureTheory
open scoped ENNReal ComplexConjugate

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

def spacesLpComplexification : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  Complex.ofRealCLM.compLpL 2 μ

theorem spacesLpComplexification_ae (u : Lp ℝ 2 μ) :
    (spacesLpComplexification μ u : α → ℂ) =ᵐ[μ] fun x => (u x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL u

theorem spacesLpComplexification_norm (u : Lp ℝ 2 μ) :
    ‖spacesLpComplexification μ u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.memLp _).aestronglyMeasurable (Lp.memLp u).aestronglyMeasurable
  filter_upwards [spacesLpComplexification_ae μ u] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs]

def spacesLpRealPart : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  Complex.reCLM.compLpL 2 μ

theorem spacesLpRealPart_ae (u : Lp ℂ 2 μ) :
    (spacesLpRealPart μ u : α → ℝ) =ᵐ[μ] fun x => (u x).re :=
  Complex.reCLM.coeFn_compLpL u

theorem spacesLpRealPart_norm_le (u : Lp ℂ 2 μ) : ‖spacesLpRealPart μ u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [spacesLpRealPart_ae μ u] with x hx
  rw [hx, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem spacesLpRealPart_complexification (u : Lp ℝ 2 μ) :
    spacesLpRealPart μ (spacesLpComplexification μ u) = u := by
  apply Lp.ext
  filter_upwards [spacesLpRealPart_ae μ (spacesLpComplexification μ u),
    spacesLpComplexification_ae μ u] with x hr hc
  rw [hr, hc, Complex.ofReal_re]

theorem spacesLpComplexification_real (u : Lp ℝ 2 μ) :
    (fun x => conj (spacesLpComplexification μ u x)) =ᵐ[μ] spacesLpComplexification μ u := by
  filter_upwards [spacesLpComplexification_ae μ u] with x hx
  rw [hx, Complex.conj_ofReal]

theorem spacesLpComplexification_realPart (u : Lp ℂ 2 μ)
    (hu : (fun x => conj (u x)) =ᵐ[μ] u) :
    spacesLpComplexification μ (spacesLpRealPart μ u) = u := by
  apply Lp.ext
  filter_upwards [spacesLpComplexification_ae μ (spacesLpRealPart μ u),
    spacesLpRealPart_ae μ u, hu] with x hc hr hreal
  rw [hc, hr]
  exact Complex.conj_eq_iff_re.mp hreal

end ContinuousFlexibility.Analysis
