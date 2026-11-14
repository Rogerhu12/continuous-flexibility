module

public import ContinuousFlexibility.Radial.R11bPhysicalMultiplier
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The reciprocal physical density on attenuated source and output remainders

The inverse coefficient's zeroth cell estimate bounds the square of its
square-root multiplier. Strict positive attenuation then gives genuine L²
membership in the physical measure. The output statement retains the
subtracted left constant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements

theorem r11b_inverse_sqrt_cell_bound {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) (m : ℕ) (r : ℝ)
    (hr : D.localizer m r ≠ 0) :
    |sqrt ((D.w r)⁻¹)| ^ 2 ≤ C 0 * exp (C 0 * radialQ (D.cellIndex m)) := by
  obtain ⟨hgeom, hpart, _, _, _, _, _, _, _, hinv, _⟩ := hD
  have hcell : r ∈ D.cells m := hpart.2.2.1 m hr
  have hw : 0 < D.w r := hgeom.2.2.2.2.1 r (hpart.2.2.2.1 m hcell)
  have hw_inv : 0 ≤ (D.w r)⁻¹ := inv_nonneg.mpr hw.le
  calc
    |sqrt ((D.w r)⁻¹)| ^ 2 = (D.w r)⁻¹ := by rw [sq_abs, sq_sqrt hw_inv]
    _ ≤ C 0 * radialE (D.cellIndex m) ^ (C 0) := by
      simpa only [radialJet, abs_of_nonneg hw_inv] using hinv m r hcell 0
    _ = C 0 * exp (C 0 * radialQ (D.cellIndex m)) := by
      rw [radialE, ← exp_mul, mul_comm (radialQ (D.cellIndex m)) (C 0)]

theorem r11b_cell_inverse_sqrt_L2_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (A γ : ℝ) (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : PolarPoint → ℝ, RadialCellIntegrable D f →
      Summable (fun m => exp (A * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f) →
      MemLp (fun x => sqrt ((D.w x.1)⁻¹) * f x) 2 (radialPhysicalMeasure D) ∧
        (∫ x, (sqrt ((D.w x.1)⁻¹) * f x) ^ 2 ∂radialPhysicalMeasure D) ≤
          K * ∑' m, exp (A * radialQ (D.cellIndex m) +
            2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f := by
  obtain ⟨C, hD⟩ := hD
  have hgeom := hD.1
  have hpart := hD.2.1
  have ha : AEStronglyMeasurable (fun x : PolarPoint => sqrt ((D.w x.1)⁻¹))
      (radialPhysicalMeasure D) :=
    (((hgeom.2.2.1.1.continuous.measurable.comp measurable_fst).inv).sqrt).aestronglyMeasurable
  exact r11b_cell_multiplier_L2_bound hpart hgeom.2.1.le
    (fun x => sqrt ((D.w x.1)⁻¹)) ha (C 0) (C 0) A γ (hD.2.2.1 0).le hγ
    (fun m => Filter.Eventually.of_forall fun x hx =>
      r11b_inverse_sqrt_cell_bound hD m x.1 hx)

theorem r11b_source_inverse_sqrt_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {F : RadialSource} (hF : SourceMember D γ M F) :
    MemLp (fun x => sqrt ((D.w x.1)⁻¹) * F.1 x) 2 (radialPhysicalMeasure D) := by
  obtain ⟨_, _, h⟩ := r11b_cell_inverse_sqrt_L2_bound hD (2 * M) γ hγ
  exact (h F.1 hF.1 hF.2.1).1

theorem r11b_sourceDerivative_inverse_sqrt_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {fθ : PolarPoint → ℝ} (hfθ : SourceDerivativeMember D γ M fθ) :
    MemLp (fun x => sqrt ((D.w x.1)⁻¹) * fθ x) 2 (radialPhysicalMeasure D) := by
  obtain ⟨_, _, h⟩ := r11b_cell_inverse_sqrt_L2_bound hD (2 * M) γ hγ
  exact (h fθ hfθ.1 hfθ.2).1

theorem r11b_outputRemainder_inverse_sqrt_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M aL : ℝ} (hγ : 0 < γ)
    {U : RadialUnknown} (hU : OutputRealization D γ M aL U) :
    MemLp (fun x => sqrt ((D.w x.1)⁻¹) * outputRemainder D aL U x)
      2 (radialPhysicalMeasure D) := by
  obtain ⟨_, _, h⟩ := r11b_cell_inverse_sqrt_L2_bound hD (-2 * M) γ hγ
  exact (h (outputRemainder D aL U) hU.1 hU.2.1).1

end ContinuousFlexibility.Radial
