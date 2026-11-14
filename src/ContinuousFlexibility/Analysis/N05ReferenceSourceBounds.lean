module

public import ContinuousFlexibility.Analysis.N05ReferenceSourceCompatibility
public import ContinuousFlexibility.Radial.R11bModeL2

/-!
# Bounds for the actual source compatibility correction

The auxiliary scalar is the actual normalized physical integral. Physical
L² control and Cauchy--Schwarz bound it by the original reference source
square sum. The compact normalizer then preserves that square estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Radial

theorem n05_referenceAuxiliaryScalar_square_bound
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : PolarPoint → ℝ,
      SourceDerivativeMember D γ M f →
      (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) ^ 2 ≤
        C * ∑' m, sourceCellSquare D γ M f m := by
  have hab := hD.choose_spec.1.2.1.le
  obtain ⟨K, hK, hphysical⟩ :=
    r11b_cell_weighted_L2_bound hD.choose_spec.2.1 hab (2 * M) γ hγ
  let q : ℝ := (2 * Real.pi)⁻¹ ^ 2 *
    ∫ p : PolarPoint, (1 : ℝ) ^ 2 ∂radialPhysicalMeasure D
  have hq : 0 ≤ q := mul_nonneg (sq_nonneg _)
    (integral_nonneg (fun _ => sq_nonneg (1 : ℝ)))
  refine ⟨q * K + 1, by positivity, fun f hf => ?_⟩
  have hLp := (hphysical f hf.1 hf.2).1
  have hI : (∫ p, f p ^ 2 ∂radialPhysicalMeasure D) ≤
      K * ∑' m, sourceCellSquare D γ M f m := (hphysical f hf.1 hf.2).2
  letI : IsFiniteMeasure (radialPhysicalMeasure D) :=
    ⟨r11b_radialPhysicalMeasure_finite D⟩
  have h1 : MemLp (fun _ : PolarPoint => (1 : ℝ)) 2 (radialPhysicalMeasure D) :=
    memLp_const 1
  have hCS : (∫ p, f p ∂radialPhysicalMeasure D) ^ 2 ≤
      (∫ p, f p ^ 2 ∂radialPhysicalMeasure D) *
        ∫ p : PolarPoint, (1 : ℝ) ^ 2 ∂radialPhysicalMeasure D := by
    simpa only [mul_one] using r11b_integral_mul_sq_le hLp h1
  have hsum : 0 ≤ ∑' m, sourceCellSquare D γ M f m :=
    tsum_nonneg (fun m => sourceCellSquare_nonneg hab γ M hf.1 m)
  calc
    _ = (2 * Real.pi)⁻¹ ^ 2 * (∫ p, f p ∂radialPhysicalMeasure D) ^ 2 := by
      rw [r11b_integral_angularMean_eq hab (hLp.integrable (by norm_num)), mul_pow]
    _ ≤ (2 * Real.pi)⁻¹ ^ 2 *
        ((∫ p, f p ^ 2 ∂radialPhysicalMeasure D) *
          ∫ p : PolarPoint, (1 : ℝ) ^ 2 ∂radialPhysicalMeasure D) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = q * ∫ p, f p ^ 2 ∂radialPhysicalMeasure D := by dsimp only [q]; ring
    _ ≤ q * (K * ∑' m, sourceCellSquare D γ M f m) :=
      mul_le_mul_of_nonneg_left hI hq
    _ = (q * K) * ∑' m, sourceCellSquare D γ M f m := (mul_assoc _ _ _).symm
    _ ≤ (q * K + 1) * ∑' m, sourceCellSquare D γ M f m :=
      mul_le_mul_of_nonneg_right (by linarith) hsum

/-- Subtracting the actual normalized auxiliary column is bounded in the
original reference source weights; its scalar is included in the estimate. -/
theorem n05_referenceSource_normalized_square_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : PolarPoint → ℝ,
      SourceDerivativeMember D γ M f →
      let a := ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))
      a ^ 2 + sourceNormSquare D γ M
        ((fun p => f p - a * (S.height (3 / 4 : ℝ)).decode S.psi p), 0) ≤
          C * sourceNormSquare D γ M (f, 0) := by
  obtain ⟨K, hK, hscalar⟩ := n05_referenceAuxiliaryScalar_square_bound hD hγ M
  let ψ : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode S.psi
  have hψ := n05_physicalNormalizer_sourceDerivativeMember hD hS γ M
  let Z : ℝ := ∑' m, sourceCellSquare D γ M ψ m
  have hab := hD.choose_spec.1.2.1.le
  have hZ : 0 ≤ Z := tsum_nonneg (fun m => sourceCellSquare_nonneg hab γ M hψ.1 m)
  refine ⟨K + 2 * (1 + K * Z), by positivity, fun f hf => ?_⟩
  dsimp only
  let a : ℝ := ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))
  have hscaled := hψ.1.const_mul (-a)
  have hscaledSum := sourceCellSquare_summable_const_mul hψ.2 (-a)
  have htotal := sourceCellSquare_summable_add hab hf.1 hscaled hf.2 hscaledSum
  have hbound := htotal.tsum_le_tsum
    (fun m => sourceCellSquare_add_le hab γ M m hf.1 hscaled)
    ((hf.2.add hscaledSum).mul_left 2)
  have hsumScaled : (∑' m, sourceCellSquare D γ M (fun p => (-a) * ψ p) m) =
      a ^ 2 * Z := by
    simp_rw [sourceCellSquare_const_mul, neg_sq]
    exact tsum_mul_left
  rw [tsum_mul_left, hf.2.tsum_add hscaledSum, hsumScaled] at hbound
  have heq : (fun p => f p - a * ψ p) = (fun p => f p + (-a) * ψ p) := by
    funext p
    ring
  change a ^ 2 + (0 ^ 2 + ∑' m, sourceCellSquare D γ M (fun p => f p - a * ψ p) m) ≤
    (K + 2 * (1 + K * Z)) * (0 ^ 2 + ∑' m, sourceCellSquare D γ M f m)
  rw [heq, zero_pow (by norm_num : 2 ≠ 0), zero_add, zero_add]
  have hscalarBound := hscalar f hf
  change a ^ 2 ≤ K * ∑' m, sourceCellSquare D γ M f m at hscalarBound
  nlinarith only [hbound, hscalarBound,
    mul_le_mul_of_nonneg_right hscalarBound hZ]

end ContinuousFlexibility.Statements
