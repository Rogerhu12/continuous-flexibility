import ContinuousFlexibility.Analysis.N05ReferenceAngularJetCells
import ContinuousFlexibility.Radial.ReferenceWeightedProduct

/-!
# The actual singleton energy in the weighted radial marginal

A single finite cosine projection is square integrable precisely as the
corresponding radial coefficient. Product disintegration and normalized
angular Parseval identify its frozen source norm with the coefficient
square integral, including the original measure normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceWeighted_singleCoefficient {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) {γ M : ℝ}
    {f : PolarPoint → ℝ} (n : ℕ)
    (hp : MemLp (referenceBasisProjection {n + 2} f) 2
      (referenceWeightedMeasure D γ M)) :
    MemLp (referenceRadialCoefficient f (n + 2)) 2
        (referenceRadialWeightedMeasure D γ M) ∧
      (∫ r, referenceRadialCoefficient f (n + 2) r ^ 2
        ∂referenceRadialWeightedMeasure D γ M) =
        sourceNormSquare D γ M (referenceBasisProjection {n + 2} f, 0) := by
  have hcoeff : referenceRadialCoefficient (referenceBasisProjection {n + 2} f) (n + 2) =
      referenceRadialCoefficient f (n + 2) := by
    funext r
    simpa only [referenceRadialCoefficient, referenceBasisProjection,
      ite_eq_left (Finset.mem_singleton_self (n + 2))] using
      referenceAngularCoefficient_projection {n + 2} (fun θ => f (r, θ)) (n + 2)
  have hc := memLp_referenceRadialCoefficient hpart hp (n + 2)
  rw [hcoeff] at hc
  have hinner (r : ℝ) :
      radialAngularMean (fun θ => referenceBasisProjection {n + 2} f (r, θ) ^ 2) =
        referenceRadialCoefficient f (n + 2) r ^ 2 := by
    simpa only [referenceBasisProjection, referenceRadialCoefficient, Finset.sum_singleton] using
      angularBasisProjection_sq {n + 2} (fun θ => f (r, θ))
  have heq := integral_referenceWeightedMeasure_eq_radial hpart hp.integrable_sq
  simp_rw [hinner] at heq
  obtain ⟨hl, hs⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hp
  refine ⟨hc, ?_⟩
  calc
    (∫ r, referenceRadialCoefficient f (n + 2) r ^ 2
        ∂referenceRadialWeightedMeasure D γ M) =
        ∫ x, referenceBasisProjection {n + 2} f x ^ 2
          ∂referenceWeightedMeasure D γ M := heq.symm
    _ = ∑' m, sourceCellSquare D γ M (referenceBasisProjection {n + 2} f) m :=
      integral_sq_referenceWeightedMeasure_eq hab hpart hl hs
    _ = sourceNormSquare D γ M (referenceBasisProjection {n + 2} f, 0) := by
      simp only [sourceNormSquare, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]

theorem n05_zeroOutputNormSquare_eq_sourceNormSquare_neg (D : ReferenceData)
    (γ M : ℝ) (f : PolarPoint → ℝ) :
    outputNormSquare D γ M 0 (f, 0) = sourceNormSquare D γ (-M) (f, 0) := by
  have hzero : outputRemainder D 0 (f, 0) = f := by
    funext p
    simp only [outputRemainder, zero_mul, sub_zero]
  simp only [outputNormSquare, sourceNormSquare, hzero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, sourceCellSquare_neg_fun]

end ContinuousFlexibility.Radial
