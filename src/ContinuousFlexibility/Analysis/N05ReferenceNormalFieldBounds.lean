import ContinuousFlexibility.Analysis.N05ReferenceZeroRemainder
import ContinuousFlexibility.Analysis.N05ReferenceNormalCoefficientBounds
import ContinuousFlexibility.Analysis.N05ReferenceOutputMultiplier
import ContinuousFlexibility.Analysis.N05ReferenceFullAngularSobolev

/-!
# Weighted bounds for the actual canonical radial field

Both coefficients have one common material exponent. Multiplication and
subtraction therefore put the genuine radial field in a fixed weaker
reference output space, uniformly before any angular order is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial

theorem n05ReferenceRadialNormalField_weighted_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ γ M (u ur : PolarPoint → ℝ),
      MemLp u 2 (referenceWeightedMeasure D γ (-M)) →
      MemLp ur 2 (referenceWeightedMeasure D γ (-M)) →
      MemLp (n05ReferenceRadialNormalField S C K u ur) 2
        (referenceWeightedMeasure D γ (-(M + A))) ∧
      outputNormSquare D γ (M + A) 0 (n05ReferenceRadialNormalField S C K u ur, 0) ≤
        B * (outputNormSquare D γ M 0 (u, 0) + outputNormSquare D γ M 0 (ur, 0)) := by
  obtain ⟨C0, L0, hC0, hL0, hb⟩ :=
    n05ReferenceNormal_coefficients_cell_bound hcoordinates hD hT h
  obtain ⟨hm₁, hm₀⟩ := n05ReferenceNormal_coefficients_measurable h hcoordinates
  have hab := hD.choose_spec.1.2.1.le
  have hpart := hD.choose_spec.2.1
  refine ⟨2 * C0, L0 / 2, by positivity, by positivity, fun γ M u ur hu hur => ?_⟩
  obtain ⟨hcu, hsu⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hu
  obtain ⟨hcr, hsr⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hur
  rw [sourceCellSquare_neg_fun] at hsu hsr
  obtain ⟨hc₁, hs₁, hn₁⟩ := n05_referenceOutput_multiplier_bound hab
    hm₁.aestronglyMeasurable hC0.le
    (fun j => Eventually.of_forall fun p hp => (hb j p hp).1) γ M hcr hsr
  obtain ⟨hc₀, hs₀, hn₀⟩ := n05_referenceOutput_multiplier_bound hab
    hm₀.aestronglyMeasurable hC0.le
    (fun j => Eventually.of_forall fun p hp => (hb j p hp).2) γ M hcu hsu
  let a : PolarPoint → ℝ := fun p => n05ReferenceNormalLeading S C K p * ur p
  let b : PolarPoint → ℝ := fun p => n05ReferenceNormalDrift S C K p * u p
  have ha : MemLp a 2 (referenceWeightedMeasure D γ (-(M + L0 / 2))) :=
    memLp_referenceWeightedMeasure hab hpart hc₁ (by simpa only [sourceCellSquare_neg_fun] using hs₁)
  have hb' : MemLp b 2 (referenceWeightedMeasure D γ (-(M + L0 / 2))) :=
    memLp_referenceWeightedMeasure hab hpart hc₀ (by simpa only [sourceCellSquare_neg_fun] using hs₀)
  have hg : MemLp (n05ReferenceRadialNormalField S C K u ur) 2
      (referenceWeightedMeasure D γ (-(M + L0 / 2))) := ha.sub hb'
  have hnorm₁ : outputNormSquare D γ (M + L0 / 2) 0 (a, 0) ≤
      C0 * outputNormSquare D γ M 0 (ur, 0) := by
    simpa only [outputNormSquare, n05_outputRemainder_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hn₁
  have hnorm₀ : outputNormSquare D γ (M + L0 / 2) 0 (b, 0) ≤
      C0 * outputNormSquare D γ M 0 (u, 0) := by
    simpa only [outputNormSquare, n05_outputRemainder_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hn₀
  have hneg : outputNormSquare D γ (M + L0 / 2) 0 (-b, 0) =
      outputNormSquare D γ (M + L0 / 2) 0 (b, 0) := by
    rw [n05_referenceZeroOutputNormSquare_eq_integral hab hpart hb'.neg,
      n05_referenceZeroOutputNormSquare_eq_integral hab hpart hb']
    simp only [Pi.neg_apply, neg_sq]
  refine ⟨hg, ?_⟩
  have hsum := n05_referenceZeroOutputNormSquare_add_le hab hpart ha hb'.neg
  rw [hneg] at hsum
  have hfield : n05ReferenceRadialNormalField S C K u ur = a + -b := by
    funext p
    exact sub_eq_add_neg _ _
  rw [hfield]
  calc
    _ ≤ 2 * (outputNormSquare D γ (M + L0 / 2) 0 (a, 0) +
        outputNormSquare D γ (M + L0 / 2) 0 (b, 0)) := hsum
    _ ≤ 2 * (C0 * outputNormSquare D γ M 0 (ur, 0) +
        C0 * outputNormSquare D γ M 0 (u, 0)) :=
      mul_le_mul_of_nonneg_left (add_le_add hnorm₁ hnorm₀) (by norm_num)
    _ = _ := by ring

end ContinuousFlexibility.Statements
