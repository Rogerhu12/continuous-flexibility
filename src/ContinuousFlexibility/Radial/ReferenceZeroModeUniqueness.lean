module

public import ContinuousFlexibility.Radial.ReferenceZeroModeGraph
public import ContinuousFlexibility.Radial.ReferenceCosineCoordinates
public import ContinuousFlexibility.Radial.ZeroModeHomogeneousUniqueness

/-!
# Uniqueness of the actual zero channel

The zero coefficient of the actual output remainder belongs to the
weighted radial L² space. The ordinary angular mean differs from this
coefficient by exactly the prescribed left constant. Thus the weak
homogeneous representation and endpoint exclusion apply to the same
domain as the frozen two-dimensional graph.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal

theorem radialAngularMean_add_const {f : ℝ → ℝ}
    (hf : Integrable f referenceAngularMeasure) (c : ℝ) :
    radialAngularMean (fun θ => f θ + c) = radialAngularMean f + c := by
  calc
    radialAngularMean (fun θ => f θ + c) =
        ∫ θ, f θ + c ∂referenceAngularMeasure :=
      (integral_referenceAngularMeasure _).symm
    _ = (∫ θ, f θ ∂referenceAngularMeasure) + c := by
      rw [integral_add hf (integrable_const c)]
      simp
    _ = radialAngularMean f + c := by rw [integral_referenceAngularMeasure]

theorem OutputRealization.angularMean_remainder_memLp {D : ReferenceData}
    (hab : D.a ≤ D.b) (hP : RadialPartition D)
    {γ M aL : ℝ} {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) :
    MemLp (fun r => radialAngularMean (fun θ => U.1 (r, θ)) - aL * D.chiLeft r)
      2 (referenceRadialWeightedMeasure D γ (-M)) := by
  have hR : MemLp (outputRemainder D aL U) 2
      ((referenceRadialWeightedMeasure D γ (-M)).prod referenceAngularMeasure) := by
    simpa only [referenceWeightedMeasure_eq_prod hP γ (-M)] using
      hU.memLp_weighted hab hP
  have he :
      referenceCosineCoefficient (outputRemainder D aL U) 0 =ᵐ[
        referenceRadialWeightedMeasure D γ (-M)]
        (fun r => radialAngularMean (fun θ => U.1 (r, θ)) - aL * D.chiLeft r) := by
    filter_upwards [memLp_two_prod_sections hR] with r hr
    have hi := hr.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hp : (fun θ => U.1 (r, θ)) =
        (fun θ => outputRemainder D aL U (r, θ) + aL * D.chiLeft r) := by
      funext θ
      dsimp only [outputRemainder]
      ring
    have hm : radialAngularMean (fun θ => U.1 (r, θ)) =
        radialAngularMean (fun θ => outputRemainder D aL U (r, θ)) +
          aL * D.chiLeft r := by
      rw [hp]
      exact radialAngularMean_add_const hi _
    simp only [referenceCosineCoefficient, referenceCosineCoeff_zero, hm, add_sub_cancel_right]
  exact (memLp_congr_ae he).mp (hU.remainder_cosineCoefficient_memLp hab hP 0)

/-- The actual maximum weak graph has no nonzero homogeneous zero mode. -/
theorem ReferenceGraph.zeroMode_eq_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hG : ReferenceGraph D γ M₀ M₁ U 0) :
    (fun r => radialAngularMean (fun θ => U.1 (r, θ))) =ᵐ[
      volume.restrict (radialCore D)] (fun _ => (0 : ℝ)) := by
  obtain ⟨C, hC⟩ := hD
  obtain ⟨A, B, hrep⟩ := hG.zeroMode_ae_affine_resistance ⟨C, hC⟩ hB
  obtain ⟨aL, hU⟩ := hG.1
  have hc : (D.a + D.b) / 2 ∈ radialCore D := by
    have hab := hC.1.2.1
    constructor <;> linarith
  have hrep' :
      (fun r => radialAngularMean (fun θ => U.1 (r, θ))) =ᵐ[
        volume.restrict (radialCore D)]
        (fun r => A + B * (∫ s in ((D.a + D.b) / 2)..r, (D.w s)⁻¹)) := by
    simpa only [Radial.zeroModeResistance, one_div] using hrep
  exact (Radial.zeroMode_homogeneous_representative_eq_zero hC hB hγ hc
    (hU.angularMean_remainder_memLp hC.1.2.1.le hC.2.1) hrep').2.2

end ContinuousFlexibility.Statements
