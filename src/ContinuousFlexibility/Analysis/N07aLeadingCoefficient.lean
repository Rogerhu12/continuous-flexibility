import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Scalar.WeightedCoefficientAlgebra

/-!
# The actual leading physical coefficient in the normal bootstrap

The pointwise geometry already fixed by N01 keeps the leading coefficient
comparable to the reference radial weight. N03 preserves this coefficient
exactly. Its reciprocal therefore has arbitrarily small material growth,
without introducing a further ellipticity hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem n07a_leading_coefficient_numeric
    {W w Q Δ : ℝ} (hW : 0 < W)
    (hw : (1 / 2 : ℝ) ≤ w / W ∧ w / W ≤ 2)
    (hQ : (7 / 8 : ℝ) ≤ Q / w ∧ Q / w ≤ 9 / 8)
    (hΔ : (1 / 2 : ℝ) ≤ Δ ∧ Δ ≤ 3 / 2) :
    W / 8 ≤ Q * inverseDThreeHalves Δ ∧
      Q * inverseDThreeHalves Δ ≤ 16 * W := by
  have hwlo := (le_div_iff₀ hW).mp hw.1
  have hwhi := (div_le_iff₀ hW).mp hw.2
  have hwp : 0 < w := by linarith only [hW, hwlo]
  have hQlo := (le_div_iff₀ hwp).mp hQ.1
  have hQhi := (div_le_iff₀ hwp).mp hQ.2
  have hQWlo : (7 / 16 : ℝ) * W ≤ Q := by linarith only [hwlo, hQlo]
  have hQWhi : Q ≤ (9 / 4 : ℝ) * W := by linarith only [hwhi, hQhi]
  have hΔp : 0 < Δ := by linarith only [hΔ.1]
  have hslo : (1 / 2 : ℝ) ≤ Real.sqrt Δ :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hΔ.1])
  have hshi : Real.sqrt Δ ≤ 2 :=
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr (by linarith only [hΔ.2])
  have hdlo : (1 / 4 : ℝ) ≤ Δ * Real.sqrt Δ := by
    have h := mul_le_mul hΔ.1 hslo (by norm_num : (0 : ℝ) ≤ 1 / 2) hΔp.le
    norm_num at h ⊢
    exact h
  have hdhi : Δ * Real.sqrt Δ ≤ 3 := by
    have h := mul_le_mul hΔ.2 hshi (Real.sqrt_nonneg Δ)
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    norm_num at h ⊢
    exact h
  have hdp : 0 < Δ * Real.sqrt Δ :=
    mul_pos hΔp (Real.sqrt_pos.mpr hΔp)
  rw [inverseDThreeHalves, mul_one_div]
  constructor
  · apply (le_div_iff₀ hdp).mpr
    have h := mul_le_mul_of_nonneg_left hdhi
      (div_nonneg hW.le (by norm_num : (0 : ℝ) ≤ 8))
    linarith only [h, hQWlo, hW]
  · apply (div_le_iff₀ hdp).mpr
    have h := mul_le_mul_of_nonneg_left hdlo
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hW.le)
    linarith only [h, hQWhi, hW]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

private theorem n07a_reference_weight_pos
    (h01 : N01Properties D T S C base loss ε) {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    0 < D.w r :=
  h01.1.1.choose_spec.1.2.2.2.2.1 r hr

/-- The fixed N01 geometry gives a state-independent comparison with the
actual reference weight throughout the annular core. -/
theorem n07a_originalLeadingCoefficient_comparable
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    D.w p.1 / 8 ≤ (originalCoefficients D S C z).a p ∧
      (originalCoefficients D S C z).a p ≤ 16 * D.w p.1 := by
  obtain ⟨hwlo, hwhi, hQlo, hQhi, hΔlo, hΔhi⟩ :=
    h01.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  simpa only [originalCoefficients, polarLinearA, linearRadial, polarScale] using
    n07a_leading_coefficient_numeric (n07a_reference_weight_pos h01 hp.1)
      ⟨hwlo, hwhi⟩ ⟨hQlo, hQhi⟩ ⟨hΔlo, hΔhi⟩

/-- Return correction preserves the leading physical coefficient. -/
theorem n07a_correctedLeadingCoefficient_comparable
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    D.w p.1 / 8 ≤ (L.coefficients z).a p ∧
      (L.coefficients z).a p ≤ 16 * D.w p.1 := by
  rw [h03.1 z hz hs p]
  exact n07a_originalLeadingCoefficient_comparable h01 hz hs hp

theorem n07a_correctedLeadingCoefficient_pos
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < (L.coefficients z).a p :=
  (div_pos (n07a_reference_weight_pos h01 hp.1) (by norm_num)).trans_le
    (n07a_correctedLeadingCoefficient_comparable h01 h03 hz hs hp).1

theorem n07a_correctedLeadingCoefficient_inverse_bound
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    |((L.coefficients z).a p)⁻¹| ≤ 8 / D.w p.1 := by
  have ha := n07a_correctedLeadingCoefficient_pos h01 h03 hz hs hp
  rw [abs_inv, abs_of_pos ha]
  have h := inv_anti₀
    (div_pos (n07a_reference_weight_pos h01 hp.1) (by norm_num : (0 : ℝ) < 8))
    (n07a_correctedLeadingCoefficient_comparable h01 h03 hz hs hp).1
  simpa only [inv_div] using h

/-- The complete reciprocal leading coefficient costs any prescribed
positive material power, uniformly over the current state neighborhood. -/
theorem n07a_correctedLeadingCoefficient_inverse_subpower
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : AnnularState S × ℝ,
      z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
      ∀ p ∈ annularOpen D,
        |((L.coefficients z).a p)⁻¹| ≤ A * T.M p.1 ^ δ := by
  obtain ⟨A, hA, hAb⟩ := referenceInverseJet_le_subpowerM h01.1.1 hT 0 hδ
  refine ⟨8 * A, mul_pos (by norm_num) hA, ?_⟩
  intro z hz hs p hp
  have hw := n07a_reference_weight_pos h01 hp.1
  have href : (D.w p.1)⁻¹ ≤ A * T.M p.1 ^ δ := by
    simpa only [radialJet, abs_of_pos (inv_pos.mpr hw)] using hAb p.1 hp.1
  calc
    _ ≤ 8 / D.w p.1 := n07a_correctedLeadingCoefficient_inverse_bound h01 h03 hz hs hp
    _ = 8 * (D.w p.1)⁻¹ := div_eq_mul_inv _ _
    _ ≤ 8 * (A * T.M p.1 ^ δ) := mul_le_mul_of_nonneg_left href (by norm_num)
    _ = (8 * A) * T.M p.1 ^ δ := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Analysis
