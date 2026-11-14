module

public import ContinuousFlexibility.Analysis.MaterialOneSidedEndpointComparison
public import ContinuousFlexibility.Analysis.N04RealizationEnvelopeAlgebra
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Converting actual sample costs to the physical point

The given endpoint-coordinate comparison controls the actual height
ratio and the sampled coefficient base. A finite polynomial envelope
using both sample and point costs then becomes a pointwise E0 envelope
with an ordinary natural state degree. Every index and sample is retained.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

/-- The same one-sided displacement supplies both scalar inputs needed
by the primitive normalizer and the final coefficient-base conversion. -/
theorem n04Realization_material_sample_value_envelopes
    {X : Type*} {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (point sample : X → ℝ)
    (hp : ∀ x, point x ∈ Ioo D.a D.b)
    (hs : ∀ x, sample x ∈ Ioo D.a D.b)
    (hE : ∀ x, 1 ≤ T.E0 (point x))
    {L : ℝ} (hL : 0 ≤ L)
    (hshift : ∀ x, endpointX 1 (Statements.endpointDistance D (sample x)) ≤
      endpointX 1 (Statements.endpointDistance D (point x)) + L) :
    HasPositiveEnvelope (fun x => T.E0 (point x))
      (fun x => T.H (point x) / T.H (sample x)) ∧
    HasPositiveEnvelope (fun x => T.E0 (point x)) (fun x => T.E0 (sample x)) := by
  obtain ⟨BH, AH, BE, AE, hBH, _, hBE, _, hb⟩ :=
    material_oneSided_endpoint_comparison hT hD (R := 1) zero_le_one hL
  obtain ⟨CH, hCH, hpackH⟩ := coefficientEnvelope_pack BH AH
  obtain ⟨CE, hCE, hpackE⟩ := coefficientEnvelope_pack BE AE
  constructor
  · exact ⟨CH, CH, hCH, hCH, fun x =>
      ((hb (point x) (sample x) (hp x) (hs x) (hshift x)).1).trans
        (hpackH _ (hE x))⟩
  · refine ⟨CE, CE, hCE, hCE, fun x => ?_⟩
    have h := (hb (point x) (sample x) (hp x) (hs x) (hshift x)).2
    rw [Real.rpow_one] at h
    exact h.trans (hpackE _ (hE x))

/-- Sample and point costs are combined before eliminating the sample
base. The state factor is unchanged by this conversion. -/
theorem n04Realization_sample_point_envelope_to_point
    {X : Type*} {sample point state value : X → ℝ}
    (hsample : ∀ x, 1 ≤ sample x) (hpoint : ∀ x, 1 ≤ point x)
    (hstate : ∀ x, 1 ≤ state x)
    (hcost : HasPositiveEnvelope point sample)
    (hvalue : HasPositiveEnvelope (fun x => sample x * point x * state x) value) :
    HasPositiveEnvelope (fun x => point x * state x) value := by
  let Q : X → ℝ := fun x => point x * state x
  have hQ (x : X) : 1 ≤ Q x := by
    simpa only [one_mul] using
      mul_le_mul (hpoint x) (hstate x) zero_le_one (zero_le_one.trans (hpoint x))
  have hpQ (x : X) : point x ≤ Q x :=
    le_mul_of_one_le_right (zero_le_one.trans (hpoint x)) (hstate x)
  have hsampleQ : HasPositiveEnvelope Q sample :=
    hcost.base_mono (fun x => zero_le_one.trans (hpoint x)) hpQ
  have hself : HasPositiveEnvelope Q Q :=
    ⟨1, 1, zero_lt_one, zero_lt_one, fun x => by
      simpa only [Real.rpow_one, one_mul] using (le_refl (Q x))⟩
  have hbase : HasPositiveEnvelope Q (fun x => sample x * point x * state x) := by
    simpa only [Q, mul_assoc] using
      hsampleQ.mul hQ hself (fun x => zero_le_one.trans (hQ x))
  exact n04Realization_envelope_substitute
    (fun x => mul_nonneg
      (mul_nonneg (zero_le_one.trans (hsample x)) (zero_le_one.trans (hpoint x)))
      (zero_le_one.trans (hstate x))) hQ hbase hvalue

/-- The resulting state exponent is an ordinary natural number, as in
the frozen primitive material-jet clause. -/
theorem n04Realization_sample_point_polynomial_bound
    {X : Type*} {sample point state value : X → ℝ}
    (hsample : ∀ x, 1 ≤ sample x) (hpoint : ∀ x, 1 ≤ point x)
    (hstate : ∀ x, 1 ≤ state x)
    (hcost : HasPositiveEnvelope point sample)
    (hvalue : HasPositiveEnvelope (fun x => sample x * point x * state x) value) :
    ∃ d : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ x, value x ≤ C * point x ^ A * state x ^ d :=
  n04Realization_envelope_separate_state hpoint hstate
    (n04Realization_sample_point_envelope_to_point hsample hpoint hstate hcost hvalue)

end ContinuousFlexibility.Analysis
