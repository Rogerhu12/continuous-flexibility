import ContinuousFlexibility.Radial.ReferenceRowAlgebra
import ContinuousFlexibility.Radial.ReferenceHomogeneousUniqueness

/-!
# Linearity and uniqueness of the actual reference weak graph

All additive integral identities are justified by the actual local L²
test pairings and the integrable border row. At positive attenuation,
the graph is a linear relation, and the proved homogeneous kernel
criterion supplies uniqueness for every source.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

theorem ReferenceGraph.smul {D : ReferenceData}
    {γ M₀ M₁ : ℝ} {U : RadialUnknown} {F : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F) (c : ℝ) :
    ReferenceGraph D γ M₀ M₁ (c • U) (c • F) := by
  refine ⟨hG.1.smul c, hG.2.1.smul c, ?_, ?_⟩
  · change referenceRow D (fun x => c * U.1 x) = c * F.2
    rw [referenceRow_const_mul, hG.2.2.1]
  · intro ψ hψ
    change radialWeakPairing D (fun x => c * U.1 x) ψ +
      (c * U.2) * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceColumn D r * Radial.cosineMode 2 θ * ψ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => (c * F.1 (r, θ)) * ψ (r, θ))
    simp only [radialWeakPairing_const_mul, mul_assoc, radialAngularMean_const_mul,
      intervalIntegral.integral_const_mul]
    have he := congrArg (fun z : ℝ => c * z) (hG.2.2.2 ψ hψ)
    simp only [mul_assoc, radialAngularMean_const_mul] at he
    nlinarith only [he]

theorem ReferenceGraph.add {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    {U V : RadialUnknown} {F K : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F)
    (hH : ReferenceGraph D γ M₀ M₁ V K) :
    ReferenceGraph D γ M₀ M₁ (U + V) (F + K) := by
  have hab := (Radial.matchingProfileGeometry hD).2.1.le
  refine ⟨hG.1.add hab hH.1, hG.2.1.add hab hD.choose_spec.2.1 hH.2.1, ?_, ?_⟩
  · change referenceRow D (fun x => U.1 x + V.1 x) = F.2 + K.2
    rw [referenceRow_add hD hB hγ hG.1 hH.1, hG.2.2.1, hH.2.2.1]
  · intro ψ hψ
    have hsource :
        (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          (F.1 (r, θ) + K.1 (r, θ)) * ψ (r, θ))) =
        (∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ) * ψ (r, θ))) +
        ∫ r in D.a..D.b, radialAngularMean (fun θ => K.1 (r, θ) * ψ (r, θ)) := by
      simpa only [add_mul] using integral_angularMean_add hab
        (hG.2.1.1.integrable_mul_test hD hψ) (hH.2.1.1.integrable_mul_test hD hψ)
    change radialWeakPairing D (fun x => U.1 x + V.1 x) ψ +
      (U.2 + V.2) * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceColumn D r * Radial.cosineMode 2 θ * ψ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (F.1 (r, θ) + K.1 (r, θ)) * ψ (r, θ))
    rw [radialWeakPairing_add hD (hG.1.radialCellIntegrable hD hB)
      (hH.1.radialCellIntegrable hD hB) hψ, hsource]
    have hu := hG.2.2.2 ψ hψ
    have hv := hH.2.2.2 ψ hψ
    nlinarith only [hu, hv]

theorem ReferenceGraph.sub {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    {U V : RadialUnknown} {F K : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F)
    (hH : ReferenceGraph D γ M₀ M₁ V K) :
    ReferenceGraph D γ M₀ M₁ (U - V) (F - K) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    hG.add hD hB hγ (hH.smul (-1))

theorem RadialRepresentativeEq.of_sub_eq_zero {D : ReferenceData}
    {U V : RadialUnknown} (h : RadialRepresentativeEq D (U - V) 0) :
    RadialRepresentativeEq D U V := by
  refine ⟨?_, ?_⟩
  · have hs := h.1
    change U.2 - V.2 = 0 at hs
    exact sub_eq_zero.mp hs
  · filter_upwards [h.2] with x hx
    change U.1 x - V.1 x = 0 at hx
    exact sub_eq_zero.mp hx

/-- Uniqueness is on the full frozen weak domain, not merely on an
operator's constructed range. The source threshold is independent of M₁. -/
theorem exists_referenceGraph_unique {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hmode : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ G : RadialModePair D →L[ℝ] RadialModePair D,
        ModeInverseProperties D j G) :
    ∃ Mmin : ℝ, 0 < Mmin ∧
      ∀ γ : ℝ, 0 < γ → ∀ M₀ : ℝ, Mmin ≤ M₀ → ∀ M₁ : ℝ,
      ∀ U V : RadialUnknown, ∀ F : RadialSource,
        ReferenceGraph D γ M₀ M₁ U F → ReferenceGraph D γ M₀ M₁ V F →
          RadialRepresentativeEq D U V := by
  obtain ⟨Mmin, hMmin, hkernel⟩ := exists_referenceGraph_homogeneous_unique hD hB hmode
  refine ⟨Mmin, hMmin, ?_⟩
  intro γ hγ M₀ hM₀ M₁ U V F hU hV
  have hsub : ReferenceGraph D γ M₀ M₁ (U - V) 0 := by
    simpa only [sub_self] using hU.sub hD hB hγ hV
  exact (hkernel γ hγ M₀ hM₀ M₁ (U - V) hsub).of_sub_eq_zero

end ContinuousFlexibility.Statements
