import ContinuousFlexibility.Analysis.AngularHilbertCommutator

/-!
# Real principal coefficients in the angular inverse estimate

The principal tame coefficients may be real numbers. Replacing them by
their nonnegative parts only enlarges the assumed bound, since every
Sobolev norm is nonnegative. The two scalar-field statements below share
this conversion and retain the same explicit inverse estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped NNReal

section Coefficients

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
  [HasAngularSpectralDecomposition 𝕜 H]

/-- Taking the nonnegative part of a principal coefficient preserves a
bundled angular-domain and tame-bound hypothesis. -/
theorem angular_sobolev_bound_toNNReal (A : AngularResolventData 𝕜 H)
    (K : H →L[𝕜] H) (a : ℕ → ℝ) (c : ℕ → ℝ≥0)
    (hbound : ∀ p v, A.Sobolev p v →
      A.Sobolev p (K v) ∧ A.sobolevNorm p (K v) ≤
        a p * A.sobolevNorm p v + (c p : ℝ) * ‖v‖) :
    ∀ p v, A.Sobolev p v →
      A.Sobolev p (K v) ∧ A.sobolevNorm p (K v) ≤
        (Real.toNNReal (a p) : ℝ) * A.sobolevNorm p v + (c p : ℝ) * ‖v‖ := by
  intro p v hv
  obtain ⟨hKv, hnorm⟩ := hbound p v hv
  refine ⟨hKv, hnorm.trans ?_⟩
  exact add_le_add
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal (a p))
      (angularSobolevNorm_nonneg (𝕜 := 𝕜) p (A.coordinates v))) le_rfl

end Coefficients

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The complex angular inverse theorem with arbitrary real principal
coefficients. Its constant depends on the nonnegative part of the
preceding principal coefficient, the zeroth error, and the inverse norm. -/
theorem angular_inverse_commutator_complex_real_coefficients
    (A : AngularResolventData ℂ H) (R K B : H →L[ℂ] H)
    (a : ℕ → ℝ) (c : ℕ → ℝ≥0) (ha : Monotone a) (hc : Monotone c)
    (hR : ∀ p v, A.Sobolev p v → A.Sobolev p (R v))
    (hbound : ∀ p v, A.Sobolev p v →
      A.Sobolev p (K v) ∧ A.sobolevNorm p (K v) ≤
        a p * A.sobolevNorm p v + (c p : ℝ) * ‖v‖)
    (hcomm : ∀ v, A.Sobolev 1 v →
      A.derivative (R v) = R (A.derivative v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f) :
    (∀ p f, A.Sobolev p f → A.Sobolev p (B f)) ∧
    (∀ p, 1 ≤ p → ∀ f, A.Sobolev p f →
      A.sobolevNorm p (B f) ≤
        angularInverseTameConstant p (Real.toNNReal (a (p - 1))) (c 0) ‖B‖ *
          (A.sobolevNorm p f + (1 + (c (p - 1) : ℝ)) * ‖f‖)) :=
  angular_inverse_commutator_complex A R K B (fun n => Real.toNNReal (a n)) c
    (Real.toNNReal_monotone.comp ha) hc hR
    (angular_sobolev_bound_toNNReal A K a c hbound) hcomm hleft hright

end Complex

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The real angular inverse theorem with arbitrary real principal
coefficients and the same constant as the complex theorem. -/
theorem angular_inverse_commutator_real_real_coefficients
    (A : AngularResolventData ℝ H) (R K B : H →L[ℝ] H)
    (a : ℕ → ℝ) (c : ℕ → ℝ≥0) (ha : Monotone a) (hc : Monotone c)
    (hR : ∀ p v, A.Sobolev p v → A.Sobolev p (R v))
    (hbound : ∀ p v, A.Sobolev p v →
      A.Sobolev p (K v) ∧ A.sobolevNorm p (K v) ≤
        a p * A.sobolevNorm p v + (c p : ℝ) * ‖v‖)
    (hcomm : ∀ v, A.Sobolev 1 v →
      A.derivative (R v) = R (A.derivative v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f) :
    (∀ p f, A.Sobolev p f → A.Sobolev p (B f)) ∧
    (∀ p, 1 ≤ p → ∀ f, A.Sobolev p f →
      A.sobolevNorm p (B f) ≤
        angularInverseTameConstant p (Real.toNNReal (a (p - 1))) (c 0) ‖B‖ *
          (A.sobolevNorm p f + (1 + (c (p - 1) : ℝ)) * ‖f‖)) :=
  angular_inverse_commutator_real A R K B (fun n => Real.toNNReal (a n)) c
    (Real.toNNReal_monotone.comp ha) hc hR
    (angular_sobolev_bound_toNNReal A K a c hbound) hcomm hleft hright

end Real

end ContinuousFlexibility.Analysis
