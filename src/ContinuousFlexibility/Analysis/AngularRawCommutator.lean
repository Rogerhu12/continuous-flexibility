import ContinuousFlexibility.Analysis.AngularRawSpectrum
import ContinuousFlexibility.Analysis.AngularRealCoefficients
import ContinuousFlexibility.Analysis.AngularFrequencyPositivity

/-!
# The commutator inverse lemma for a given unbounded operator

The operator in the public hypotheses is an arbitrary self-adjoint
`LinearPMap`, and its spectrum is defined by actual bounded inverses on
its domain.  The integer spectrum constructs the bounded resolvent and
the full spectral coordinates.  The commutator hypothesis uses the
original operator's domain and action.  No shifted inverse, spectral
decomposition, positivity, or inverse regularity is an extra premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped NNReal

section Common

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
  [HasAngularSpectralDecomposition 𝕜 H]

/-- The Sobolev domain obtained from the proved spectral decomposition
of the given raw self-adjoint angular operator. -/
def angularRawSobolev (L : H →ₗ.[𝕜] H) (hL : IsSelfAdjoint L)
    (hSpectrum : angularRawSpectrum L ⊆ range (fun n : ℕ => (n : ℝ)))
    (p : ℕ) (v : H) : Prop :=
  (angularResolventDataOfRaw L hL hSpectrum).Sobolev p v

/-- The exact Japanese-bracket Sobolev norm of the given raw operator. -/
def angularRawSobolevNorm (L : H →ₗ.[𝕜] H) (hL : IsSelfAdjoint L)
    (hSpectrum : angularRawSpectrum L ⊆ range (fun n : ℕ => (n : ℝ)))
    (p : ℕ) (v : H) : ℝ :=
  (angularResolventDataOfRaw L hL hSpectrum).sobolevNorm p v

/-- The first Sobolev space is the original operator domain. -/
theorem angularRaw_domain_iff_sobolev_one (L : H →ₗ.[𝕜] H) (hL : IsSelfAdjoint L)
    (hSpectrum : angularRawSpectrum L ⊆ range (fun n : ℕ => (n : ℝ))) (v : H) :
    v ∈ L.domain ↔ angularRawSobolev L hL hSpectrum 1 v := by
  let D := angularResolventDataOfRaw L hL hSpectrum
  have hdom : D.frequency.domain = L.domain :=
    congrArg LinearPMap.domain (angularResolventDataOfRaw_frequency_eq L hL hSpectrum)
  rw [← hdom]
  exact D.frequency_domain_iff_sobolev_one v

/-- The spectral derivative is the action of the original raw operator. -/
theorem angularRaw_derivative_eq (L : H →ₗ.[𝕜] H) (hL : IsSelfAdjoint L)
    (hSpectrum : angularRawSpectrum L ⊆ range (fun n : ℕ => (n : ℝ))) (v : L.domain) :
    (angularResolventDataOfRaw L hL hSpectrum).derivative (v : H) = L v := by
  let D := angularResolventDataOfRaw L hL hSpectrum
  have hv : D.Sobolev 1 (v : H) :=
    (angularRaw_domain_iff_sobolev_one L hL hSpectrum v).mp v.property
  have hleft := D.operator_add_derivative hv
  have hright : D.operator ((v : H) + L v) = v :=
    (angularRawShiftedResolvent L hSpectrum).right_shifted v
  exact add_left_cancel (D.injective (hleft.trans hright.symm))

/-- Nonnegativity follows from the integer spectral hypothesis and the
proved spectral decomposition; it is not an added raw-operator premise. -/
theorem angularRaw_nonneg (L : H →ₗ.[𝕜] H) (hL : IsSelfAdjoint L)
    (hSpectrum : angularRawSpectrum L ⊆ range (fun n : ℕ => (n : ℝ))) (v : L.domain) :
    0 ≤ RCLike.re (inner 𝕜 (v : H) (L v)) := by
  let D := angularResolventDataOfRaw L hL hSpectrum
  have hv : D.Sobolev 1 (v : H) :=
    (angularRaw_domain_iff_sobolev_one L hL hSpectrum v).mp v.property
  have hdom : (v : H) ∈ D.frequency.domain :=
    (D.frequency_domain_iff_sobolev_one v).mpr hv
  have h := D.frequency_nonneg ⟨v, hdom⟩
  rw [← D.derivative_eq_frequency ⟨v, hdom⟩] at h
  change 0 ≤ RCLike.re (inner 𝕜 (v : H)
    ((angularResolventDataOfRaw L hL hSpectrum).derivative (v : H))) at h
  rwa [angularRaw_derivative_eq L hL hSpectrum v] at h

/-- Transfer a commutator identity stated on the original domain to the
derived spectral scale.  Domain membership of the output is part of the
meaning of applying the original unbounded operator. -/
theorem angularRaw_commutator_to_coordinates (L : H →ₗ.[𝕜] H) (hL : IsSelfAdjoint L)
    (hSpectrum : angularRawSpectrum L ⊆ range (fun n : ℕ => (n : ℝ)))
    (R K : H →L[𝕜] H)
    (hcomm : ∀ v : L.domain, ∃ hRv : R (v : H) ∈ L.domain,
      L ⟨R (v : H), hRv⟩ = R (L v) + K (v : H)) :
    ∀ v, angularRawSobolev L hL hSpectrum 1 v →
      (angularResolventDataOfRaw L hL hSpectrum).derivative (R v) =
        R ((angularResolventDataOfRaw L hL hSpectrum).derivative v) + K v := by
  intro v hv
  have hvL : v ∈ L.domain := (angularRaw_domain_iff_sobolev_one L hL hSpectrum v).mpr hv
  obtain ⟨hRv, heq⟩ := hcomm ⟨v, hvL⟩
  rw [angularRaw_derivative_eq L hL hSpectrum ⟨R v, hRv⟩,
    angularRaw_derivative_eq L hL hSpectrum ⟨v, hvL⟩]
  exact heq

end Common

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 8.4 for an arbitrary given complex self-adjoint unbounded
operator with integer spectrum.  The principal coefficients may be real
of either sign; their positive parts enter the explicit tame constant. -/
theorem angular_inverse_commutator_raw_complex (L : H →ₗ.[ℂ] H) (hL : IsSelfAdjoint L)
    (hSpectrum : angularRawSpectrum L ⊆ range (fun n : ℕ => (n : ℝ)))
    (R K B : H →L[ℂ] H) (a : ℕ → ℝ) (c : ℕ → ℝ≥0)
    (ha : Monotone a) (hc : Monotone c)
    (hR : ∀ p v, angularRawSobolev L hL hSpectrum p v →
      angularRawSobolev L hL hSpectrum p (R v))
    (hbound : ∀ p v, angularRawSobolev L hL hSpectrum p v →
      angularRawSobolev L hL hSpectrum p (K v) ∧
      angularRawSobolevNorm L hL hSpectrum p (K v) ≤
        a p * angularRawSobolevNorm L hL hSpectrum p v + (c p : ℝ) * ‖v‖)
    (hcomm : ∀ v : L.domain, ∃ hRv : R (v : H) ∈ L.domain,
      L ⟨R (v : H), hRv⟩ = R (L v) + K (v : H))
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f) :
    (∀ p f, angularRawSobolev L hL hSpectrum p f →
      angularRawSobolev L hL hSpectrum p (B f)) ∧
    (∀ p, 1 ≤ p → ∀ f, angularRawSobolev L hL hSpectrum p f →
      angularRawSobolevNorm L hL hSpectrum p (B f) ≤
        angularInverseTameConstant p (Real.toNNReal (a (p - 1))) (c 0) ‖B‖ *
          (angularRawSobolevNorm L hL hSpectrum p f +
            (1 + (c (p - 1) : ℝ)) * ‖f‖)) :=
  angular_inverse_commutator_complex_real_coefficients
    (angularResolventDataOfRaw L hL hSpectrum) R K B a c ha hc hR hbound
    (angularRaw_commutator_to_coordinates L hL hSpectrum R K hcomm) hleft hright

end Complex

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The same raw-operator commutator inverse theorem for arbitrary real
Hilbert spaces, with exactly the same explicit tame constant. -/
theorem angular_inverse_commutator_raw_real (L : H →ₗ.[ℝ] H) (hL : IsSelfAdjoint L)
    (hSpectrum : angularRawSpectrum L ⊆ range (fun n : ℕ => (n : ℝ)))
    (R K B : H →L[ℝ] H) (a : ℕ → ℝ) (c : ℕ → ℝ≥0)
    (ha : Monotone a) (hc : Monotone c)
    (hR : ∀ p v, angularRawSobolev L hL hSpectrum p v →
      angularRawSobolev L hL hSpectrum p (R v))
    (hbound : ∀ p v, angularRawSobolev L hL hSpectrum p v →
      angularRawSobolev L hL hSpectrum p (K v) ∧
      angularRawSobolevNorm L hL hSpectrum p (K v) ≤
        a p * angularRawSobolevNorm L hL hSpectrum p v + (c p : ℝ) * ‖v‖)
    (hcomm : ∀ v : L.domain, ∃ hRv : R (v : H) ∈ L.domain,
      L ⟨R (v : H), hRv⟩ = R (L v) + K (v : H))
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f) :
    (∀ p f, angularRawSobolev L hL hSpectrum p f →
      angularRawSobolev L hL hSpectrum p (B f)) ∧
    (∀ p, 1 ≤ p → ∀ f, angularRawSobolev L hL hSpectrum p f →
      angularRawSobolevNorm L hL hSpectrum p (B f) ≤
        angularInverseTameConstant p (Real.toNNReal (a (p - 1))) (c 0) ‖B‖ *
          (angularRawSobolevNorm L hL hSpectrum p f +
            (1 + (c (p - 1) : ℝ)) * ‖f‖)) :=
  angular_inverse_commutator_real_real_coefficients
    (angularResolventDataOfRaw L hL hSpectrum) R K B a c ha hc hR hbound
    (angularRaw_commutator_to_coordinates L hL hSpectrum R K hcomm) hleft hright

end Real

/--
info: 'ContinuousFlexibility.Analysis.angular_inverse_commutator_raw_complex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms angular_inverse_commutator_raw_complex

/--
info: 'ContinuousFlexibility.Analysis.angular_inverse_commutator_raw_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms angular_inverse_commutator_raw_real

end ContinuousFlexibility.Analysis
