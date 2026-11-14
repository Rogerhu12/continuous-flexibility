module

public import ContinuousFlexibility.Analysis.AngularResolventDomains
public import ContinuousFlexibility.Analysis.AngularInverseEstimate
public import ContinuousFlexibility.Analysis.AngularRealInverseEstimate

/-!
# Regularity of an inverse from an angular commutator

These are the Hilbert-space statements of the manuscript's angular
commutator lemma.  Their spectral coordinates are constructed from the
given self-adjoint resolvent.  The common transport proof below serves
both scalar fields; the public theorems use the proved real and complex
coordinate estimates and have no decomposition or interpolation premise.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped NNReal

section Transport

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
  [HasAngularSpectralDecomposition 𝕜 H]

/-- Transport the proved coordinate estimate through the canonical
spectral isometry.  The estimate argument is supplied by a theorem in
each of the two public scalar-field specializations below. -/
private theorem angular_inverse_commutator_transport (A : AngularResolventData 𝕜 H)
    (R K B : H →L[𝕜] H) (a c : ℕ → ℝ≥0)
    (hR : ∀ p v, A.Sobolev p v → A.Sobolev p (R v))
    (hbound : ∀ p v, A.Sobolev p v →
      A.Sobolev p (K v) ∧ A.sobolevNorm p (K v) ≤
        (a p : ℝ) * A.sobolevNorm p v + (c p : ℝ) * ‖v‖)
    (hcomm : ∀ v, A.Sobolev 1 v →
      A.derivative (R v) = R (A.derivative v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f)
    (hcoordinate :
      (∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
        MemAngularSobolev (𝕜 := 𝕜) p (angularConjugate A.coordinates R v)) →
      (∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
        MemAngularSobolev (𝕜 := 𝕜) p (angularConjugate A.coordinates K v)) →
      (∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
        angularSobolevNorm (𝕜 := 𝕜) p (angularConjugate A.coordinates K v) ≤
          (a p : ℝ) * angularSobolevNorm (𝕜 := 𝕜) p v + (c p : ℝ) * ‖v‖) →
      (∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
        angularDerivative (𝕜 := 𝕜) (angularConjugate A.coordinates R v) =
          angularConjugate A.coordinates R (angularDerivative (𝕜 := 𝕜) v) +
            angularConjugate A.coordinates K v) →
      (∀ v, angularConjugate A.coordinates B (v + angularConjugate A.coordinates R v) = v) →
      (∀ f, angularConjugate A.coordinates B f +
        angularConjugate A.coordinates R (angularConjugate A.coordinates B f) = f) →
      (∀ p f, MemAngularSobolev (𝕜 := 𝕜) p f →
        MemAngularSobolev (𝕜 := 𝕜) p (angularConjugate A.coordinates B f)) ∧
      (∀ p, 1 ≤ p → ∀ f, MemAngularSobolev (𝕜 := 𝕜) p f →
        angularSobolevNorm (𝕜 := 𝕜) p (angularConjugate A.coordinates B f) ≤
          angularInverseTameConstant p (a (p - 1)) (c 0) ‖angularConjugate A.coordinates B‖ *
            (angularSobolevNorm (𝕜 := 𝕜) p f + (1 + (c (p - 1) : ℝ)) * ‖f‖))) :
    (∀ p f, A.Sobolev p f → A.Sobolev p (B f)) ∧
    (∀ p, 1 ≤ p → ∀ f, A.Sobolev p f →
      A.sobolevNorm p (B f) ≤
        angularInverseTameConstant p (a (p - 1)) (c 0) ‖B‖ *
          (A.sobolevNorm p f + (1 + (c (p - 1) : ℝ)) * ‖f‖)) := by
  have hback (p : ℕ) (v : lp (fun n => angularResolventEigenspace A.operator n) 2)
      (hv : MemAngularSobolev (𝕜 := 𝕜) p v) : A.Sobolev p (A.coordinates.symm v) := by
    simpa only [AngularResolventData.Sobolev, LinearIsometryEquiv.apply_symm_apply] using hv
  have hRC : ∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
      MemAngularSobolev (𝕜 := 𝕜) p (angularConjugate A.coordinates R v) := by
    intro p v hv
    simpa only [AngularResolventData.Sobolev, angularConjugate_apply] using
      hR p (A.coordinates.symm v) (hback p v hv)
  have hKC : ∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
      MemAngularSobolev (𝕜 := 𝕜) p (angularConjugate A.coordinates K v) := by
    intro p v hv
    simpa only [AngularResolventData.Sobolev, angularConjugate_apply] using
      (hbound p (A.coordinates.symm v) (hback p v hv)).1
  have hboundC : ∀ p v, MemAngularSobolev (𝕜 := 𝕜) p v →
      angularSobolevNorm (𝕜 := 𝕜) p (angularConjugate A.coordinates K v) ≤
        (a p : ℝ) * angularSobolevNorm (𝕜 := 𝕜) p v + (c p : ℝ) * ‖v‖ := by
    intro p v hv
    simpa only [AngularResolventData.sobolevNorm, angularConjugate_apply,
      LinearIsometryEquiv.apply_symm_apply, A.coordinates.symm.norm_map] using
      (hbound p (A.coordinates.symm v) (hback p v hv)).2
  have hcommC : ∀ v, v ∈ angularFrequencyDomain (𝕜 := 𝕜) →
      angularDerivative (𝕜 := 𝕜) (angularConjugate A.coordinates R v) =
        angularConjugate A.coordinates R (angularDerivative (𝕜 := 𝕜) v) +
          angularConjugate A.coordinates K v := by
    intro v hv
    have hmem := hback 1 v ((memAngularSobolev_one_iff_frequency (𝕜 := 𝕜) v).mpr hv)
    simpa only [map_add, AngularResolventData.coordinates_derivative,
      AngularResolventData.derivative, LinearIsometryEquiv.apply_symm_apply,
      angularConjugate_apply] using
      congrArg A.coordinates (hcomm (A.coordinates.symm v) hmem)
  have hleftC : ∀ v,
      angularConjugate A.coordinates B (v + angularConjugate A.coordinates R v) = v := by
    intro v
    simpa only [angularConjugate_apply, map_add, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply] using
      congrArg A.coordinates (hleft (A.coordinates.symm v))
  have hrightC : ∀ f, angularConjugate A.coordinates B f +
      angularConjugate A.coordinates R (angularConjugate A.coordinates B f) = f := by
    intro f
    simpa only [angularConjugate_apply, map_add, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply] using
      congrArg A.coordinates (hright (A.coordinates.symm f))
  obtain ⟨hreg, hestimate⟩ := hcoordinate hRC hKC hboundC hcommC hleftC hrightC
  constructor
  · intro p f hf
    simpa only [AngularResolventData.Sobolev, angularConjugate_apply_coordinates] using
      hreg p (A.coordinates f) hf
  · intro p hp f hf
    simpa only [AngularResolventData.sobolevNorm, angularConjugate_apply_coordinates,
      norm_angularConjugate, A.coordinates.norm_map] using
      hestimate p hp (A.coordinates f) hf

end Transport

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Regularity and tame bounds for a bounded inverse on a complex
Hilbert space with integer angular spectrum.  The constant depends only
on the order, the principal coefficient at the preceding order, the
zeroth error coefficient, and the base inverse norm. -/
theorem angular_inverse_commutator_complex (A : AngularResolventData ℂ H)
    (R K B : H →L[ℂ] H) (a c : ℕ → ℝ≥0) (ha : Monotone a) (hc : Monotone c)
    (hR : ∀ p v, A.Sobolev p v → A.Sobolev p (R v))
    (hbound : ∀ p v, A.Sobolev p v →
      A.Sobolev p (K v) ∧ A.sobolevNorm p (K v) ≤
        (a p : ℝ) * A.sobolevNorm p v + (c p : ℝ) * ‖v‖)
    (hcomm : ∀ v, A.Sobolev 1 v →
      A.derivative (R v) = R (A.derivative v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f) :
    (∀ p f, A.Sobolev p f → A.Sobolev p (B f)) ∧
    (∀ p, 1 ≤ p → ∀ f, A.Sobolev p f →
      A.sobolevNorm p (B f) ≤
        angularInverseTameConstant p (a (p - 1)) (c 0) ‖B‖ *
          (A.sobolevNorm p f + (1 + (c (p - 1) : ℝ)) * ‖f‖)) :=
  angular_inverse_commutator_transport A R K B a c hR hbound hcomm hleft hright
    (angular_inverse_tame_complex _ _ _ a c ha hc)

end Complex

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The same angular inverse regularity theorem for real Hilbert spaces,
with exactly the same tame constant. -/
theorem angular_inverse_commutator_real (A : AngularResolventData ℝ H)
    (R K B : H →L[ℝ] H) (a c : ℕ → ℝ≥0) (ha : Monotone a) (hc : Monotone c)
    (hR : ∀ p v, A.Sobolev p v → A.Sobolev p (R v))
    (hbound : ∀ p v, A.Sobolev p v →
      A.Sobolev p (K v) ∧ A.sobolevNorm p (K v) ≤
        (a p : ℝ) * A.sobolevNorm p v + (c p : ℝ) * ‖v‖)
    (hcomm : ∀ v, A.Sobolev 1 v →
      A.derivative (R v) = R (A.derivative v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f) :
    (∀ p f, A.Sobolev p f → A.Sobolev p (B f)) ∧
    (∀ p, 1 ≤ p → ∀ f, A.Sobolev p f →
      A.sobolevNorm p (B f) ≤
        angularInverseTameConstant p (a (p - 1)) (c 0) ‖B‖ *
          (A.sobolevNorm p f + (1 + (c (p - 1) : ℝ)) * ‖f‖)) :=
  angular_inverse_commutator_transport A R K B a c hR hbound hcomm hleft hright
    (angular_inverse_tame_real _ _ _ a c ha hc)

end Real

/--
info: 'ContinuousFlexibility.Analysis.angular_inverse_commutator_complex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms angular_inverse_commutator_complex

/--
info: 'ContinuousFlexibility.Analysis.angular_inverse_commutator_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms angular_inverse_commutator_real

end ContinuousFlexibility.Analysis
