module

public import ContinuousFlexibility.Analysis.N06NormalizerFirstNormal
public import ContinuousFlexibility.Analysis.N06NormalizerDirection

/-!
# A supported normalizer with the complete original N05 contract

The physical normalizer is constructed inside the existing normalization
region. Its change source is represented at every original weighted
level. The source-preserving graph shear then supplies the new inverse,
all three weighted exponents, every material and angular order, and the
first weak normal derivative. No normalizer-support hypothesis is added
to the old witness, and no normalization region is enlarged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}

/-- Every clause of N05 is retained by the explicitly transported domain. -/
theorem n06Normalizer_N05
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0)
    (hsource : ∀ m, (V.forget (3 / 4 : ℝ) 0 b v.val.2 m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode (S.psi - ψ)))
    (hlevels : ∀ γ t : ℝ, ∀ s : ℕ,
      VolumeMember S K V γ t s (V.forget (3 / 4 : ℝ) 0 b v.val.2)) :
    N05Properties D T (n06WithNormalizer S ψ) (n06NormalizerGeometry C ψ)
      (n06NormalizerCanonical K ψ) (n06NormalizerVolume V ψ) b
      (n06NormalizerDomain B ψ v hv) := by
  refine ⟨h05.1, n06Normalizer_isVolumeModel ψ h05.2.1,
    h05.2.2.1, h05.2.2.2.1, h05.2.2.2.2.1,
    n06NormalizerDomain_graph_closed h05 ψ v hv,
    n06NormalizerDomain_graph_iff h05 ψ v hv hsource,
    n06NormalizerDomain_right_inverse h05 ψ v hv,
    n06NormalizerDomain_left_inverse h05 ψ v hv,
    n06NormalizerDomain_globalInverse_eq h05 ψ v hv,
    n06NormalizerDomain_graph_bound h05 ψ v hv, ?_, ?_, ?_⟩
  · exact n06NormalizerDomain_three_weights h05 ψ v hv hlevels
  · exact n06NormalizerDomain_central_weights h05 ψ v hv hlevels
  · exact n06NormalizerDomain_first_normal h05 ψ v hv hlevels

/-- The primitive reference-coordinate data are copied without alteration. -/
theorem n06Normalizer_controlledReferenceCoordinates
    (ψ : (S.height (3 / 4 : ℝ)).Space)
    (h : N05ControlledReferenceCoordinates D S C K) :
    N05ControlledReferenceCoordinates D (n06WithNormalizer S ψ)
      (n06NormalizerGeometry C ψ) (n06NormalizerCanonical K ψ) := h

/- The cumulative arbitrary-normalizer transport is intentionally retired.
The shared primitive geometry constrains the actual chosen psi through its
auxiliary-column gauge and jets. Those facts are not preserved by an arbitrary
replacement. The original-K proof retains psi; the independent data and N05
graph transports in this module remain available. -/

end ContinuousFlexibility.Statements
