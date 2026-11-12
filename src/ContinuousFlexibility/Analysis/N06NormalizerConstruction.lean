import ContinuousFlexibility.Analysis.N06NormalizerFirstNormal
import ContinuousFlexibility.Analysis.N06NormalizerDirection

/-!
# A supported normalizer with the complete original N05 contract

The physical normalizer is constructed inside the existing normalization
region. Its change source is represented at every original weighted
level. The source-preserving graph shear then supplies the new inverse,
all three weighted exponents, every material and angular order, and the
first weak normal derivative. No normalizer-support hypothesis is added
to the old witness, and no normalization region is enlarged.
-/

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

/-- Reselecting the actual normalizer preserves the complete Through05
witness. The explicitly retained coordinate hypothesis is only used to
construct the compact change source in every original weighted level. -/
theorem n06_exists_supported_normalizer_through05
    {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hthrough : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ ψ : (S.height (3 / 4 : ℝ)).Space, S.Q ψ = 1 ∧
      ∃ v : B.Space, ∃ hv : n06NormalizerLambda S K v.val.1 = 0,
        IsPhysicalSpaces D T (n06WithNormalizer S ψ) ∧
        NonlinearPropertiesThrough05 D T (n06WithNormalizer S ψ)
          (n06NormalizerGeometry C ψ) (n06NormalizerReturns R ψ)
          (n06NormalizerCorrection L ψ) (n06NormalizerCanonical K ψ)
          (n06NormalizerVolume V ψ) b (n06NormalizerDomain B ψ v hv) base loss ε ∧
        ∃ g : ℝ → ℝ, ∃ J : Set ℝ,
          ContDiff ℝ ∞ g ∧ IsCompact J ∧ J ⊆ radialCore D ∧
          J ⊆ K.normalizationRegion ∧ (∀ r, r ∉ J → g r = 0) ∧
          (S.height (3 / 4 : ℝ)).decode ψ = fun p : PolarPoint => g p.1 := by
  have h01 : N01Properties D T S C base loss ε := hthrough.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := hthrough.1.2.2.2.2.1
  have h05 : N05Properties D T S C K V b B := hthrough.2
  obtain ⟨ψ, hunit, g, J, hg, hJ, hJD, hJK, hzero, hψ⟩ :=
    n06_exists_normalizer_in_normalizationRegion hT hS h01.1.2.2.2.1 h04
  have hcompact : HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode ψ) := by
    refine ⟨J, hJ, hJD, ?_⟩
    intro r hr θ
    exact (congrFun hψ (r, θ)).trans (hzero r hr)
  obtain ⟨d, hd, hzeroLambda, hlevels⟩ :=
    n06_exists_normalizer_change_source hT hS h01 h04 h05 hcoordinates ψ hcompact hunit
  let v : B.Space := B.inverse d
  have hv : n06NormalizerLambda S K v.val.1 = 0 :=
    (n06NormalizerLambda_apply v.val.1).trans hzeroLambda
  have hvs : v.val.2 = d := h05.2.2.2.2.2.2.2.1 d
  have hvsource : ∀ m, (V.forget (3 / 4 : ℝ) 0 b v.val.2 m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode (S.psi - ψ)) := by
    rw [hvs]
    exact hd
  have hvlevels : ∀ γ t : ℝ, ∀ s : ℕ,
      VolumeMember S K V γ t s (V.forget (3 / 4 : ℝ) 0 b v.val.2) := by
    rw [hvs]
    exact hlevels
  refine ⟨ψ, hunit, v, hv, n06WithNormalizer_isPhysical hT hS ψ hcompact hunit,
    ⟨n06Normalizer_through04 ψ hthrough.1,
      n06Normalizer_N05 h05 ψ v hv hvsource hvlevels⟩,
    g, J, hg, hJ, hJD, hJK, hzero, hψ⟩

end ContinuousFlexibility.Statements
