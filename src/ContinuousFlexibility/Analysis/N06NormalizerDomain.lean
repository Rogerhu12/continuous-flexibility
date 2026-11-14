module

public import ContinuousFlexibility.Analysis.N06NormalizerRelation
public import ContinuousFlexibility.Analysis.N06NormalizerGraphTransport

/-!
# The transported canonical domain and its original source projection

The new domain uses the explicit graph shear already identified with the
new physical relation. Its inverse is the old inverse followed by the
source-preserving graph equivalence. Material exponents are copied
unchanged. The all-level estimates are transported separately.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ}

def n06NormalizerDomain (B : CanonicalDomainData S K V b)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0) :
    CanonicalDomainData (n06WithNormalizer S ψ) (n06NormalizerCanonical K ψ)
      (n06NormalizerVolume V ψ) b where
  weakExponent := B.weakExponent
  sourceMaterial := B.sourceMaterial
  outputMaterial := B.outputMaterial
  lossMaterial := B.lossMaterial
  graph := n06NormalizerGraph B.graph (n06NormalizerLambda S K) v.val.2
  inverse := (n06NormalizerGraphEquiv B.graph (n06NormalizerLambda S K) v hv).toContinuousLinearMap.comp
    B.inverse
  globalInverse := fun F => n06NormalizerUnknownShear (n06NormalizerLambda S K) v.val.1
    (B.globalInverse F)

theorem n06NormalizerDomain_inverse_val (B : CanonicalDomainData S K V b)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    ((n06NormalizerDomain B ψ v hv).inverse F).val =
      ((B.inverse F).val.1 + (B.inverse F).val.1.2.2.2 • v.val.1, (B.inverse F).val.2) := by
  apply Prod.ext
  · have h := n06NormalizerGraphEquiv_unknown
      B.graph (n06NormalizerLambda S K) v hv (B.inverse F)
    have hs := n06NormalizerUnknownShear_apply
      (n06NormalizerLambda S K) v.val.1 (B.inverse F).val.1
    have hLambda := n06NormalizerLambda_apply (B.inverse F).val.1
    exact h.trans (hs.trans
      (congrArg (fun c : ℝ => (B.inverse F).val.1 + c • v.val.1) hLambda))
  · exact n06NormalizerGraphEquiv_source
      B.graph (n06NormalizerLambda S K) v hv (B.inverse F)

theorem n06NormalizerDomain_graph_closed
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0) :
    IsClosed ((n06NormalizerDomain B ψ v hv).graph :
      Set (CanonicalUnknown (n06WithNormalizer S ψ) (n06NormalizerCanonical K ψ) ×
        (n06NormalizerVolume V ψ).level (3 / 4 : ℝ) 0 b)) :=
  n06NormalizerGraph_closed B.graph (n06NormalizerLambda S K) v.val.2 h05.2.2.2.2.2.1

theorem n06NormalizerDomain_graph_iff
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0)
    (hd : ∀ m, (V.forget (3 / 4 : ℝ) 0 b v.val.2 m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode (S.psi - ψ)))
    (x : CanonicalUnknown S K × V.level (3 / 4 : ℝ) 0 b) :
    x ∈ (n06NormalizerDomain B ψ v hv).graph ↔
      ReferenceCanonicalRelation D T (n06WithNormalizer S ψ)
        (n06NormalizerGeometry C ψ) (n06NormalizerCanonical K ψ) (n06NormalizerVolume V ψ)
        B.weakExponent B.sourceMaterial B.outputMaterial B.lossMaterial x.1
        ((n06NormalizerVolume V ψ).forget (3 / 4 : ℝ) 0 b x.2) :=
  n06_normalizer_graph_iff_referenceRelation h05 ψ v.val.2 hd x

theorem n06NormalizerDomain_right_inverse
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0) (F : V.level (3 / 4 : ℝ) 0 b) :
    ((n06NormalizerDomain B ψ v hv).inverse F).val.2 = F := by
  exact n06_graph_equiv_inverse_right
    (n06NormalizerGraphEquiv B.graph (n06NormalizerLambda S K) v hv)
    (n06NormalizerGraphEquiv_source B.graph (n06NormalizerLambda S K) v hv)
    B.inverse h05.2.2.2.2.2.2.2.1 F

theorem n06NormalizerDomain_left_inverse
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0)
    (u : (n06NormalizerDomain B ψ v hv).Space) :
    (n06NormalizerDomain B ψ v hv).inverse u.val.2 = u := by
  exact n06_graph_equiv_inverse_left
    (n06NormalizerGraphEquiv B.graph (n06NormalizerLambda S K) v hv)
    (n06NormalizerGraphEquiv_source B.graph (n06NormalizerLambda S K) v hv)
    B.inverse h05.2.2.2.2.2.2.2.2.1 u

theorem n06NormalizerDomain_globalInverse_eq
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0) (F : V.level (3 / 4 : ℝ) 0 b) :
    ((n06NormalizerDomain B ψ v hv).inverse F).val.1 =
      (n06NormalizerDomain B ψ v hv).globalInverse
        ((n06NormalizerVolume V ψ).forget (3 / 4 : ℝ) 0 b F) := by
  exact n06_graph_equiv_global_inverse
    (n06NormalizerGraphEquiv B.graph (n06NormalizerLambda S K) v hv)
    (n06NormalizerUnknownShear (n06NormalizerLambda S K) v.val.1)
    (n06NormalizerGraphEquiv_unknown B.graph (n06NormalizerLambda S K) v hv)
    B.inverse (V.forget (3 / 4 : ℝ) 0 b) B.globalInverse h05.2.2.2.2.2.2.2.2.2.1 F

theorem n06NormalizerDomain_graph_bound
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ u : (n06NormalizerDomain B ψ v hv).Space,
      ‖u‖ ≤ C₀ * ‖u.val.2‖ := by
  exact n06_graph_equiv_source_bound
    (n06NormalizerGraphEquiv B.graph (n06NormalizerLambda S K) v hv)
    (n06NormalizerGraphEquiv_source B.graph (n06NormalizerLambda S K) v hv)
    h05.2.2.2.2.2.2.2.2.2.2.1

end ContinuousFlexibility.Statements
