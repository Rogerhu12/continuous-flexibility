import ContinuousFlexibility.Analysis.N07aAngularReferenceJetEnvelopes
import ContinuousFlexibility.Analysis.N07aAngularFixedVolume
import ContinuousFlexibility.Analysis.N07aCanonicalSourceRegularity

/-!
# The actual canonical height of every physical candidate

Every decoded physical height has all material and angular source-graph
levels after the actual current coordinate change. The proof uses its
genuine spatial jets and the original period and reflection identities.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

theorem n07a_candidateCanonicalHeight_contDiffOn
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (m : ℕ) :
    ContDiffOn ℝ ∞ (canonicalHeight S K z m f) (canonicalOpen S K m) := by
  have hgeom := h04.1.charts z hz hs m
  have hmaps : MapsTo (K.inverseChart z m) (canonicalOpen S K m) (annularOpen D) :=
    fun y hy => (h04.1.domains z hz hs m).2.2.1 (hgeom.2.1 hy)
  exact (hf.comp hgeom.2.2.2.2.2.1 hmaps).div
    (hgeom.2.2.2.2.2.2.1.comp hgeom.2.2.2.2.2.1 hgeom.2.1)
    (fun y hy => (hgeom.2.2.2.2.2.2.2 _ (hgeom.2.1 hy)).1.ne')

theorem n07a_candidateCanonicalHeight_periodic
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (m : ℕ) :
    ∀ y ∈ canonicalOpen S K m,
      canonicalHeight S K z m f (y + (0, Real.pi)) = canonicalHeight S K z m f y := by
  have hgeom := h04.1.charts z hz hs m
  have hper := n07a_current_inverseChart_periodic h04 hz hs m
  intro y hy
  have hh := (hgeom.2.2.2.2.2.2.2 _ (hgeom.2.1 hy)).2.2.2
  simp only [canonicalHeight, hper y hy, hf (K.inverseChart z m y), hh]

theorem n07a_candidateCanonicalHeight_even
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hf : ∀ r θ, f (r, -θ) = f (r, θ)) (m : ℕ) :
    ∀ y ∈ canonicalOpen S K m,
      canonicalHeight S K z m f (y.1, -y.2) = canonicalHeight S K z m f y := by
  intro y hy
  have hx := (h04.1.charts z hz hs m).2.1 hy
  have hInv := h04.1.inverseReflection z hz hs m y hy
  have hreflect := h04.1.reflection z hz hs m _ hx
  simp only [canonicalHeight, hInv, hreflect.2.1, hf]

theorem n07a_currentHeight_volume
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hV : IsVolumeModel T S K V)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space) (t s : ℕ) :
    ∃ W : V.level (3 / 4 : ℝ) (t : ℝ) s,
      ∀ m, (V.forget (3 / 4 : ℝ) (t : ℝ) s W m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          canonicalHeight S K (liftSectorParameter S C z) m
            ((S.height (3 / 4 : ℝ)).decode u) := by
  have hdecode := (hS.1 (3 / 4 : ℝ)).2.2.2.1 u
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := h01.2.2.1.liftSectorParameter_sector z
  exact n07a_fixedJetEnvelope_volume hD hT h04 href hV
    (n07a_candidateCanonicalHeight_contDiffOn h04 hz' hs hdecode.1)
    (n07a_candidateCanonicalHeight_periodic h04 hz' hs hdecode.2.2.1)
    (n07a_candidateCanonicalHeight_even h04 hz' hs hdecode.2.1)
    (fun c => n07a_currentCanonicalHeight_fixedJetEnvelope
      hD hT hS h01 h04 href hcur hRatio z hz u c) t s

end ContinuousFlexibility.Analysis
