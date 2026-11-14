module

public import ContinuousFlexibility.Analysis.N06CurrentSourceJets
public import ContinuousFlexibility.Analysis.N06FinitePhysicalPartition
public import ContinuousFlexibility.Analysis.N06NuPhysicalRegularity

/-!
# Actual current compact sources in the original volume model

The current-source jet bounds follow from the actual closed forward-chart
jets. On the finitely many physical pieces met by a compact support, a
finite sum provides the bound required by the original volume-model
construction. Thus source membership has no canonical jet estimate or
normalization-region support hypothesis.

The final two applications construct the actual current nu column and
the physical compatibility field. These are existence and finite-norm
results at a fixed state; uniform perturbative smallness is a separate
question.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

/-- The actual current angular jets have one bound on any finite set of
pieces, at every prescribed finite order. -/
theorem n06_currentSource_finiteJets_bounded
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi)) (b : ℕ) (I : Finset ℕ) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ m ∈ I, ∀ j, j ≤ b →
      ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative 0 j (canonicalSource S K z m f) p| ≤ δ := by
  classical
  have hbound : ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ j, j ≤ b →
      ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative 0 j (canonicalSource S K z m f) p| ≤ B :=
    fun m => n06_current_canonicalSource_angularJets_bounded h04 hz hs hf hp m b
  choose c hc hjets using hbound
  refine ⟨∑ m ∈ I, c m, Finset.sum_nonneg (fun m _ => (hc m).le), ?_⟩
  intro m hm j hj p hpU
  exact (hjets m j hj p hpU).trans
    (Finset.single_le_sum (fun m _ => (hc m).le) hm)

/-- A smooth periodic even physical source with compact radial support
belongs, after the actual current source transformation, to every fixed
level of the same chosen volume model. No jet bound is an input. -/
theorem n06Volume_exists_current_compact_source
    (hD : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (γ t : ℝ) (b : ℕ)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ p : PolarPoint, f (p.1, -p.2) = f p)
    (hsupport : HasCompactRadialSupport D f) :
    ∃ F : V.level γ t b,
      ∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m f := by
  obtain ⟨J, hJ, hJD, hzero⟩ := hsupport
  have hfinite := n06_currentPieces_finite_on_compact hD hC hcoordinates h04 hz hs hJ hJD
  obtain ⟨δ, hδ, hbound⟩ := n06_currentSource_finiteJets_bounded
    h04 hz hs hf hp b hfinite.toFinset
  obtain ⟨F, hF, _⟩ := n06Volume_exists_finite_canonical_source hD hT hV
    (n06_N04_qualitative_parts h04).1 hz hs γ t b hfinite hf.contDiffOn
    (fun p _ => hp p) (fun p _ => he p) hzero hδ hbound
  exact ⟨F, hF⟩

/-- The genuine nu column at the current state is an actual source in
the selected volume model. Its physical support need not lie in the
normalization region of the current atlas. -/
theorem n06Volume_exists_current_nuSource
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hV : IsVolumeModel T S K V)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (γ t : ℝ) (b : ℕ) :
    ∃ F : V.level γ t b,
      ∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m (nuColumnField D S C z) := by
  obtain ⟨hJ, hJD, hzero⟩ := n06_nuColumns_common_radialSupport hT hS h01
  exact n06Volume_exists_current_compact_source h01.1.1 h01.2.2.2.1
    hT hV h04 hcoordinates hz hs
    γ t b (n06_nuColumn_contDiff hT hS h01 hz hs)
    (n06_nuColumn_periodic hT hS h01 z) (n06_nuColumn_even hT hS h01 z)
    ⟨tsupport D.chi, hJ, hJD, hzero z⟩

/-- The original compatibility field also belongs to the same source
level in the actual current coordinates, with no fixed-chart support
condition. -/
theorem n06Volume_exists_current_compatibilitySource
    (hD : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (γ t : ℝ) (b : ℕ) :
    ∃ F : V.level γ t b,
      ∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode S.psi) := by
  have hψ := (hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi
  exact n06Volume_exists_current_compact_source hD hC hT hV h04 hcoordinates hz hs γ t b
    (physical_height_contDiff_and_flatJets hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) S.psi).1 hψ.2.2.1
    (fun p => hψ.2.1 p.1 p.2) hS.2.2.2.2.2.2.2.2.1

end ContinuousFlexibility.Statements
