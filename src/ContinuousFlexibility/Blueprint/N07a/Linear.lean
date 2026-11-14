module

public import ContinuousFlexibility.Analysis.N07aActualForwardDifferentialBound
public import ContinuousFlexibility.Analysis.N07aStageRestriction
public import ContinuousFlexibility.Analysis.N07aActualCanonicalSolutionBounds
public import ContinuousFlexibility.Analysis.N07aCandidateConstruction
public import ContinuousFlexibility.Analysis.N07aLinearFromCandidate
public import ContinuousFlexibility.Analysis.N07aAngularCandidateUniqueness
public import ContinuousFlexibility.Analysis.N07aConstructionRestriction

/-!
# N07a: the normalized physical linear inverse and its fixed loss

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 637–790.
Task: `docs/tasks/N07a-Linear.md`.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

variable (A : RadialReference) (T : MaterialData) (S : PhysicalSpacesData)
  (C : NonlinearGeometryData S) (R : ReturnEquationData S)
  (L : ReturnCorrectionData S) (K : CanonicalData S) (V : VolumeModelData S K)
  (b : ℕ) (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)
  (base loss : ℕ) (ε : ℝ)

private theorem n07aLinear_of_actual_geometry
    (hT : IsMaterialData A.val T) (hS : IsPhysicalSpaces A.val T S)
    (h06 : NonlinearPropertiesThrough06 A.val T S C R L K V b B P base loss ε)
    (hAngular : N07aAngularProperties S C K V b B P base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hFirst : N07aActualForwardFirstBound T S C K base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∃ G : ScalarInverseData S,
        ScalarLinearInverseProperties A.val S C L G base' ε' := by
  have h01 : N01Properties A.val T S C base loss ε := h06.1.1.1.1.1
  have h04 : N04Properties A.val T S C L K base loss ε := h06.1.1.2.2.2.2.1
  have hprimitive : CanonicalGeometry.PrimitiveGeometryProperties A.val T S C L K base ε :=
    h06.1.1.2.2.2.2.2.1
  let canonical := n07a_exists_actualCanonicalSolutionData A.property.1 hT hS h01 h04
    hprimitive.2.2.1 hprimitive.2.1 hprimitive.2.2.2.1 hRatio h06.1.2 h06.2 hAngular
  let base₁ : ℕ := canonical.choose
  have hb₁ : base ≤ base₁ := canonical.choose_spec.1
  let ε₁ : ℝ := canonical.choose_spec.2.choose
  have canonicalNeighborhood := canonical.choose_spec.2.choose_spec
  have he₁ : 0 < ε₁ := canonicalNeighborhood.1
  have he₁ε : ε₁ ≤ ε := canonicalNeighborhood.2.1
  let data : N07aActualCanonicalSolutionData A.val T S C L K V b B P base₁ ε₁ :=
    Classical.choice canonicalNeighborhood.2.2
  have h06₁ := n07a_through06_restrict hT h06 hb₁ he₁ε he₁
  have h01₁ : N01Properties A.val T S C base₁ loss ε₁ := h06₁.1.1.1.1.1
  have h02₁ : N02Properties A.val T S C R base₁ ε₁ := h06₁.1.1.1.1.2
  have h03₁ : N03Properties A.val T S C R L base₁ ε₁ := h06₁.1.1.1.2
  have h04₁ : N04Properties A.val T S C L K base₁ loss ε₁ := h06₁.1.1.2.2.2.2.1
  have hprimitive₁ : CanonicalGeometry.PrimitiveGeometryProperties A.val T S C L K
      base₁ ε₁ := h06₁.1.1.2.2.2.2.2.1
  let candidate := n07a_exists_boundedPhysicalCandidate A.property.1 hT hS
    h01₁ h02₁ h03₁ h04₁ hprimitive₁.2.2.1 hprimitive₁.2.2.2.1
    (hRatio.restrict hb₁ he₁ε) (hFirst.restrict hb₁ he₁ε)
    h06₁.1.1.2.2.2.2.2.2 h06₁.1.2 data
  let base₂ : ℕ := candidate.choose
  have hb₂ : base₁ ≤ base₂ := candidate.choose_spec.1
  let ε₂ : ℝ := candidate.choose_spec.2.choose
  have candidateNeighborhood := candidate.choose_spec.2.choose_spec
  have he₂ : 0 < ε₂ := candidateNeighborhood.1
  have he₂ε : ε₂ ≤ ε₁ := candidateNeighborhood.2.1
  let u : CanonicalGeometry.Parameter S → S.Source → HeightPair S × ℝ :=
    candidateNeighborhood.2.2.choose
  have hsol : ∀ z ∈ sectorNeighborhood S base₂ ε₂ ε₂, ∀ f,
      N07aScalarSolution A.val S C L (liftSectorParameter S C z) f (u z f) :=
    candidateNeighborhood.2.2.choose_spec.1
  have hbound : ∃ d low : ℕ, ∀ s : ℕ, ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ z ∈ sectorNeighborhood S base₂ ε₂ ε₂, ∀ f,
        n07aOutputGrading S s (u z f) ≤ A₀ *
          (S.sourceGrading (s + d) f +
            (1 + CanonicalGeometry.parameterGrading S (s + d) z) * S.sourceGrading low f) :=
    candidateNeighborhood.2.2.choose_spec.2
  have h06₂ := n07a_through06_restrict hT h06₁ hb₂ he₂ε he₂
  have h01₂ : N01Properties A.val T S C base₂ loss ε₂ := h06₂.1.1.1.1.1
  have h02₂ : N02Properties A.val T S C R base₂ ε₂ := h06₂.1.1.1.1.2
  have h03₂ : N03Properties A.val T S C R L base₂ ε₂ := h06₂.1.1.1.2
  have h04₂ : N04Properties A.val T S C L K base₂ loss ε₂ := h06₂.1.1.2.2.2.2.1
  have hprimitive₂ : CanonicalGeometry.PrimitiveGeometryProperties A.val T S C L K
      base₂ ε₂ := h06₂.1.1.2.2.2.2.2.1
  have hcanonical₂ : CanonicalPrimitiveGeometry A.val T S C L K base₂ ε₂ :=
    h06₂.1.1.2.2.2.2.2.2
  let inverse := n07a_exists_scalarLinearInverse_of_boundedCandidate
    hS hT h01₂ h02₂ h03₂ u hsol hbound
    (fun z hz hs f v w hv hw => n07a_scalarSolution_unique A.property.1 hT hS
      h01₂ h02₂ h03₂ h04₂ A.property.2.2.2.1 hprimitive₂.1 hprimitive₂.2.2.1
      hprimitive₂.2.2.2.1 (hRatio.restrict (hb₁.trans hb₂) (he₂ε.trans he₁ε)) hcanonical₂ h06₂.1.2 h06₂.2 hz hs hv hw)
  let G : ScalarInverseData S := inverse.choose
  have hG : ScalarLinearInverseProperties A.val S C L G base₂ ε₂ := inverse.choose_spec
  exact ⟨base₂, hb₁.trans hb₂, ε₂, he₂, he₂ε.trans he₁ε, G, hG⟩

theorem N07aLinear
    (hT : IsMaterialData A.val T) (hS : IsPhysicalSpaces A.val T S)
    (h06 : NonlinearPropertiesThrough06 A.val T S C R L K V b B P base loss ε)
    (hAngular : N07aAngularProperties S C K V b B P base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∃ G : ScalarInverseData S,
        ScalarLinearInverseProperties A.val S C L G base' ε' := by
  have h01 : N01Properties A.val T S C base loss ε := h06.1.1.1.1.1
  have h04 : N04Properties A.val T S C L K base loss ε := h06.1.1.2.2.2.2.1
  have hp : CanonicalGeometry.PrimitiveGeometryProperties A.val T S C L K base ε :=
    h06.1.1.2.2.2.2.2.1
  obtain ⟨baseR, hbR, εR, heR, heRε, hRatio⟩ :=
    n07a_actualMaterialRatios_neighborhood A.property.1 hT h06.2.1 h01.2.2.1
      h04.1 hp.2.2.1 hp.2.2.2.1
  obtain ⟨baseF, hbF, εF, heF, heFε, hFirst⟩ :=
    n07a_actualForwardFirstBound_neighborhood A.property.1 hT h06.2.1 h01.2.2.1
      h04.1 hp.2.2.1 hp.2.2.2.1
  let base₀ := max baseR baseF
  let ε₀ := min εR εF
  have hb₀ : base ≤ base₀ := hbR.trans (le_max_left _ _)
  have he₀ : 0 < ε₀ := lt_min heR heF
  have he₀ε : ε₀ ≤ ε := (min_le_left _ _).trans heRε
  have h06₀ := n07a_through06_restrict hT h06 hb₀ he₀ε he₀
  have hA₀ := n07a_angularProperties_restrict hAngular hb₀ he₀ε
  obtain ⟨base₁, hb₁, ε₁, he₁, he₁ε, G, hG⟩ :=
    n07aLinear_of_actual_geometry A T S C R L K V b B P base₀ loss ε₀ hT hS h06₀ hA₀
      (hRatio.restrict (le_max_left _ _) (min_le_left _ _))
      (hFirst.restrict (le_max_right _ _) (min_le_right _ _))
  exact ⟨base₁, hb₀.trans hb₁, ε₁, he₁, he₁ε.trans he₀ε, G, hG⟩

end ContinuousFlexibility.Blueprint
