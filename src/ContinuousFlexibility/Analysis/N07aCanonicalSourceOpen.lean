module

public import ContinuousFlexibility.Analysis.N06Neighborhood
public import ContinuousFlexibility.Analysis.N07aCanonicalSourceBounds
public import ContinuousFlexibility.Analysis.N07aCanonicalSourceRegularity
public import ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficients
public import ContinuousFlexibility.Analysis.N07aParameterNeighborhood

/-!
# The actual source in the bounded open coefficient algebra

The source is the original height decoder followed by the actual current
source transform. One justified low-order restriction bounds all of its
mixed jets on every open canonical piece. No regularity certificate for a
replacement source is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
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
  {base loss : ℕ} {ε : ℝ}

private theorem n07a_sourceOpen_with_neighborhood
    {b : ℕ} {η : ℝ} {Condition : ℕ → ℝ → Prop} {P : Prop}
    (h : ∃ b', b ≤ b' ∧ ∃ η', 0 < η' ∧ η' ≤ η ∧ Condition b' η')
    (hP : ∀ b', b ≤ b' → ∀ η', 0 < η' → η' ≤ η → Condition b' η' → P) : P := by
  obtain ⟨b', hb, η', hη', hη, hc⟩ := h
  exact hP b' hb η' hη' hη hc

private theorem n07a_exists_canonicalSourceOpen_neighborhood_of_ratios
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε',
        ∀ f : (S.height (3 / 4 : ℝ)).Space, ∀ m : ℕ,
          ∃ χ : N07aCanonicalOpenCoefficient S K m,
            χ.value = canonicalSource S K (liftSectorParameter S C z) m
              ((S.height (3 / 4 : ℝ)).decode f) := by
  have hj := n07a_canonicalSource_height_sampleJets hD hT hS
    (by norm_num : 0 ≤ (3 / 4 : ℝ)) (by norm_num : (3 / 4 : ℝ) ≤ 1)
    hrefState h04 href hcur hRatio
  let low : ℕ := hj.choose
  let d : ℕ := hj.choose_spec.choose
  have hjb := hj.choose_spec.choose_spec
  have hn := n07a_lowParameter_neighborhood (S := S) (base := base) hε low
  let base' : ℕ := hn.choose
  let ε' : ℝ := hn.choose_spec.2.choose
  have hnb := hn.choose_spec.2.choose_spec
  refine ⟨base', hn.choose_spec.1, ε', hnb.1, hnb.2.1, ?_⟩
  intro z hz f m
  have hz₀ : z ∈ sectorNeighborhood S base ε ε := hnb.2.2.1 hz
  have hlow : CanonicalGeometry.parameterGrading S low z ≤ 1 := hnb.2.2.2 z hz
  let v : PolarPoint → ℝ := canonicalSource S K (liftSectorParameter S C z) m
    ((S.height (3 / 4 : ℝ)).decode f)
  have hv : ContDiffOn ℝ ∞ v (canonicalOpen S K m) :=
    n07a_canonicalSource_contDiffOn hrefState h04 hcur z hz₀
      ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f).1 m
  have hp : ∀ p ∈ canonicalOpen S K m, v (p + (0, Real.pi)) = v p :=
    n07a_canonicalSource_periodic_on hrefState h04 hcur z hz₀
      ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f).2.2.1 m
  have hb : ∀ a b : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ p ∂canonicalMeasure S K m, |mixedDerivative a b v p| ≤ M := by
    intro a b
    let bound := hjb a b 0
    let e : ℕ → ℝ := bound.choose
    let M : ℝ := e m *
      (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ (0 : ℕ))⁻¹) *
      ((S.height (3 / 4 : ℝ)).grading (0 + (a + b) + d) f +
        (1 + CanonicalGeometry.parameterGrading S (0 + (a + b) + d) z) *
          (S.height (3 / 4 : ℝ)).grading low f)
    refine ⟨|M|, abs_nonneg _, ?_⟩
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    exact (bound.choose_spec.2.2 z ⟨hz₀, hlow⟩ f m p hp).trans (le_abs_self M)
  exact ⟨⟨v, hv, hp, hb⟩, rfl⟩

theorem n07a_exists_canonicalSourceOpen_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε',
        ∀ f : (S.height (3 / 4 : ℝ)).Space, ∀ m : ℕ,
          ∃ χ : N07aCanonicalOpenCoefficient S K m,
            χ.value = canonicalSource S K (liftSectorParameter S C z) m
              ((S.height (3 / 4 : ℝ)).decode f) := by
  refine n07a_sourceOpen_with_neighborhood
    (n07a_actualMaterialRatios_neighborhood hD hT hε hrefState h04.1 href hcur) ?_
  intro base₀ hb₀ ε₀ he₀ he₀ε hRatio
  have h04₀ := n06_N04Properties_mono h04 hb₀ he₀ε
  have hcur₀ := n07a_currentJets_restrict hD hT hcur hb₀ he₀ε
  refine n07a_sourceOpen_with_neighborhood
    (n07a_exists_canonicalSourceOpen_neighborhood_of_ratios
      hD hT hS he₀ hrefState h04₀ href hcur₀ hRatio) ?_
  intro base₁ hb₁ ε₁ he₁ he₁ε result
  exact ⟨base₁, hb₀.trans hb₁, ε₁, he₁, he₁ε.trans he₀ε, result⟩

end ContinuousFlexibility.Analysis
