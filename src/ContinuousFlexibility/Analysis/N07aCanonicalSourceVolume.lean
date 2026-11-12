import ContinuousFlexibility.Analysis.N06Neighborhood
import ContinuousFlexibility.Analysis.N07aCanonicalSourceRegularity
import ContinuousFlexibility.Analysis.N07aLinearJetVolumeBounds
import ContinuousFlexibility.Analysis.N07aParameterNeighborhood

/-!
# The original physical source in every prescribed canonical volume level

One low-order neighborhood serves all angular and material orders. The
constructed classes represent the original canonical source, and the
complete sampled envelope costs only two additional material orders.
-/

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
  {V : VolumeModelData S K} {base loss : ℕ} {ε γ : ℝ}

local instance n07aCanonicalSourceVolumeLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) :=
  Submodule.normedAddCommGroup _

local instance n07aCanonicalSourceVolumeLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) :=
  Submodule.normedSpace _

private theorem n07a_sourceVolume_with_neighborhood
    {b : ℕ} {η : ℝ} {Condition : ℕ → ℝ → Prop} {P : Prop}
    (h : ∃ b', b ≤ b' ∧ ∃ η', 0 < η' ∧ η' ≤ η ∧ Condition b' η')
    (hP : ∀ b', b ≤ b' → ∀ η', 0 < η' → η' ≤ η → Condition b' η' → P) : P := by
  obtain ⟨b', hb, η', hη', hη, hc⟩ := h
  exact hP b' hb η' hη' hη hc

private theorem n07a_canonicalSource_height_volume_of_ratios
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hV : IsVolumeModel T S K V) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∃ low outLoss : ℕ, ∀ t s : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧
        ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ u : (S.height γ).Space,
          ∃ Fts : V.level γ (t : ℝ) s,
            (∀ m, (V.forget γ (t : ℝ) s Fts m : PolarPoint → ℝ)
              =ᵐ[canonicalMeasure S K m]
                canonicalSource S K (liftSectorParameter S C z) m ((S.height γ).decode u)) ∧
            ‖Fts‖ ≤ C₀ * ((S.height γ).grading (t + s + outLoss) u +
              (1 + CanonicalGeometry.parameterGrading S (t + s + outLoss) z) *
                (S.height γ).grading low u) := by
  have hj := n07a_canonicalSource_height_sampleJets hD hT hS hγ hγ1
    hrefState h04 href hcur hRatio
  let low : ℕ := hj.choose
  let d : ℕ := hj.choose_spec.choose
  have hjb := hj.choose_spec.choose_spec
  have hn := n07a_lowParameter_neighborhood (S := S) (base := base) hε low
  let base' : ℕ := hn.choose
  let ε' : ℝ := hn.choose_spec.2.choose
  have hnb := hn.choose_spec.2.choose_spec
  let U := sectorNeighborhood S base' ε' ε'
  have hU : U ⊆ sectorNeighborhood S base ε ε := hnb.2.2.1
  have hf := hjb.restrict (fun z (hz : z ∈ U) => ⟨hU hz, hnb.2.2.2 z hz⟩)
  refine ⟨base', hn.choose_spec.1, ε', hnb.1, hnb.2.1, low, d + 2, fun t s => ?_⟩
  apply n07a_sampleLinearJet_volume_bound hD hT h04 href hV
    (n07aParameterGrading_monotone S) (gradedSeminorm_monotone _ _) hf
  · intro z hz u m
    exact n07a_canonicalSource_contDiffOn hrefState h04 hcur z (hU hz)
      ((hS.1 γ).2.2.2.1 u).1 m
  · intro z hz u m
    exact n07a_canonicalSource_periodic_on hrefState h04 hcur z (hU hz)
      ((hS.1 γ).2.2.2.1 u).2.2.1 m
  · intro z hz u m
    exact n07a_canonicalSource_even_on h04
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) (hU hz) le_rfl)
      (hrefState.liftSectorParameter_sector z) ((hS.1 γ).2.2.2.1 u).2.1 m

theorem n07a_canonicalSource_height_volume
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hV : IsVolumeModel T S K V) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∃ low outLoss : ℕ, ∀ t s : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧
        ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ u : (S.height γ).Space,
          ∃ Fts : V.level γ (t : ℝ) s,
            (∀ m, (V.forget γ (t : ℝ) s Fts m : PolarPoint → ℝ)
              =ᵐ[canonicalMeasure S K m]
                canonicalSource S K (liftSectorParameter S C z) m ((S.height γ).decode u)) ∧
            ‖Fts‖ ≤ C₀ * ((S.height γ).grading (t + s + outLoss) u +
              (1 + CanonicalGeometry.parameterGrading S (t + s + outLoss) z) *
                (S.height γ).grading low u) := by
  refine n07a_sourceVolume_with_neighborhood
    (n07a_actualMaterialRatios_neighborhood hD hT hε hrefState h04.1 href hcur) ?_
  intro base₀ hb₀ ε₀ he₀ he₀ε hRatio
  have h04₀ := n06_N04Properties_mono h04 hb₀ he₀ε
  have hcur₀ := n07a_currentJets_restrict hD hT hcur hb₀ he₀ε
  refine n07a_sourceVolume_with_neighborhood
    (n07a_canonicalSource_height_volume_of_ratios
      hD hT hS hγ hγ1 he₀ hrefState h04₀ href hcur₀ hRatio hV) ?_
  intro base₁ hb₁ ε₁ he₁ he₁ε result
  exact ⟨base₁, hb₀.trans hb₁, ε₁, he₁, he₁ε.trans he₀ε, result⟩

end ContinuousFlexibility.Analysis
