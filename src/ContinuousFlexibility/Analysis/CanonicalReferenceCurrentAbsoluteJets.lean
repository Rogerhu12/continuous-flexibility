import ContinuousFlexibility.Analysis.N07aGeometryJetBounds
import ContinuousFlexibility.Analysis.MaterialSampleBounds
import ContinuousFlexibility.Analysis.N04RealizationJetScalars

/-!
# Absolute unit jets at the actual material sample

The reference jets and the genuine current difference share one fixed
state loss. A uniform bound for the actual positive height power turns
their sum into an explicit E0 envelope, without replacing the sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true
open scoped ContDiff

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
  {base : ℕ} {ε : ℝ}

theorem n04Coordinates_reference_canonicalLengthInverse_envelope
    (href : CanonicalGeometry.ReferenceJets D T S C L K) :
    ∃ B : ℝ, 0 < B ∧ ∀ m,
      |(K.right m - K.left m)⁻¹| ≤ B * T.E0 (T.sample (K.cell m)) ^ B := by
  obtain ⟨B, hB, hb⟩ := href.2 0
  refine ⟨B, hB, fun m => ?_⟩
  have hp : ((1 / 2, 0) : PolarPoint) ∈ CanonicalGeometry.unitStrip := by
    constructor <;> norm_num
  simpa only [spaces_mixedDerivative_zero, CanonicalGeometry.atom] using
    hb m .canonicalLengthInverse (1 / 2, 0) hp 0 0 (by omega)

/-- The loss is chosen once, before every spatial order and every atom. -/
theorem n04Coordinates_unitAtom_absolute_envelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m)))
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m v p,
        p ∈ CanonicalGeometry.unitStrip → ∀ i j : ℕ, i + j ≤ s →
          |mixedDerivative i j
            (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m v) p| ≤
            A * T.E0 (T.sample (K.cell m)) ^ B *
              (1 + CanonicalGeometry.parameterGrading S (s + loss) z) := by
  have hHeight : ∃ CH : ℝ, 0 < CH ∧ ∀ m,
      T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (K.cell m)) ^ (0 : ℝ) ≤ CH :=
    material_sample_height_coefficient_power_bounded
      hD hT K.cell 0 (by norm_num : (0 : ℝ) < 3 / 4)
  let CH : ℝ := hHeight.choose
  have hCH : 0 < CH := hHeight.choose_spec.1
  have hHb (m : ℕ) : T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) ≤ CH := by
    simpa only [CH, Real.rpow_zero, mul_one] using hHeight.choose_spec.2 m
  let loss : ℕ := hcur.2.1.choose
  have hdiff := hcur.2.1.choose_spec
  refine ⟨loss, fun s => ?_⟩
  let B₀ : ℝ := (href.2 s).choose
  have hB₀ : 0 < B₀ := (href.2 s).choose_spec.1
  have hb₀ := (href.2 s).choose_spec.2
  let B₁ : ℝ := (hdiff s).choose
  have hB₁ : 0 < B₁ := (hdiff s).choose_spec.1
  have hb₁ := (hdiff s).choose_spec.2
  have hscalar := n04Realization_referenceAndDifferenceEnvelope hB₀.le hB₁.le hCH.le
  let Q : ℝ := hscalar.choose
  have hQ : 0 < Q := hscalar.choose_spec.1
  refine ⟨Q, Q, hQ, hQ, ?_⟩
  intro z hz m v p hp i j hij
  have he := congrArg abs
    (n07a_geometryAtom_jet_decomposition href hcur z hz m v ⟨p, hp⟩ i j)
  exact he.trans_le (hscalar.choose_spec.2
    (T.E0 (T.sample (K.cell m))) (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ))
    (CanonicalGeometry.parameterGrading S (s + loss) z) _ _
    (hfloor m) (hHb m) (apply_nonneg _ _)
    (hb₀ m v p hp i j hij) (hb₁ z hz m v ⟨p, hp⟩ i j hij))

end ContinuousFlexibility.Analysis
