import ContinuousFlexibility.Analysis.N07aGeometryJetBounds
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Absolute unit jets at the actual material sample

The reference jets and the genuine current difference share one fixed
state loss. A uniform bound for the actual positive height power turns
their sum into an explicit E0 envelope, without replacing the sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
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
  obtain ⟨CH, hCH, hHb⟩ := material_sample_height_coefficient_power_bounded
    hD hT K.cell 0 (by norm_num : (0 : ℝ) < 3 / 4)
  have hHeight (m : ℕ) : T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) ≤ CH := by
    simpa only [Real.rpow_zero, mul_one] using hHb m
  let loss : ℕ := hcur.2.1.choose
  have hdiff := hcur.2.1.choose_spec
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B₀, hB₀, hb₀⟩ := href.2 s
  obtain ⟨B₁, hB₁, hb₁⟩ := hdiff s
  let A : ℝ := B₀ + B₁ * CH
  let B : ℝ := max B₀ B₁
  refine ⟨A, B, add_pos hB₀ (mul_pos hB₁ hCH),
    hB₀.trans_le (le_max_left _ _), ?_⟩
  intro z hz m v p hp i j hij
  let E : ℝ := T.E0 (T.sample (K.cell m))
  let G : ℝ := CanonicalGeometry.parameterGrading S (s + loss) z
  have hE : 1 ≤ E := hfloor m
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hG : 0 ≤ G := apply_nonneg _ _
  have hEB : 0 ≤ E ^ B := Real.rpow_nonneg hE0 B
  have hH0 : 0 ≤ T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg
      (hT.2.1 _ (materialSample_mem_interval hD hT (K.cell m))).2.1.le _
  have he₀ : E ^ B₀ ≤ E ^ B :=
    Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _)
  have he₁ : E ^ B₁ ≤ E ^ B :=
    Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _)
  have hr : |mixedDerivative i j
      (CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m v) p| ≤
        B₀ * E ^ B :=
    (hb₀ m v p hp i j hij).trans (mul_le_mul_of_nonneg_left he₀ hB₀.le)
  have hd : |CanonicalGeometry.differenceJets D T S C L K z v m i j ⟨p, hp⟩| ≤
      B₁ * E ^ B * CH * G :=
    (hb₁ z hz m v ⟨p, hp⟩ i j hij).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left he₁ hB₁.le)
          (hHeight m) hH0 (mul_nonneg hB₁.le hEB)) hG)
  have hExtra : 0 ≤ E ^ B * (B₁ * CH + B₀ * G) :=
    mul_nonneg hEB (add_nonneg (mul_nonneg hB₁.le hCH.le) (mul_nonneg hB₀.le hG))
  rw [n07a_geometryAtom_jet_decomposition href hcur z hz m v ⟨p, hp⟩ i j]
  calc
    _ ≤ |CanonicalGeometry.differenceJets D T S C L K z v m i j ⟨p, hp⟩| +
        |mixedDerivative i j
          (CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m v) p| :=
      abs_add_le _ _
    _ ≤ B₁ * E ^ B * CH * G + B₀ * E ^ B := add_le_add hd hr
    _ ≤ A * E ^ B * (1 + G) := by
      dsimp only [A]
      nlinarith [hExtra]

end ContinuousFlexibility.Analysis
