import ContinuousFlexibility.Analysis.CirclePositiveInverseFixedBaseBounds

/-!
# Uniform-domain bounds for the actual inverse-circle operator

The fixed lower derivative bound gives a single open domain. Restriction
and uniqueness transfer the existing fixed-base estimate to every genuine
tower on that same domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04NegativeGeometryInverseOperatorCircleSMul (H : CircleModelData) :
    SMul ℝ (H.Space × H.Space) := Prod.instSMul

/-- The input base is uniform in the order, the travel and the actual tower. -/
theorem n04NegativeGeometry_inverseOperator_fixedBase
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading)
    (JF : SmoothDirections univ (fun y : H.Space × H.Space =>
      circleShiftedChartComposeContinuousLinear hH hT hD hγ (fun _ => 0) y.1 y.2))
    (JP : ∀ travel : ℕ → ℝ, SmoothDirections (circlePositiveLiftDomain H ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ travel y.1 y.2))
    (a : ℝ) (ha : 0 < a) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ travel : ℕ → ℝ,
      ∀ K : SmoothDirections (circleUniformInverseDomain H a ×ˢ univ)
        (fun y : H.Space × H.Space =>
          circlePositiveInverseComposeLinear hH hT hD hγ travel y.1 y.2),
      ∀ y ∈ circleUniformInverseDomain H a ×ˢ univ,
        pairGrading H.grading H.grading B y ≤ R →
      ∀ v : Fin n → H.Space × H.Space,
        H.grading s (K.D n y v) ≤
          C * tameJetSize (pairGrading H.grading H.grading) n s L B y v := by
  obtain ⟨B, hB⟩ := circlePositiveInverseComposeLinear_fixedBase_oneHigh
    (D := D) (T := T) (γ := γ) (M := H) hD hT hγ hH hi JF (JP (fun _ => 0)) (a / 2) (half_pos ha)
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hB n
  refine ⟨L, fun R _hR s => ?_⟩
  obtain ⟨C, hC, hb⟩ := hL (max R 1) (le_max_right _ _) s
  refine ⟨C, hC, fun travel K y hy hlow v => ?_⟩
  have hlower (m : ℕ) (θ : ℝ) :
      a / 2 ≤ deriv (circleAffineLift travel (H.decode y.1) 1 m) θ := by
    rw [circleAffineLift_deriv hH]
    exact interior_subset hy.1 m θ
  let K' : SmoothDirections (circleUniformInverseDomain H a ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ travel y.1 y.2) :=
    (JP travel).restrict ((circleUniformInverseDomain_isOpen H a).prod isOpen_univ)
      (fun y hy => ⟨circleUniformInverseDomain_subset_positive ha hy.1, hy.2⟩)
  have heq := congrArg (fun A : (H.Space × H.Space) [×n]→L[ℝ] H.Space => A v)
    (K.unique K' n y hy)
  have heq' : K.D n y v = (JP travel).D n y v := heq
  rw [heq']
  exact hb travel (JP travel) y hlower (hlow.trans (le_max_left _ _)) v

end ContinuousFlexibility.Statements
