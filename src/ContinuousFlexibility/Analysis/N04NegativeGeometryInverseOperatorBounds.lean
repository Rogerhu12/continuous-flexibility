import ContinuousFlexibility.Analysis.CirclePositiveInverseFixedBaseBounds
import ContinuousFlexibility.Analysis.CircleTravelUniformJets
import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations

/-! One fixed base for the actual inverse-composition operator, uniformly in travel. -/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n04NegativeGeometryInverseBoundsCircleSMul (H : CircleModelData) :
    SMul ℝ (H.Space × H.Space) := Prod.instSMul

private theorem inverseOperator_restrict_jet_eq
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
    {U V : Set E} {f : E → F} (hU : IsOpen U) (hUV : U ⊆ V)
    (J : SmoothDirections V f) (K : SmoothDirections U f)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    K.D n x v = J.D n x v :=
  congrArg (fun A : E [×n]→L[ℝ] F => A v)
    (K.unique (smoothDirectionsRestrict J hU hUV) n x hx)

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
    (M := H) hD hT hγ hH hi JF (JP (fun _ => 0)) (a / 2) (half_pos ha)
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hB n
  refine ⟨L, fun R _hR s => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hL (max R 1) (le_max_right _ _) s
  refine ⟨C, hC, fun travel K y hy hlow v => ?_⟩
  have hlower (m : ℕ) (θ : ℝ) :
      a / 2 ≤ deriv (circleAffineLift travel (H.decode y.1) 1 m) θ := by
    rw [circleAffineLift_deriv hH]
    exact interior_subset hy.1 m θ
  have hsub : circleUniformInverseDomain H a ×ˢ (univ : Set H.Space) ⊆
      circlePositiveLiftDomain H ×ˢ univ :=
    fun y hy => ⟨circleUniformInverseDomain_subset_positive ha hy.1, hy.2⟩
  have heq : K.D n y v = (JP travel).D n y v :=
    inverseOperator_restrict_jet_eq
      ((circleUniformInverseDomain_isOpen H a).prod isOpen_univ) hsub
      (JP travel) K n y hy v
  exact (congrArg (H.grading s) heq).trans_le (hbound travel (JP travel) y hlower
    (hlow.trans (le_max_left _ _)) v)


end ContinuousFlexibility.Statements
