module

public import ContinuousFlexibility.Analysis.CirclePositiveInverseFixedBaseBounds
public import ContinuousFlexibility.Analysis.CircleTravelUniformJets
public import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations

/-! One fixed base for the actual inverse-composition operator, uniformly in travel. -/

@[expose] public section

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

/-- Restriction and enlargement of the low box are independent of the
concrete projective-limit circle model. Keeping this step abstract also
prevents elaboration from repeatedly expanding that model's operations. -/
private theorem inverseOperator_fixedBase_restrict
    {I E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    {U V : Set E} {f : I → E → F} (hU : IsOpen U) (hUV : U ⊆ V)
    (JP : ∀ i, SmoothDirections V (f i)) (A : I → E → Prop)
    (hA : ∀ i x, x ∈ U → A i x)
    (hbound : ∃ B : ℕ, ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 1 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i (J : SmoothDirections V (f i)) x,
        A i x → p B x ≤ R → ∀ v : Fin n → E,
          q s (J.D n x v) ≤ C * tameJetSize p n s L B x v) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i (K : SmoothDirections U (f i)) x,
        x ∈ U → p B x ≤ R → ∀ v : Fin n → E,
          q s (K.D n x v) ≤ C * tameJetSize p n s L B x v := by
  obtain ⟨B, hB⟩ := hbound
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hB n
  refine ⟨L, fun R _ s => ?_⟩
  obtain ⟨C, hC, hCs⟩ := hL (max R 1) (le_max_right _ _) s
  refine ⟨C, hC, fun i K x hx hlow v => ?_⟩
  have he := inverseOperator_restrict_jet_eq hU hUV (JP i) K n x hx v
  exact (congrArg (q s) he).trans_le
    (hCs i (JP i) x (hA i x hx) (hlow.trans (le_max_left _ _)) v)

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
  have hsub : circleUniformInverseDomain H a ×ˢ (univ : Set H.Space) ⊆
      circlePositiveLiftDomain H ×ˢ univ :=
    fun y hy => ⟨circleUniformInverseDomain_subset_positive ha hy.1, hy.2⟩
  apply inverseOperator_fixedBase_restrict
    (pairGrading H.grading H.grading) H.grading
    ((circleUniformInverseDomain_isOpen H a).prod isOpen_univ) hsub JP
    (fun travel y => ∀ m θ,
      a / 2 ≤ deriv (circleAffineLift travel (H.decode y.1) 1 m) θ)
  · intro travel y hy m θ
    rw [circleAffineLift_deriv hH]
    exact interior_subset hy.1 m θ
  · exact circlePositiveInverseComposeLinear_fixedBase_oneHigh
      hD hT hγ hH hi JF (JP (fun _ => 0)) (a / 2) (half_pos ha)


end ContinuousFlexibility.Statements
