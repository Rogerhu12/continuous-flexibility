import ContinuousFlexibility.Analysis.N04NegativeGeometryInverseOperatorBounds
import ContinuousFlexibility.Analysis.CircleTravelUniformJets
import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations
import ContinuousFlexibility.Analysis.TameFixedBaseCompositionBounds

/-!
# A common base under genuine inverse-circle composition

The forward pair and the actual inverse operator compose through their
projective jets. Their common low bases are chosen before every order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04NegativeGeometryInverseCompositionCircleSMul (H : CircleModelData) :
    SMul ℝ (H.Space × H.Space) := Prod.instSMul

section InverseComposition

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {f g : I → E → H.Space}

/-- The diagonal pair has twice the original grading, without expanding
any concrete state or circle representation. -/
theorem n04NegativeGeometry_diagonalTower_grading
    {f₀ : E → H.Space} (J : SmoothDirections U f₀)
    (n s : ℕ) (x : E) (v : Fin n → E) :
    pairGrading H.grading H.grading s ((smoothDirectionsProd J J).D n x v) =
      H.grading s (J.D n x v) + H.grading s (J.D n x v) := by
  simp only [smoothDirectionsProd, ContinuousMultilinearMap.prod_apply, pairGrading_apply]

/-- One input base precedes all orders and all actual inverse towers.
The hypotheses describe the forward families and their genuine towers;
no inverse estimate is an input. -/
theorem n04NegativeGeometry_circleInverse_fixedBase_oneHigh
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (hIp : HasInterpolation (pairGrading realGrading p))
    (J : ∀ i, SmoothDirections U (fun x => (f i x, g i x)))
    (BJ : ℕ)
    (hJ : ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → p BJ x ≤ R →
      ∀ v : Fin n → E,
        pairGrading H.grading H.grading s ((J i).D n x v) ≤
          C * tameJetSize p n s L BJ x v)
    (travel : I → ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hlower : ∀ i x, x ∈ U → ∀ m θ,
      a ≤ 1 + deriv (H.decode (f i x) m) θ) :
    ∃ B : ℕ, BJ ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (K : SmoothDirections U (fun x =>
        circlePositiveInverseComposeLinear hH hT hD hγ (travel i) (f i x) (g i x))),
      ∀ x ∈ U, p B x ≤ R → ∀ v : Fin n → E,
        H.grading s (K.D n x v) ≤ C * tameJetSize p n s L B x v := by
  classical
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  let W : Set H.Space := circleUniformInverseDomain H a
  have hW : IsOpen W := circleUniformInverseDomain_isOpen H a
  have hsub : W ⊆ circlePositiveLiftDomain H := circleUniformInverseDomain_subset_positive ha
  let JP : ∀ travel : ℕ → ℝ, SmoothDirections (circlePositiveLiftDomain H ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ travel y.1 y.2) :=
    fun travel => (smoothTameOn_circlePositiveInverseComposeLinear hH hT hD hγ hi travel).choose
  let KP : ∀ i, SmoothDirections (W ×ˢ univ)
      (fun y : H.Space × H.Space =>
        circlePositiveInverseComposeLinear hH hT hD hγ (travel i) y.1 y.2) :=
    fun i => (JP (travel i)).restrict (hW.prod isOpen_univ)
      (fun y hy => ⟨hsub hy.1, hy.2⟩)
  let JF : SmoothDirections univ (fun y : H.Space × H.Space =>
      circleShiftedChartComposeContinuousLinear hH hT hD hγ (fun _ => 0) y.1 y.2) :=
    (exists_circleChartComposition_uniform_oneHigh hH hT hD hγ hi (fun _ => 0)).choose
  let operator := n04NegativeGeometry_inverseOperator_fixedBase hH hT hD hγ hi JF JP a ha
  let BK : ℕ := operator.choose
  let d : ℕ → ℕ := fun n => (hJ n).choose
  have hd (n : ℕ) := (hJ n).choose_spec
  let e : ℕ → ℕ := fun n => (operator.choose_spec n).choose
  have he (n : ℕ) := (operator.choose_spec n).choose_spec
  have houter (n : ℕ) (R : ℝ) (_hR : 0 ≤ R) (s : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i y, y ∈ W ×ˢ univ →
        pairGrading H.grading H.grading BK y ≤ R →
        ∀ v : Fin n → H.Space × H.Space,
          H.grading s ((KP i).D n y v) ≤
            C * tameJetSize (pairGrading H.grading H.grading) n s (e n) BK y v := by
    let bound := he n R _hR s
    refine ⟨bound.choose, bound.choose_spec.1, fun i y hy hlow v => ?_⟩
    exact bound.choose_spec.2 (travel i) (KP i) y hy hlow v
  have hmap (i : I) : MapsTo (fun x => (f i x, g i x)) U (W ×ˢ univ) :=
    fun x hx => ⟨mem_circleUniformInverseDomain hH hT hD hγ ha (f i x)
      (hlower i x hx), mem_univ _⟩
  let composite := projectiveCompositionJets_fixedBase_oneHigh
    p (pairGrading H.grading H.grading) H.grading hp hIp J KP BJ BK d e hd houter hmap
  let B : ℕ := composite.choose
  refine ⟨B, composite.choose_spec.1, fun n => ?_⟩
  let lossData := composite.choose_spec.2 n
  let L : ℕ := lossData.choose
  refine ⟨L, fun R hR s => ?_⟩
  let bound := lossData.choose_spec R hR s
  refine ⟨bound.choose, bound.choose_spec.1, fun i K x hx hlow v => ?_⟩
  let Kactual : SmoothDirections U (fun x =>
      circlePositiveInverseComposeLinear hH hT hD hγ (travel i) (f i x) (g i x)) :=
    smoothDirectionsOfJets (J i).open_domain
      (projectiveCompositionJets (fun x => (f i x, g i x)) (J i).D (KP i).D)
      (HasProjectiveJetsOn.comp_topological (J i).open_domain (KP i).open_domain
        (J i).hasProjectiveJetsOn (KP i).hasProjectiveJetsOn (hmap i))
  have heq := congrArg (fun A : E [×n]→L[ℝ] H.Space => A v) (K.unique Kactual n x hx)
  have heq' : K.D n x v =
      projectiveCompositionJets (fun x => (f i x, g i x)) (J i).D (KP i).D n x v := heq
  exact (congrArg (H.grading s) heq').trans_le (bound.choose_spec.2 i x hx hlow v)

end InverseComposition

end ContinuousFlexibility.Statements
