module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryInverseOperatorBounds
public import ContinuousFlexibility.Analysis.TameFixedBaseCompositionBounds

/-! Fixed-base composition of an actual inverse-circle operator with genuine input towers. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n04NegativeGeometryInverseCompositionCircleSMul (H : CircleModelData) :
    SMul ℝ (H.Space × H.Space) := Prod.instSMul

private theorem inverseCompositionJet_eq
    {X Y : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
    {Z : ℕ → Type*} [∀ n, NormedAddCommGroup (Z n)] [∀ n, NormedSpace ℝ (Z n)]
    [∀ n, CompleteSpace (Z n)] {bond : ∀ n, Z (n + 1) →L[ℝ] Z n}
    {U : Set X} {V : Set Y} {f : X → Y} {g : Y → ProjectiveLimit Z bond}
    (J : SmoothDirections U f) (K : SmoothDirections V g)
    (A : SmoothDirections U (fun x => g (f x))) (hmap : MapsTo f U V)
    (n : ℕ) (x : X) (hx : x ∈ U) (v : Fin n → X) :
    A.D n x v = projectiveCompositionJets f J.D K.D n x v := by
  let B : SmoothDirections U (fun x => g (f x)) :=
    smoothDirectionsOfJets J.open_domain (projectiveCompositionJets f J.D K.D)
      (HasProjectiveJetsOn.comp_topological J.open_domain K.open_domain
        J.hasProjectiveJetsOn K.hasProjectiveJetsOn hmap)
  exact congrArg (fun L : X [×n]→L[ℝ] ProjectiveLimit Z bond => L v)
    (A.unique B n x hx)

/-- Select and compose a family while its coefficient spaces and
operators are abstract. The circle realization is supplied only once
at the final application, after all choices and tower comparisons. -/
private theorem inverseFamilyComposition_fixedBase
    {I Q E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    {Z : ℕ → Type*} [∀ n, NormedAddCommGroup (Z n)] [∀ n, NormedSpace ℝ (Z n)]
    [∀ n, CompleteSpace (Z n)] {bond : ∀ n, Z (n + 1) →L[ℝ] Z n}
    {U : Set E} {V : Set F} {f : I → E → F} {g : Q → F → ProjectiveLimit Z bond}
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (r : ℕ → Seminorm ℝ (ProjectiveLimit Z bond))
    (hp : Monotone p) (hI : HasInterpolation (pairGrading realGrading p))
    (travel : I → Q) (J : ∀ i, SmoothDirections U (f i))
    (K : ∀ i, SmoothDirections V (g (travel i))) (BJ : ℕ)
    (hJ : ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → p BJ x ≤ R → ∀ v : Fin n → E,
        q s ((J i).D n x v) ≤ C * tameJetSize p n s L BJ x v)
    (hK : ∃ BK : ℕ, ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t (A : SmoothDirections V (g t)) y,
        y ∈ V → q BK y ≤ R → ∀ v : Fin n → F,
          r s (A.D n y v) ≤ C * tameJetSize q n s L BK y v)
    (hmap : ∀ i, MapsTo (f i) U V) :
    ∃ B : ℕ, BJ ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (A : SmoothDirections U (fun x => g (travel i) (f i x))) x,
        x ∈ U → p B x ≤ R → ∀ v : Fin n → E,
          r s (A.D n x v) ≤ C * tameJetSize p n s L B x v := by
  classical
  choose d hd using hJ
  obtain ⟨BK, hBK⟩ := hK
  choose e he using hBK
  have houter (n : ℕ) (R : ℝ) (hR : 0 ≤ R) (s : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i y, y ∈ V → q BK y ≤ R → ∀ v : Fin n → F,
        r s ((K i).D n y v) ≤ C * tameJetSize q n s (e n) BK y v := by
    obtain ⟨C, hC, hbound⟩ := he n R hR s
    exact ⟨C, hC, fun i y hy hlow v => hbound (travel i) (K i) y hy hlow v⟩
  obtain ⟨B, hB, hbound⟩ := projectiveCompositionJets_fixedBase_oneHigh
    p q r hp hI J K BJ BK d e hd houter hmap
  refine ⟨B, hB, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hbound n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨C, hC, hCs⟩ := hL R hR s
  refine ⟨C, hC, fun i A x hx hlow v => ?_⟩
  have heq := inverseCompositionJet_eq (J i) (K i) A (hmap i) n x hx v
  exact (congrArg (r s) heq).trans_le (hCs i x hx hlow v)

section InverseComposition

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {f g : I → E → H.Space}

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
  have hmap (i : I) : MapsTo (fun x => (f i x, g i x)) U (W ×ˢ univ) :=
    fun x hx => ⟨mem_circleUniformInverseDomain hH hT hD hγ ha (f i x)
      (hlower i x hx), mem_univ _⟩
  exact inverseFamilyComposition_fixedBase
    p (pairGrading H.grading H.grading) H.grading hp hIp travel J KP BJ hJ
    (n04NegativeGeometry_inverseOperator_fixedBase hH hT hD hγ hi JF JP a ha) hmap

end InverseComposition


end ContinuousFlexibility.Statements
