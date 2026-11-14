module

public import ContinuousFlexibility.Analysis.N08JointResidual
public import ContinuousFlexibility.Analysis.N08ColumnData
public import ContinuousFlexibility.Analysis.N08ControlInverseResponse

/-!
# Combining the actual residual and control estimates on one neighborhood

The scalar residual, both genuine columns, and their inverse-response
estimates have already been constructed. This assembly lemma combines them
with the numerical uniform bound for the same actual circle diagonal. It
keeps the physical spaces, scalar inverse, and all derivative identities.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem n08_with_joint_residual_witness
    {I J W : Type*} {A B C : I → J → Prop}
    {D E F : I → J → W → Prop} {P : Prop}
    (h : ∃ i : I, ∃ j : J, A i j ∧ B i j ∧ C i j ∧
      ∃ w : W, D i j w ∧ E i j w ∧ F i j w)
    (hP : ∀ i j, A i j → B i j → C i j →
      ∀ w, D i j w → E i j w → F i j w → P) : P := by
  obtain ⟨i, j, ha, hb, hc, w, hd, he, hf⟩ := h
  exact hP i j ha hb hc w hd he hf

private theorem n08_with_control_response_witness
    {I J K W : Type*} {A B C D : I → J → K → Prop}
    {E F G H : I → J → K → W → Prop} {P : Prop}
    (h : ∃ i : I, ∃ j : J, ∃ k : K,
      A i j k ∧ B i j k ∧ C i j k ∧ D i j k ∧
      ∃ w : W, E i j k w ∧ F i j k w ∧ G i j k w ∧ H i j k w)
    (hP : ∀ i j k, A i j k → B i j k → C i j k → D i j k →
      ∀ w, E i j k w → F i j k w → G i j k w → H i j k w → P) : P := by
  obtain ⟨i, j, k, ha, hb, hc, hd, w, he, hf, hg, hh⟩ := h
  exact hP i j k ha hb hc hd w he hf hg hh

private theorem n08_assembly_with_positive_bound
    {Condition : ℝ → Prop} {P : Prop}
    (h : ∃ K : ℝ, 0 < K ∧ Condition K)
    (hP : ∀ K : ℝ, 0 < K → Condition K → P) : P := by
  obtain ⟨K, hK, hCondition⟩ := h
  exact hP K hK hCondition

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {G : ScalarInverseData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08Properties_of_uniform_diagonal
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    {diagonalBase : ℕ} {diagonalRadius : ℝ}
    (hdiagonalRadius : 0 < diagonalRadius)
    (hdiagonal : ∀ z ∈ stateNeighborhood S C diagonalBase diagonalRadius,
      stateSector S z.1 → ∀ m,
        (1 / 2 : ℝ) ≤ |n08CircleDiagonal hS hR z m| ∧
          |n08CircleDiagonal hS hR z m| ≤ 2) :
    ∃ newBase newLoss : ℕ, ∃ η : ℝ,
      base ≤ newBase ∧ loss ≤ newLoss ∧ 0 < η ∧ η ≤ ε ∧
      ∃ P : ResidualData S, ∃ B : ControlColumnData S,
        N08Properties D T S C R G P B newBase newLoss η := by
  refine n08_with_joint_residual_witness
    (W := AnnularState S × ℝ → S.Source)
    (n08ResidualData_nu_and_smooth hT hS hN hR) ?_
  intro scalarBase scalarRadius hscalarBase hscalarRadius hscalarOld ν
    hnuDecode hnuDeriv hjoint
  refine n08_with_control_response_witness
    (W := AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source)
    (n08ControlInverseResponse_exists hT hS hN hG) ?_
  intro responseBase responseLoss responseRadius hresponseBase hresponseLoss
    hresponseRadius hresponseOld H _ hcontrolDeriv hresponse hcontrolSmooth
  let newBase : ℕ := max scalarBase (max responseBase diagonalBase)
  let η : ℝ := min scalarRadius (min responseRadius diagonalRadius)
  let P : ResidualData S := n08ResidualData hT hS hN hR
  let B : ControlColumnData S := n08ColumnData hS hR H ν
  have hbScalar : scalarBase ≤ newBase := le_max_left _ _
  have hbResponse : responseBase ≤ newBase :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hbDiagonal : diagonalBase ≤ newBase :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hb : base ≤ newBase := hscalarBase.trans hbScalar
  have hη : 0 < η := lt_min hscalarRadius (lt_min hresponseRadius hdiagonalRadius)
  have hηScalar : η ≤ scalarRadius := min_le_left _ _
  have hηResponse : η ≤ responseRadius :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηDiagonal : η ≤ diagonalRadius :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hηε : η ≤ ε := hηScalar.trans hscalarOld
  have hsub : stateNeighborhood S C newBase η ⊆ stateNeighborhood S C base ε :=
    n08_stateNeighborhood_mono hb hηε
  have hsubScalar : stateNeighborhood S C newBase η ⊆
      stateNeighborhood S C scalarBase scalarRadius :=
    n08_stateNeighborhood_mono hbScalar hηScalar
  have hsubResponse : stateNeighborhood S C newBase η ⊆
      stateNeighborhood S C responseBase responseRadius :=
    n08_stateNeighborhood_mono hbResponse hηResponse
  have hsubDiagonal : stateNeighborhood S C newBase η ⊆
      stateNeighborhood S C diagonalBase diagonalRadius :=
    n08_stateNeighborhood_mono hbDiagonal hηDiagonal
  refine ⟨newBase, responseLoss, η, hb, hresponseLoss, hη, hηε, P, B, ?_⟩
  refine ⟨n08_isClosed_stateSector hS, n08_isOpen_sectorNeighborhood S newBase η η,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz hs p hp
    exact n08ResidualData_scalar_decode hT hS hN hR (hsub hz) hs p hp
  · intro z hz hs
    exact n08ResidualData_circle_coe hT hS hN hR (hsub hz) hs
  · exact n08ResidualData_reference hT hS hN hR
  · exact n08ControlRestriction_apply hS
  · intro z hz hs p hp
    exact hnuDecode z (hsubScalar hz) hs p hp
  · intro z hz
    exact hnuDeriv z (hsubScalar hz)
  · intro z hz hs u
    exact hcontrolDeriv z (hsubResponse hz) hs u
  · intro z hz hs u
    exact n08HeightRow_hasLineDerivAt hS hT hN hR (hsub hz) hs u
  · intro z hz hs u
    exact n08CircleColumn_hasLineDerivAt hS hN.2.2.1 hR (hsub hz) hs u
  · intro z hz hs u
    change n08ControlRestriction S (n08CircleColumn hS hR z u) =
      n08BoundedControlDiagonal (n08CircleDiagonal hS hR) z (n08ControlRestriction S u)
    have heval := congrArg
      (fun A : ControlBanach →L[ℝ] ControlBanach => A (n08ControlRestriction S u))
      (n08BoundedControlDiagonal_eq (n08CircleDiagonal hS hR) z
        (hdiagonal z (hsubDiagonal hz) hs))
    exact (n08CircleColumn_restriction_eq hT hS hN hR (hsub hz) hs
      (fun m => (hdiagonal z (hsubDiagonal hz) hs m).2) u).trans heval.symm
  · intro z hz hs u m
    exact n08BoundedControlDiagonal_apply _ z (hdiagonal z (hsubDiagonal hz) hs) u m
  · intro m
    exact n08CircleDiagonal_reference hT hS hN hR m
  · intro z hz hs u
    exact n08BoundedControlDiagonal_inverse _ z (hdiagonal z (hsubDiagonal hz) hs) u
  · intro z hz hs m
    exact hdiagonal z (hsubDiagonal hz) hs m
  · intro s
    refine n08_assembly_with_positive_bound (hresponse s) ?_
    intro K hK hKb
    exact ⟨K, hK, fun z hz u => hKb z (hsubResponse hz) u⟩
  · exact smoothTameOn_mono hjoint (n08_isOpen_sectorNeighborhood S newBase η η)
      (n08_sectorNeighborhood_mono hbScalar hηScalar hηScalar)
  · exact smoothTameOn_mono hcontrolSmooth
      ((n08_isOpen_sectorNeighborhood S newBase η η).prod isOpen_univ)
      (Set.prod_mono (n08_sectorNeighborhood_mono hbResponse hηResponse hηResponse)
        (subset_refl _))

end ContinuousFlexibility.Statements
