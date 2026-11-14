module

public import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceJets
public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryCompositionPrefixWordData

/-!
# Composition bounds for the actual endpoint source

The actual source is the retained inverse chart composed with its fixed
reference chart. This module transfers abstract word bounds for those
two factors to every positive source jet of order at most four. Material
samples and seminorm windows are supplied separately by the sampled
prefix construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04SourceWordStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_sourceJet_word_bound
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀)
        base ε m (!side), ∀ n : ℕ, 1 ≤ n → n ≤ 4 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_sourceJet W.S W.C (X.src i side) (W.A X.e₀) n),
      ∀ K s d : ℕ, K + s + d ≤ N →
      ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
      (∀ j, 1 ≤ j → j ≤ n →
        ∀ JI : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
          (n04PositiveGeometry_storedInverseJet W.S W.C (W.A X.e₀) m (!side) j),
        N04BoundaryWordBounds JI K s d z θ P M H t shift) →
      (∀ j, 1 ≤ j → j ≤ n →
        ∀ JR : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
          (n04PositiveGeometry_referenceForwardJet W.S W.C (W.A X.e₀) m (!side) j),
        N04BoundaryWordBounds JR K s d z θ P M H t shift) →
      N04BoundaryWordBounds Q K s d z θ P (C * M ^ (5 + 2 * N)) H t shift := by
  let wordData : N04PlaneCompositionPrefixWordData (StateDirections W.S × ℝ) N :=
    n04PositiveGeometry_planeCompositionPrefixWordData N
  have hC : 1 ≤ (16 : ℝ) * wordData.C := by
    nlinarith only [wordData.one_le_C]
  refine ⟨16 * wordData.C, hC, ?_⟩
  intro i side m hm hctx n hn hn4 Q K s d hNorder z hz θ P
    M H t hM hH hHM ht shift hI hR
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  have hA : CanonicalGeometry W.D W.S W.C (W.A X.e₀) base ε :=
    n04PartA_restrict (n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field X.e₀) hb hεW
  have hrad := n04PositiveGeometry_sourceEndpoint_eq_root (X.src i side) hm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D :=
    hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 :=
    hrad.symm ▸ (W.roots i side).2.1
  let F := fun y : (StateDirections W.S × ℝ) × ℝ =>
    (W.A X.e₀).inverseChart (liftSectorParameter W.S W.C y.1)
      (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1)
  let G := fun _y : (StateDirections W.S × ℝ) × ℝ =>
    (W.A X.e₀).chart (W.C.referenceState, 0)
      (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1)
  let q := fun y : (StateDirections W.S × ℝ) × ℝ => (n04PositiveEndpoint i side, y.2)
  have hreg := fun y hy => n04PositiveGeometry_sourceComposite_regularities
    W.hT W.hS hN hflow hA (X.src i side) hm hctx (y := y) hy
  let JI : ∀ j, 1 ≤ j → j ≤ n →
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_storedInverseJet W.S W.C (W.A X.e₀) m (!side) j) :=
    fun j hj hjn => n04PositiveGeometry_storedInverseJet_joint W.hT W.hS hN hεone hflow hA
      hctx hr hroot j hj (hjn.trans hn4)
  let JF : ∀ j, 1 ≤ j → j ≤ n →
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (F y) (G y (q y))) :=
    fun j hj hjn => (JI j hj hjn).congr
      (fun y hy => congrArg (iteratedFDeriv ℝ j (F y)) (hreg y hy).1.symm)
  let JR : ∀ j, 1 ≤ j → j ≤ n →
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_referenceForwardJet W.S W.C (W.A X.e₀) m (!side) j) :=
    fun j hj hjn => n04PositiveGeometry_referenceForwardJet_joint W.hT W.hS hN hε hεone hflow
      hctx hr hroot j hj (hjn.trans hn4)
  let JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → PolarPoint,
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (G y) (q y) v) :=
    fun j hj hjn v =>
      (n04PositiveGeometry_boundaryFixedEvaluation_directions (JR j hj hjn) v).congr
        (fun y _ => congrArg
          (fun r : ℝ => iteratedFDeriv ℝ j (G y) (r, y.2) v) hrad)
  have hJF (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      N04BoundaryWordBounds (JF j hj hjn) K s d z θ P M H t shift :=
    N04BoundaryWordBounds.congr (J := JI j hj hjn) (Q := JF j hj hjn)
      (hI j hj hjn (JI j hj hjn)) hz
      (fun y hy => congrArg (iteratedFDeriv ℝ j (F y)) (hreg y hy).1.symm)
  have hJG (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) (v : Fin j → PolarPoint)
      (hv : ∀ a, ‖v a‖ ≤ 1) :
      N04BoundaryWordBounds (JG j hj hjn v) K s d z θ P M H t shift :=
    N04BoundaryWordBounds.congr
      (J := n04PositiveGeometry_boundaryFixedEvaluation_directions (JR j hj hjn) v)
      (Q := JG j hj hjn v) ((hR j hj hjn (JR j hj hjn)).fixedEvaluation v hv) hz
      (fun y _ => congrArg
        (fun r : ℝ => iteratedFDeriv ℝ j (G y) (r, y.2) v) hrad)
  have hformula (y : (StateDirections W.S × ℝ) × ℝ) :
      n04PositiveGeometry_sourceJet W.S W.C (X.src i side) (W.A X.e₀) n y =
        iteratedFDeriv ℝ n (F y ∘ G y) (q y) :=
    congrArg (fun f : PolarPoint → PolarPoint => iteratedFDeriv ℝ n f (q y))
      (n04PositiveGeometry_sourceMap_eq_rootComposite (X.src i side) (W.A X.e₀) hm
        (liftSectorParameter W.S W.C y.1))
  let QC : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y => iteratedFDeriv ℝ n (F y ∘ G y) (q y)) :=
    Q.congr (fun y _ => hformula y)
  have hcomposite : N04BoundaryWordBounds QC K s d z θ P
      (16 * wordData.C * M ^ (5 + 2 * N)) H t shift :=
    wordData.bound (sectorNeighborhood_isOpen W.S base ε ε) F G q
      (fun y hy => (hreg y hy).2.1) (fun y hy => (hreg y hy).2.2)
      n hn hn4 JF JG QC K s d hNorder z hz θ P M H t hM hH hHM ht shift hJF hJG
  exact N04BoundaryWordBounds.congr (J := QC) (Q := Q) hcomposite hz
    (fun y _ => (hformula y).symm)

end ContinuousFlexibility.Analysis
