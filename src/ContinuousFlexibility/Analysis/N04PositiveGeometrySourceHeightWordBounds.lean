import ContinuousFlexibility.Analysis.N04PositiveGeometryActualHeightDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryRadialProductComposition

/-! # Word bounds for the literal source height and its reciprocal -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_sourceHeightChoice_word_bound
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (n N : ℕ) (hn : n ≤ 3) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side),
      ∀ inv : Bool,
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × ℝ => radialBoundaryJet (fun p => if inv then
          (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1) p)⁻¹
          else n04PositiveSourceHeight (X.src i side) (W.A X.e₀)
            (liftSectorParameter W.S W.C y.1) p) (n04PositiveEndpoint i side) n y.2),
      ∀ K s d, K + s + d ≤ N → ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ j, j ≤ n → ∀ JR : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_referenceHeightPowerJet W.S W.C (W.A X.e₀) m (!side)
          (if inv then -1 else 1) j), N04BoundaryWordBounds JR K s d z θ P M H t shift) →
      (∀ j, j ≤ n → ∀ JC : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_sourceHeightCurrentJet W X i side m (if inv then 1 else -1) j),
        N04BoundaryWordBounds JC K s d z θ P M H t shift) →
      (∀ j, 1 ≤ j → j ≤ n →
        ∀ JS : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
          (n04PositiveGeometry_sourceJet W.S W.C (X.src i side) (W.A X.e₀) j),
        N04BoundaryWordBounds JS K s d z θ P M H t shift) →
      N04BoundaryWordBounds Q K s d z θ P
        (C * M ^ ((n + 1 + 2 * N) * (N + 2))) H t shift := by
  obtain ⟨C, hC, hbound⟩ := n04PositiveGeometry_radialProductComposition_bound
    (E := StateDirections W.S × ℝ) n N L hL
  refine ⟨C, hC, ?_⟩
  intro i side m hm hctx inv Q K s d hNorder z hz θ P M H t hM hH hHM hHL ht shift hR hCj hS
  let U := sectorNeighborhood W.S base ε ε
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S base ε ε
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let k := if side then ((W.A X.e₀).cutPair m).1 else ((W.A X.e₀).cutPair m).2
  let r := n04PositiveEndpoint i side
  let a : ℝ := if inv then -1 else 1
  let b : ℝ := if inv then 1 else -1
  let f : ((StateDirections W.S × ℝ) × ℝ) → PolarPoint → ℝ :=
    fun _ p => (W.A X.e₀).height (W.C.referenceState, 0) k p ^ a
  let h : ((StateDirections W.S × ℝ) × ℝ) → PolarPoint → ℝ :=
    fun y p => (W.A X.e₀).height (liftSectorParameter W.S W.C y.1) k p ^ b
  let g : ((StateDirections W.S × ℝ) × ℝ) → PolarPoint → PolarPoint :=
    fun y => n04PositiveSourceMap (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1)
  have hrad := n04PositiveGeometry_source_root_eq W X i side m hm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D :=
    hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 :=
    hrad.symm ▸ (W.roots i side).2.1
  have hidx : (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1) = k := by
    cases side <;> rfl
  have hzW (y : (StateDirections W.S × ℝ) × ℝ) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :=
    stateNeighborhood_mono W.S W.C hb hεW
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hy.1 le_rfl)
  have hs (y : (StateDirections W.S × ℝ) × ℝ) := hN.2.2.1.liftSectorParameter_sector y.1
  have hf (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiffAt ℝ ∞ (f y) (r, y.2) := by
    simpa only [hrad, hidx] using n04PositiveGeometry_actualHeightPower_root_smooth W X
      W.through03.1.1.reference_mem_stateNeighborhood W.through03.1.1.2.2.1.stateSector
      m (!side) a y.2
  have hg (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiffAt ℝ ∞ (g y) (r, y.2) :=
    (n04Coordinates_actualAtlas_positiveEndpoint_of_source W.hT W.hS W.through03 W.field
      X.e₀ (X.src i side) (hzW y hy) (hs y)).root_smooth y.2
  have hh (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiffAt ℝ ∞ (h y) (g y (r, y.2)) := by
    have hp := n04PositiveGeometry_source_endpoint_value W X i side m hm (hzW y hy) (hs y) y.2
    have hc := n04PositiveGeometry_actualHeightPower_root_smooth W X (hzW y hy) (hs y)
      m (!side) b (Function.invFun
        (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side)) y.2)
    simpa only [hrad, hidx, ← hp] using hc
  let JR (j : ℕ) (hj : j ≤ n) :=
    n04PositiveGeometry_referenceHeightPowerJet_joint W.hT W.hS hN hε hεone hflow
      hctx hr hroot a j (hj.trans hn)
  let JF (j : ℕ) (hj : j ≤ n) : SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (f y) r j y.2) :=
    (n04PositiveGeometry_boundaryFixedEvaluation_directions (JR j hj) (fun _ => (1, 0))).congr
      (fun y hy => by simpa only [n04PositiveGeometry_referenceHeightPowerJet, hidx, hrad] using
        (n06_radialBoundaryJet_eq_frechet j (hf y hy)).symm)
  let JH (j : ℕ) (hj : j ≤ n) : SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ j (h y) (g y (r, y.2))) :=
    n04PositiveGeometry_sourceHeightCurrentJet_joint W X hb hε hεW hεone hflow
      i side m hm hctx b j (hj.trans hn)
  let JS (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :=
    n04PositiveGeometry_sourceJet_joint W X hb hε hεW hεone hflow
      i side m hm hctx j hj (by omega)
  let JG (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) (v : Fin j → PolarPoint) :=
    n04PositiveGeometry_boundaryFixedEvaluation_directions (JS j hj hjn) v
  have hformula (y : (StateDirections W.S × ℝ) × ℝ) :
      (fun p => if inv then
        (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1) p)⁻¹
        else n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1) p) =
      (fun p => f y p * h y (g y p)) :=
    funext (fun p => n04PositiveGeometry_sourceHeight_factorization W X i side m hm
      (liftSectorParameter W.S W.C y.1) inv p)
  let Q' := Q.congr (fun y _ => congrArg
    (fun F : PolarPoint → ℝ => radialBoundaryJet F r n y.2) (hformula y))
  have hF (j : ℕ) (hj : j ≤ n) : N04BoundaryWordBounds (JF j hj) K s d z θ P M H t shift := by
    have h := (hR j hj (JR j hj)).fixedEvaluation (fun _ => ((1 : ℝ), (0 : ℝ)))
      (fun _ => by simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one])
    exact h.congr hz (fun y hy => by
      simpa only [n04PositiveGeometry_referenceHeightPowerJet, hidx, hrad] using
        (n06_radialBoundaryJet_eq_frechet j (hf y hy)).symm)
  have hout := hbound hU r f h g hf hh hg JF JH JG Q' K s d hNorder z hz θ P
    M H t hM hH hHM hHL ht shift hF (fun j hj => hCj j hj (JH j hj))
    (fun j hj hjn v hv => (hS j hj hjn (JS j hj hjn)).fixedEvaluation v hv)
  exact hout.congr hz (fun y _ => congrArg
    (fun F : PolarPoint → ℝ => radialBoundaryJet F r n y.2) (hformula y).symm)

end ContinuousFlexibility.Analysis
