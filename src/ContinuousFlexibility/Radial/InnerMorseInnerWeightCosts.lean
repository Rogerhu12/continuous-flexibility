import ContinuousFlexibility.Radial.InnerMorseInnerWeights
import ContinuousFlexibility.Radial.InnerActualModelChain

/-!
# Fixed coefficient loss for the actual finite-chain weight

Each model is assigned its original cell index. A gap uses the larger
of its neighboring retained cell indices, with the terminal index at an
outer cap and N on the finite middle. Both signs of the actual physical
weight have the same square-root coefficient comparison on every
piece. The output loss is a positive measurable contraction and has
the exact prescribed coefficient value on each piece.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory ContinuousFlexibility.Statements

def innerMorseInnerModelIndex (N K : ℕ) (p : Fin (2 * K + 1)) : ℕ :=
  if p.val < K then N + (K - 1 - p.val)
  else if p.val = K then N else N + (p.val - K - 1)

def innerMorseInnerGapIndex (N K : ℕ) (g : Fin (2 * K + 2)) : ℕ :=
  N + min (K - 1) (if g.val ≤ K then K - g.val else g.val - K - 1)

def innerMorseInnerPieceIndex (N K : ℕ) : Fin (2 * (2 * K + 1) + 1) → ℕ :=
  innerDisjointCoverElim innerModelChainPiece innerModelChainGap
    innerModelChainPiece_injective innerModelChainGap_injective
    (fun p g => (innerModelChainGap_ne_model g p).symm) innerModelChainPiece_or_gap
    (innerMorseInnerModelIndex N K) (innerMorseInnerGapIndex N K)

theorem innerMorseInnerPieceIndex_model (N K : ℕ) (p : Fin (2 * K + 1)) :
    innerMorseInnerPieceIndex N K (innerModelChainPiece p) = innerMorseInnerModelIndex N K p :=
  innerDisjointCoverElim_left innerModelChainPiece innerModelChainGap
    innerModelChainPiece_injective innerModelChainGap_injective
    (fun p g => (innerModelChainGap_ne_model g p).symm) innerModelChainPiece_or_gap
    (innerMorseInnerModelIndex N K) (innerMorseInnerGapIndex N K) p

theorem innerMorseInnerPieceIndex_gap (N K : ℕ) (g : Fin (2 * K + 2)) :
    innerMorseInnerPieceIndex N K (innerModelChainGap g) = innerMorseInnerGapIndex N K g :=
  innerDisjointCoverElim_right innerModelChainPiece innerModelChainGap
    innerModelChainPiece_injective innerModelChainGap_injective
    (fun p g => (innerModelChainGap_ne_model g p).symm) innerModelChainPiece_or_gap
    (innerMorseInnerModelIndex N K) (innerMorseInnerGapIndex N K) g

theorem innerMorseInnerModelIndex_center (N K : ℕ) :
    innerMorseInnerModelIndex N K (innerMorseInnerCenter K) = N := by
  simp only [innerMorseInnerModelIndex, innerMorseInnerCenter, lt_self_iff_false,
    ite_false, ite_true]

theorem innerMorseInnerModelIndex_tail (N K : ℕ) (side : Bool) (p : Fin K) :
    innerMorseInnerModelIndex N K (innerMorseInnerTailSlot K side p) =
      innerMorseInnerTailIndex N K side p := by
  cases side with
  | false =>
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, Bool.false_eq_true,
      ite_false, innerMorseInnerModelIndex, p.isLt, ite_true]
  | true =>
    have hlt : ¬K + 1 + p.val < K := by omega
    have hne : K + 1 + p.val ≠ K := by omega
    have heq : K + 1 + p.val - K - 1 = p.val := by omega
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, ite_true,
      innerMorseInnerModelIndex, hlt, hne, ite_false, heq]

theorem innerMorseInnerModelIndex_bounds (N K : ℕ) (p : Fin (2 * K + 1)) :
    N ≤ innerMorseInnerModelIndex N K p ∧ innerMorseInnerModelIndex N K p ≤ N + K := by
  unfold innerMorseInnerModelIndex
  split_ifs <;> omega

theorem innerMorseInnerGapIndex_bounds (N K : ℕ) (g : Fin (2 * K + 2)) :
    N ≤ innerMorseInnerGapIndex N K g ∧ innerMorseInnerGapIndex N K g ≤ N + K := by
  have hm := min_le_left (K - 1) (if g.val ≤ K then K - g.val else g.val - K - 1)
  unfold innerMorseInnerGapIndex
  omega

theorem innerMorseInnerPieceIndex_bounds (N K : ℕ) (p : Fin (2 * (2 * K + 1) + 1)) :
    N ≤ innerMorseInnerPieceIndex N K p ∧ innerMorseInnerPieceIndex N K p ≤ N + K := by
  rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
  · rw [innerMorseInnerPieceIndex_model]
    exact innerMorseInnerModelIndex_bounds N K q
  · rw [innerMorseInnerPieceIndex_gap]
    exact innerMorseInnerGapIndex_bounds N K g

/-- A piece's normalization removes its possibly large absolute weight.
Only its comparison with the local coefficient enters operator bounds. -/
def innerMorseInnerPieceBase (N K : ℕ) (a γ σ : ℝ) : Fin (2 * (2 * K + 1) + 1) → ℝ :=
  innerDisjointCoverElim innerModelChainPiece innerModelChainGap
    innerModelChainPiece_injective innerModelChainGap_injective
    (fun p g => (innerModelChainGap_ne_model g p).symm) innerModelChainPiece_or_gap
    (fun p => (innerCellWeight N a γ (innerMorseInnerModelIndex N K p)) ^ σ)
    (fun g => (innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ) ^ σ)

theorem innerMorseInnerPieceBase_model (N K : ℕ) (a γ σ : ℝ) (p : Fin (2 * K + 1)) :
    innerMorseInnerPieceBase N K a γ σ (innerModelChainPiece p) =
      (innerCellWeight N a γ (innerMorseInnerModelIndex N K p)) ^ σ :=
  innerDisjointCoverElim_left innerModelChainPiece innerModelChainGap
    innerModelChainPiece_injective innerModelChainGap_injective
    (fun p g => (innerModelChainGap_ne_model g p).symm) innerModelChainPiece_or_gap
    (fun p => (innerCellWeight N a γ (innerMorseInnerModelIndex N K p)) ^ σ)
    (fun g => (innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ) ^ σ) p

theorem innerMorseInnerPieceBase_gap (N K : ℕ) (a γ σ : ℝ) (g : Fin (2 * K + 2)) :
    innerMorseInnerPieceBase N K a γ σ (innerModelChainGap g) =
      (innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ) ^ σ :=
  innerDisjointCoverElim_right innerModelChainPiece innerModelChainGap
    innerModelChainPiece_injective innerModelChainGap_injective
    (fun p g => (innerModelChainGap_ne_model g p).symm) innerModelChainPiece_or_gap
    (fun p => (innerCellWeight N a γ (innerMorseInnerModelIndex N K p)) ^ σ)
    (fun g => (innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ) ^ σ) g

theorem innerMorseInnerPieceBase_pos (N K : ℕ) (a γ σ : ℝ)
    (p : Fin (2 * (2 * K + 1) + 1)) : 0 < innerMorseInnerPieceBase N K a γ σ p := by
  rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
  · rw [innerMorseInnerPieceBase_model]
    exact rpow_pos_of_pos (innerCellWeight_pos N a γ _) σ
  · rw [innerMorseInnerPieceBase_gap]
    exact rpow_pos_of_pos (innerMorseInnerCutWeight_pos N K a γ _) σ

theorem innerMorseInnerPieceBase_center (N K : ℕ) (a γ σ : ℝ) :
    innerMorseInnerPieceBase N K a γ σ (innerModelChainPiece (innerMorseInnerCenter K)) = 1 := by
  rw [innerMorseInnerPieceBase_model, innerMorseInnerModelIndex_center,
    innerCellWeight_base, one_rpow]

theorem inner_radialE_sqrt_ge_one (m : ℕ) : 1 ≤ sqrt (radialE m) := by
  simpa only [sqrt_one, radialE] using sqrt_le_sqrt (one_le_exp_iff.mpr (radialQ_nonneg m))

section ActualWeight

variable {D : ReferenceData} (N K : ℕ) {a γ σ : ℝ}
  (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
  (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ))
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)

include ha hγ hσ hN hNa

theorem innerMorseInnerWeight_model_ratios (p : Fin (2 * K + 1)) {x : ℝ}
    (hx : x ∈ Ioo (G.left (innerModelChainPiece p)) (G.right (innerModelChainPiece p))) :
    (innerMorseInnerWeight N K a γ G l r x) ^ σ /
        (innerCellWeight N a γ (innerMorseInnerModelIndex N K p)) ^ σ ≤
      sqrt (radialE (innerMorseInnerModelIndex N K p)) ∧
    (innerCellWeight N a γ (innerMorseInnerModelIndex N K p)) ^ σ /
        (innerMorseInnerWeight N K a γ G l r x) ^ σ ≤
      sqrt (radialE (innerMorseInnerModelIndex N K p)) := by
  rw [innerMorseInnerWeight_on_model N K a γ G l r p ⟨hx.1, hx.2.le⟩]
  by_cases hp : p.val < K
  · simpa only [innerMorseInnerModelWeight, innerMorseInnerModelIndex, hp, ite_true,
      innerMorseInterpolatedWeight] using
      innerMorseInterpolatedWeight_cell_ratios N ha hγ hσ hN hNa
        (Nat.le_add_right N (K - 1 - p.val)) false
        (l (innerModelChainPiece p)) (r (innerModelChainPiece p)) x
  · by_cases hp0 : p.val = K
    · simp only [innerMorseInnerModelWeight, innerMorseInnerModelIndex, hp, hp0,
        ite_false, ite_true, innerInterpolatedWeight_same _ _ zero_lt_one,
        innerCellWeight_base, one_rpow, div_one]
      exact ⟨inner_radialE_sqrt_ge_one N, inner_radialE_sqrt_ge_one N⟩
    · simpa only [innerMorseInnerModelWeight, innerMorseInnerModelIndex, hp, hp0,
        ite_false, innerMorseInterpolatedWeight] using
        innerMorseInterpolatedWeight_cell_ratios N ha hγ hσ hN hNa
          (Nat.le_add_right N (p.val - K - 1)) true
          (l (innerModelChainPiece p)) (r (innerModelChainPiece p)) x

theorem innerMorseInnerWeight_piece_ratios (p : Fin (2 * (2 * K + 1) + 1)) {x : ℝ}
    (hx : x ∈ Ioo (G.left p) (G.right p)) :
    (innerMorseInnerWeight N K a γ G l r x) ^ σ / innerMorseInnerPieceBase N K a γ σ p ≤
      sqrt (radialE (innerMorseInnerPieceIndex N K p)) ∧
    innerMorseInnerPieceBase N K a γ σ p / (innerMorseInnerWeight N K a γ G l r x) ^ σ ≤
      sqrt (radialE (innerMorseInnerPieceIndex N K p)) := by
  rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
  · rw [innerMorseInnerPieceIndex_model, innerMorseInnerPieceBase_model]
    exact innerMorseInnerWeight_model_ratios N K ha hγ hσ hN hNa G l r q hx
  · rw [innerMorseInnerPieceIndex_gap, innerMorseInnerPieceBase_gap,
      innerMorseInnerWeight_on_gap N K a γ G l r g ⟨hx.1, hx.2.le⟩,
      div_self (rpow_pos_of_pos (innerMorseInnerCutWeight_pos N K a γ _) σ).ne']
    exact ⟨inner_radialE_sqrt_ge_one _, inner_radialE_sqrt_ge_one _⟩

/-- These are the two actual multiplier inequalities used by the
Dirichlet sum. The local constants are independent of the number of
cells, the sign, and the absolute size of the weight. -/
theorem innerMorseInnerWeight_piece_bounds (p : Fin (2 * (2 * K + 1) + 1)) {x : ℝ}
    (hx : x ∈ Ioo (G.left p) (G.right p)) :
    |(innerMorseInnerWeight N K a γ G l r x) ^ σ| ≤
      sqrt (radialE (innerMorseInnerPieceIndex N K p)) * innerMorseInnerPieceBase N K a γ σ p ∧
    |((innerMorseInnerWeight N K a γ G l r x) ^ σ)⁻¹| ≤
      sqrt (radialE (innerMorseInnerPieceIndex N K p)) / innerMorseInnerPieceBase N K a γ σ p := by
  have hu := rpow_pos_of_pos (innerMorseInnerWeight_pos N K a γ G l r x) σ
  have hb := innerMorseInnerPieceBase_pos N K a γ σ p
  have h := innerMorseInnerWeight_piece_ratios N K ha hγ hσ hN hNa G l r p hx
  rw [abs_of_pos hu, abs_of_pos (inv_pos.mpr hu)]
  refine ⟨(div_le_iff₀ hb).mp h.1, ?_⟩
  apply (le_div_iff₀ hb).mpr
  simpa only [div_eq_mul_inv, mul_comm] using h.2

end ActualWeight

section CoefficientLoss

variable {D : ReferenceData} (N K : ℕ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))

def innerMorseInnerLoss (ℓ : ℝ) : ℝ → ℝ :=
  innerPiecewiseCoefficientLoss (innerChainWeightPiece G) (innerMorseInnerPieceIndex N K) N ℓ

/-- The coefficient function extends the original cell values to gaps
by the adjacent retained index and has the middle value elsewhere. -/
def innerMorseInnerCoefficient : ℝ → ℝ :=
  fun x => radialE N * innerPiecewiseWeight (innerChainWeightPiece G)
    (fun p _ => radialE (innerMorseInnerPieceIndex N K p) / radialE N) x

theorem innerMorseInnerCoefficient_on_piece (p : Fin (2 * (2 * K + 1) + 1))
    {x : ℝ} (hx : x ∈ innerChainWeightPiece G p) :
    innerMorseInnerCoefficient N K G x = radialE (innerMorseInnerPieceIndex N K p) := by
  rw [innerMorseInnerCoefficient,
    innerPiecewiseWeight_on_piece _ (innerChainWeightPieces_disjoint G) _ hx]
  exact mul_div_cancel₀ _ (exp_pos (radialQ N)).ne'

theorem innerMorseInnerLoss_eq_coefficient (ℓ x : ℝ) :
    innerMorseInnerLoss N K G ℓ x = (innerMorseInnerCoefficient N K G x / radialE N) ^ (-ℓ) := by
  by_cases hx : x ∈ ⋃ p, innerChainWeightPiece G p
  · obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    rw [innerMorseInnerCoefficient_on_piece N K G p hp]
    exact innerPiecewiseWeight_on_piece _ (innerChainWeightPieces_disjoint G) _ hp
  · rw [innerMorseInnerLoss, innerPiecewiseCoefficientLoss,
      innerPiecewiseWeight_outside _ _ hx, innerMorseInnerCoefficient,
      innerPiecewiseWeight_outside _ _ hx, mul_one,
      div_self (exp_pos (radialQ N)).ne', one_rpow]

theorem innerMorseInnerLoss_measurable (ℓ : ℝ) : Measurable (innerMorseInnerLoss N K G ℓ) :=
  innerPiecewiseCoefficientLoss_measurable _ (fun _ => measurableSet_Ioc) _ N ℓ

theorem innerMorseInnerLoss_pos (ℓ x : ℝ) : 0 < innerMorseInnerLoss N K G ℓ x :=
  innerPiecewiseCoefficientLoss_pos _ (innerChainWeightPieces_disjoint G) _ N ℓ x

theorem innerMorseInnerLoss_le_one {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (x : ℝ) :
    |innerMorseInnerLoss N K G ℓ x| ≤ 1 :=
  innerPiecewiseCoefficientLoss_le_one _ (innerChainWeightPieces_disjoint G) _ hℓ
    (fun p => (innerMorseInnerPieceIndex_bounds N K p).1) x

theorem innerMorseInnerLoss_on_piece (ℓ : ℝ) (p : Fin (2 * (2 * K + 1) + 1))
    {x : ℝ} (hx : x ∈ Ioo (G.left p) (G.right p)) :
    innerMorseInnerLoss N K G ℓ x = innerCoefficientLoss N ℓ (innerMorseInnerPieceIndex N K p) :=
  innerPiecewiseWeight_on_piece _ (innerChainWeightPieces_disjoint G) _ ⟨hx.1, hx.2.le⟩

/-- The localized output weight has exactly the cell loss used in the
Dirichlet estimate. Its extra factor is an actual global contraction. -/
theorem innerMorseInnerWeight_localized_piece_bound {a γ σ ℓ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ))
    (l r : Fin (2 * (2 * K + 1) + 1) → ℝ) (p : Fin (2 * (2 * K + 1) + 1))
    {x : ℝ} (hx : x ∈ Ioo (G.left p) (G.right p)) :
    |innerMorseInnerLoss N K G ℓ x * (innerMorseInnerWeight N K a γ G l r x) ^ σ| ≤
      innerCoefficientLoss N ℓ (innerMorseInnerPieceIndex N K p) *
        sqrt (radialE (innerMorseInnerPieceIndex N K p)) * innerMorseInnerPieceBase N K a γ σ p := by
  rw [abs_mul, abs_of_pos (innerMorseInnerLoss_pos N K G ℓ x),
    innerMorseInnerLoss_on_piece N K G ℓ p hx, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (innerMorseInnerWeight_piece_bounds N K ha hγ hσ hN hNa G l r p hx).1
    (innerCoefficientLoss_pos N ℓ _).le

end CoefficientLoss

end ContinuousFlexibility.Radial
