module

public import ContinuousFlexibility.Radial.InnerPiecewiseWeights
public import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph

/-!
# One positive weight on the actual finite radial chain

The physical intervals use a half-open partition, so a cut has its
prescribed value as a pointwise function as well as an L² multiplier.
Interpolation is confined between the two buffer walls of each piece.
Equal endpoint weights give an exactly constant gap, including both
endpoints. The finite middle part is the special case with both values one.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory ContinuousFlexibility.Statements
open scoped BigOperators

variable {D : ReferenceData} {n : ℕ} (G : InnerRadialChainGeometry D n)

def innerChainWeightPiece (p : Fin (n + 1)) : Set ℝ := Ioc (G.left p) (G.right p)

theorem innerChainWeightPieces_disjoint :
    Pairwise (fun p q => Disjoint (innerChainWeightPiece G p) (innerChainWeightPiece G q)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  change G.left p < x ∧ x ≤ G.right p at hxp
  change G.left q < x ∧ x ≤ G.right q at hxq
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · have hidx : p.succ ≤ q.castSucc := by
      change p.val + 1 ≤ q.val
      exact Nat.succ_le_of_lt hlt
    have horder : G.right p ≤ G.left q := G.increasing.monotone hidx
    exact (not_lt_of_ge (hxp.2.trans horder)) hxq.1
  · have hidx : q.succ ≤ p.castSucc := by
      change q.val + 1 ≤ p.val
      exact Nat.succ_le_of_lt hgt
    have horder : G.right q ≤ G.left p := G.increasing.monotone hidx
    exact (not_lt_of_ge (hxq.2.trans horder)) hxp.1

def innerChainWeight (l r : Fin (n + 1) → ℝ) (w : Fin (n + 2) → ℝ) : ℝ → ℝ :=
  innerPiecewiseWeight (innerChainWeightPiece G) (fun p =>
    innerInterpolatedWeight (l p) (r p) (w p.castSucc) (w p.succ))

theorem innerChainWeight_on_piece (l r : Fin (n + 1) → ℝ)
    (w : Fin (n + 2) → ℝ) (p : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioc (G.left p) (G.right p)) :
    innerChainWeight G l r w x =
      innerInterpolatedWeight (l p) (r p) (w p.castSucc) (w p.succ) x :=
  innerPiecewiseWeight_on_piece _ (innerChainWeightPieces_disjoint G) _ hx

theorem innerChainWeight_measurable (l r : Fin (n + 1) → ℝ)
    (w : Fin (n + 2) → ℝ) : Measurable (innerChainWeight G l r w) :=
  innerPiecewiseWeight_measurable _ (fun _ => measurableSet_Ioc) _
    (fun p => (innerInterpolatedWeight_contDiff (l p) (r p)
      (w p.castSucc) (w p.succ)).continuous.measurable)

theorem innerChainWeight_pos (l r : Fin (n + 1) → ℝ)
    (w : Fin (n + 2) → ℝ) (x : ℝ) : 0 < innerChainWeight G l r w x :=
  innerPiecewiseWeight_pos _ (innerChainWeightPieces_disjoint G) _
    (fun p x _ => innerInterpolatedWeight_pos _ _ _ _ x) x

/-- A cut is assigned the same value which is seen on either neighboring
buffer. In particular the interface weight is this actual point value. -/
theorem innerChainWeight_right_cut (l r : Fin (n + 1) → ℝ)
    (w : Fin (n + 2) → ℝ) (hw : ∀ k, 0 < w k)
    (hlr : ∀ p, l p < r p) (hr : ∀ p, r p ≤ G.right p) (p : Fin (n + 1)) :
    innerChainWeight G l r w (G.right p) = w p.succ := by
  rw [innerChainWeight_on_piece G l r w p ⟨G.left_lt_right p, le_rfl⟩]
  exact innerInterpolatedWeight_eqOn_buffer (hlr p) (hw _) (hw _) true (hr p)

theorem innerChainWeight_buffer (l r : Fin (n + 1) → ℝ)
    (w : Fin (n + 2) → ℝ) (hw : ∀ k, 0 < w k)
    (hlr : ∀ p, l p < r p) (p : Fin (n + 1)) (side : Bool) {x : ℝ}
    (hpiece : x ∈ Ioc (G.left p) (G.right p))
    (hbuffer : x ∈ if side then Ici (r p) else Iic (l p)) :
    innerChainWeight G l r w x = if side then w p.succ else w p.castSucc := by
  rw [innerChainWeight_on_piece G l r w p hpiece]
  exact innerInterpolatedWeight_eqOn_buffer (hlr p) (hw _) (hw _) side hbuffer

theorem innerInterpolatedWeight_same (l r : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ) :
    innerInterpolatedWeight l r w w x = w := by
  unfold innerInterpolatedWeight
  rw [show (1 - innerWeightTransition l r x) * log w +
    innerWeightTransition l r x * log w = log w by ring, exp_log hw]

/-- The full gap weight is constant, independently of its length. -/
theorem innerChainWeight_constant_piece (l r : Fin (n + 1) → ℝ)
    (w : Fin (n + 2) → ℝ) (hw : ∀ k, 0 < w k)
    (p : Fin (n + 1)) (hgap : w p.castSucc = w p.succ) {x : ℝ}
    (hx : x ∈ Ioc (G.left p) (G.right p)) :
    innerChainWeight G l r w x = w p.succ := by
  rw [innerChainWeight_on_piece G l r w p hx, hgap]
  exact innerInterpolatedWeight_same _ _ (hw _) _

/-- Both actual multiplier signs are bounded for each finite chain.
These finite bounds are used only to define the operators; estimates
use local ratios instead. -/
theorem innerChainWeight_finite_bounds (l r : Fin (n + 1) → ℝ)
    (w : Fin (n + 2) → ℝ) (hw : ∀ k, 0 < w k) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, |innerChainWeight G l r w x| ≤ C ∧
      |(innerChainWeight G l r w x)⁻¹| ≤ C := by
  obtain ⟨C, hC, hb⟩ := innerInterpolatedWeight_finite_bounds l r
    (fun p => w p.castSucc) (fun p => w p.succ) (fun p => hw _) (fun p => hw _)
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro x
  constructor
  · exact innerPiecewiseWeight_bound _ (innerChainWeightPieces_disjoint G) _
      (le_max_right _ _) (fun p y _ => ((hb p y).1.trans (le_max_left _ _))) x
  · exact innerPiecewiseWeight_inv_bound _ (innerChainWeightPieces_disjoint G) _
      (le_max_right _ _) (fun p y _ => ((hb p y).2.trans (le_max_left _ _))) x

/-- Restricting the global function to a physical open piece gives the
same interpolation used for its local norm bound. -/
theorem innerChainWeight_local_ratio (l r : Fin (n + 1) → ℝ)
    (w : Fin (n + 2) → ℝ) (p : Fin (n + 1)) {base R : ℝ}
    (hlocal : ∀ x, |innerInterpolatedWeight (l p) (r p)
      (w p.castSucc) (w p.succ) x| ≤ R * base) :
    ∀ x ∈ Ioo (G.left p) (G.right p), |innerChainWeight G l r w x| ≤ R * base := by
  intro x hx
  rw [innerChainWeight_on_piece G l r w p ⟨hx.1, hx.2.le⟩]
  exact hlocal x

end ContinuousFlexibility.Radial
