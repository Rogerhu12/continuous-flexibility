import ContinuousFlexibility.Radial.InnerMorseInnerChain
import ContinuousFlexibility.Radial.InnerModelChainGaps
import ContinuousFlexibility.Radial.InnerMorseWeights
import ContinuousFlexibility.Radial.InnerChainDiagonal

/-!
# The actual cut weights on the finite inner chain

The left tail is enumerated inward, the right tail outward. The first
inward cut on either tail has weight one. Adjacent outward and inward
cuts carry exactly the same geometric mean, including the two terminal
cap remnants. Flattening these values therefore gives one positive
physical weight which is constant on every gap.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory ContinuousFlexibility.Statements

theorem innerMorseInwardWeight_succ (N : ℕ) (a γ : ℝ) {m : ℕ} (hm : N ≤ m) :
    innerMorseInwardWeight N a γ (m + 1) = innerMorseOutwardWeight N a γ m := by
  have hne : m + 1 ≠ N := by omega
  simp only [innerMorseInwardWeight, hne, ite_false, Nat.add_sub_cancel,
    innerMorseOutwardWeight]

def innerMorseInnerModelWeight (N K : ℕ) (a γ : ℝ)
    (p : Fin (2 * K + 1)) (i : Fin 2) : ℝ :=
  if p.val < K then innerMorseCutWeight N a γ false (N + (K - 1 - p.val)) i
  else if p.val = K then 1
  else innerMorseCutWeight N a γ true (N + (p.val - K - 1)) i

def innerMorseInnerOuterWeight (N K : ℕ) (a γ : ℝ) : ℝ :=
  if K = 0 then 1 else innerMorseOutwardWeight N a γ (N + (K - 1))

def innerMorseInnerCutWeight (N K : ℕ) (a γ : ℝ) : Fin (2 * (2 * K + 1) + 2) → ℝ :=
  innerModelChainCuts (innerMorseInnerModelWeight N K a γ)
    (innerMorseInnerOuterWeight N K a γ) (innerMorseInnerOuterWeight N K a γ)

theorem innerMorseInnerModelWeight_pos (N K : ℕ) (a γ : ℝ)
    (p : Fin (2 * K + 1)) (i : Fin 2) : 0 < innerMorseInnerModelWeight N K a γ p i := by
  unfold innerMorseInnerModelWeight
  split_ifs
  · exact innerMorseCutWeight_pos N a γ false _ i
  · norm_num
  · exact innerMorseCutWeight_pos N a γ true _ i

theorem innerMorseInnerOuterWeight_pos (N K : ℕ) (a γ : ℝ) :
    0 < innerMorseInnerOuterWeight N K a γ := by
  unfold innerMorseInnerOuterWeight
  split_ifs
  · norm_num
  · exact innerGeometricMeanWeight_pos (innerCellWeight_pos N a γ _)
      (innerCellWeight_pos N a γ _)

theorem innerMorseInnerCutWeight_pos (N K : ℕ) (a γ : ℝ)
    (i : Fin (2 * (2 * K + 1) + 2)) : 0 < innerMorseInnerCutWeight N K a γ i := by
  cases i using Fin.cases with
  | zero => exact innerMorseInnerOuterWeight_pos N K a γ
  | succ i =>
    cases i using Fin.lastCases with
    | last =>
      simpa only [innerMorseInnerCutWeight, innerModelChainCuts, Fin.cons_succ,
        Fin.snoc_last] using innerMorseInnerOuterWeight_pos N K a γ
    | cast i =>
      simpa only [innerMorseInnerCutWeight, innerModelChainCuts, Fin.cons_succ,
        Fin.snoc_castSucc, innerFlattenModelCuts] using
        innerMorseInnerModelWeight_pos N K a γ
          ⟨i.val / 2, by omega⟩ ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩

theorem innerMorseInnerModelWeight_center (N K : ℕ) (a γ : ℝ) (i : Fin 2) :
    innerMorseInnerModelWeight N K a γ (innerMorseInnerCenter K) i = 1 := by
  simp only [innerMorseInnerModelWeight, innerMorseInnerCenter, lt_self_iff_false,
    ite_false, ite_true]

theorem innerMorseInnerModelWeight_tail (N K : ℕ) (a γ : ℝ)
    (side : Bool) (p : Fin K) (i : Fin 2) :
    innerMorseInnerModelWeight N K a γ (innerMorseInnerTailSlot K side p) i =
      innerMorseCutWeight N a γ side (innerMorseInnerTailIndex N K side p) i := by
  cases side with
  | false =>
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, Bool.false_eq_true,
      ite_false, innerMorseInnerModelWeight, p.isLt, ite_true]
  | true =>
    have hlt : ¬K + 1 + p.val < K := by omega
    have hne : K + 1 + p.val ≠ K := by omega
    have heq : K + 1 + p.val - K - 1 = p.val := by omega
    simp only [innerMorseInnerTailSlot, innerMorseInnerTailIndex, ite_true,
      innerMorseInnerModelWeight, hlt, hne, ite_false, heq]

/-- Every internal gap joins equal prescribed cut values. This also
covers the two transitions between the finite middle and cell N. -/
theorem innerMorseInnerModelWeight_adjacent (N K : ℕ) (a γ : ℝ) (p : Fin (2 * K)) :
    innerMorseInnerModelWeight N K a γ p.castSucc 1 =
      innerMorseInnerModelWeight N K a γ p.succ 0 := by
  by_cases hp : p.val < K
  · by_cases hq : p.val + 1 < K
    · have hi : N + (K - 1 - p.val) = N + (K - 1 - (p.val + 1)) + 1 := by omega
      simp only [innerMorseInnerModelWeight, Fin.val_castSucc, Fin.val_succ,
        hp, hq, ite_true, innerMorseCutWeight, Bool.false_eq_true, ite_false,
        show (1 : Fin 2) ≠ 0 by decide, eq_self_iff_true]
      rw [hi, innerMorseInwardWeight_succ N a γ (Nat.le_add_right _ _)]
    · have hq0 : p.val + 1 = K := by omega
      have hi : K - 1 - p.val = 0 := by omega
      simp [innerMorseInnerModelWeight, hp, hq, hq0, hi, innerMorseCutWeight,
        innerMorseInwardWeight]
  · by_cases hp0 : p.val = K
    · have hq : ¬p.val + 1 < K := by omega
      have hq0 : p.val + 1 ≠ K := by omega
      have hi : p.val + 1 - K - 1 = 0 := by omega
      simp [innerMorseInnerModelWeight, hp, hp0, hq, hq0, hi, innerMorseCutWeight,
        innerMorseInwardWeight]
    · have hq : ¬p.val + 1 < K := by omega
      have hq0 : p.val + 1 ≠ K := by omega
      have hi : N + (p.val + 1 - K - 1) = N + (p.val - K - 1) + 1 := by omega
      simp only [innerMorseInnerModelWeight, Fin.val_castSucc, Fin.val_succ,
        hp, hp0, hq, hq0, ite_false, innerMorseCutWeight, ite_true,
        show (1 : Fin 2) ≠ 0 by decide, eq_self_iff_true]
      rw [hi, innerMorseInwardWeight_succ N a γ (Nat.le_add_right _ _)]

theorem innerMorseInnerModelWeight_first (N K : ℕ) (a γ : ℝ) :
    innerMorseInnerModelWeight N K a γ 0 0 = innerMorseInnerOuterWeight N K a γ := by
  by_cases hK : K = 0
  · subst K
    simp [innerMorseInnerModelWeight, innerMorseInnerOuterWeight]
  · have hpos : 0 < K := Nat.pos_of_ne_zero hK
    simp only [innerMorseInnerModelWeight, Fin.val_zero, hpos, ite_true,
      Nat.sub_zero, innerMorseCutWeight, Bool.false_eq_true, ite_false,
      eq_self_iff_true, innerMorseInnerOuterWeight, hK]

theorem innerMorseInnerModelWeight_last (N K : ℕ) (a γ : ℝ) :
    innerMorseInnerModelWeight N K a γ (Fin.last (2 * K)) 1 =
      innerMorseInnerOuterWeight N K a γ := by
  by_cases hK : K = 0
  · subst K
    simp [innerMorseInnerModelWeight, innerMorseInnerOuterWeight]
  · have hlt : ¬2 * K < K := by omega
    have hne : 2 * K ≠ K := by omega
    have hi : 2 * K - K - 1 = K - 1 := by omega
    simp only [innerMorseInnerModelWeight, Fin.val_last, hlt, hne, ite_false,
      hi, innerMorseCutWeight, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      innerMorseInnerOuterWeight, hK]

theorem innerMorseInnerCutWeight_model_left (N K : ℕ) (a γ : ℝ)
    (p : Fin (2 * K + 1)) :
    innerMorseInnerCutWeight N K a γ (innerModelChainPiece p).castSucc =
      innerMorseInnerModelWeight N K a γ p 0 :=
  innerModelChainCuts_model_left _ _ _ p

theorem innerMorseInnerCutWeight_model_right (N K : ℕ) (a γ : ℝ)
    (p : Fin (2 * K + 1)) :
    innerMorseInnerCutWeight N K a γ (innerModelChainPiece p).succ =
      innerMorseInnerModelWeight N K a γ p 1 :=
  innerModelChainCuts_model_right _ _ _ p

theorem innerMorseInnerCutWeight_gap (N K : ℕ) (a γ : ℝ) (g : Fin (2 * K + 2)) :
    innerMorseInnerCutWeight N K a γ (innerModelChainGap g).castSucc =
      innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ := by
  unfold innerMorseInnerCutWeight
  rw [innerModelChainCuts_gap_left, innerModelChainCuts_gap_right]
  by_cases hg : 0 < g.val
  · rw [dif_pos hg]
    by_cases hlast : g.val < 2 * K + 1
    · rw [dif_pos hlast]
      have hprev : g.val - 1 < 2 * K := by omega
      have he := innerMorseInnerModelWeight_adjacent N K a γ ⟨g.val - 1, hprev⟩
      have hsucc : (⟨g.val - 1, hprev⟩ : Fin (2 * K)).succ = ⟨g.val, hlast⟩ := by
        apply Fin.ext
        simp only [Fin.val_succ] <;> omega
      rw [hsucc] at he
      exact he
    · rw [dif_neg hlast]
      have he : (⟨g.val - 1, by omega⟩ : Fin (2 * K + 1)) = Fin.last (2 * K) := by
        apply Fin.ext
        simp only [Fin.val_last] <;> omega
      rw [he]
      exact innerMorseInnerModelWeight_last N K a γ
  · have hzero : g.val = 0 := by omega
    have hlt : g.val < 2 * K + 1 := by omega
    rw [dif_neg hg, dif_pos hlt]
    have he : (⟨g.val, hlt⟩ : Fin (2 * K + 1)) = 0 := Fin.ext hzero
    rw [he]
    exact (innerMorseInnerModelWeight_first N K a γ).symm

/-- Only the internal cuts carry interface variables. The endpoint
weights above remain useful for interpolation on the terminal caps. -/
def innerMorseInnerInterfaceWeight (N K : ℕ) (a γ : ℝ) : Fin (2 * (2 * K + 1)) → ℝ :=
  fun i => innerMorseInnerCutWeight N K a γ i.castSucc.succ

theorem innerMorseInnerInterfaceWeight_pos (N K : ℕ) (a γ : ℝ)
    (i : Fin (2 * (2 * K + 1))) : 0 < innerMorseInnerInterfaceWeight N K a γ i :=
  innerMorseInnerCutWeight_pos N K a γ _

theorem innerChainScalarRestriction_full_left (n : ℕ) (p : Fin (n + 1))
    (w : Fin (n + 2) → ℝ) (hp : 0 < p.val) :
    innerChainScalarRestriction n p (fun i => w i.castSucc.succ) 1 0 = w p.castSucc := by
  rw [innerChainScalarRestriction, if_pos rfl, dif_pos hp]
  apply congrArg w
  apply Fin.ext
  simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

theorem innerChainScalarRestriction_full_right (n : ℕ) (p : Fin (n + 1))
    (w : Fin (n + 2) → ℝ) (hp : p.val < n) :
    innerChainScalarRestriction n p (fun i => w i.castSucc.succ) 1 1 = w p.succ := by
  rw [innerChainScalarRestriction, if_neg (by decide : (1 : Fin 2) ≠ 0), dif_pos hp]

theorem innerMorseInnerInterfaceWeight_model (N K : ℕ) (a γ : ℝ)
    (p : Fin (2 * K + 1)) (i : Fin 2) :
    innerChainScalarRestriction (2 * (2 * K + 1)) (innerModelChainPiece p)
      (innerMorseInnerInterfaceWeight N K a γ) 1 i = innerMorseInnerModelWeight N K a γ p i := by
  have hl : 0 < (innerModelChainPiece p).val := by
    simp only [innerModelChainPiece] <;> omega
  have hr : (innerModelChainPiece p).val < 2 * (2 * K + 1) := by
    simp only [innerModelChainPiece] <;> omega
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · rw [innerMorseInnerInterfaceWeight, innerChainScalarRestriction_full_left _ _ _ hl]
    exact innerMorseInnerCutWeight_model_left N K a γ p
  · rw [innerMorseInnerInterfaceWeight, innerChainScalarRestriction_full_right _ _ _ hr]
    exact innerMorseInnerCutWeight_model_right N K a γ p

/-- Closed model intervals see the same interpolation at their left
cut, which belongs to the preceding half-open gap in the partition. -/
theorem innerChainWeight_on_closed_internal_piece {D : ReferenceData} {n : ℕ}
    (G : InnerRadialChainGeometry D n) (l r : Fin (n + 1) → ℝ)
    (w : Fin (n + 2) → ℝ) (hw : ∀ i, 0 < w i)
    (hlr : ∀ p, l p < r p) (hr : ∀ p, r p ≤ G.right p)
    (p : Fin (n + 1)) (hp : 0 < p.val) (hl : G.left p ≤ l p)
    {x : ℝ} (hx : x ∈ Icc (G.left p) (G.right p)) :
    innerChainWeight G l r w x =
      innerInterpolatedWeight (l p) (r p) (w p.castSucc) (w p.succ) x := by
  by_cases he : x = G.left p
  · subst x
    let previous : Fin (n + 1) := ⟨p.val - 1, by omega⟩
    have hi : previous.succ = p.castSucc := by
      apply Fin.ext
      simp only [previous, Fin.val_succ, Fin.val_castSucc] <;> omega
    have hc : G.right previous = G.left p := congrArg G.cuts hi
    calc
      innerChainWeight G l r w (G.left p) = w previous.succ := by
        rw [← hc]
        exact innerChainWeight_right_cut G l r w hw hlr hr previous
      _ = w p.castSucc := congrArg w hi
      _ = innerInterpolatedWeight (l p) (r p) (w p.castSucc) (w p.succ) (G.left p) :=
        (innerInterpolatedWeight_eqOn_buffer (hlr p) (hw _) (hw _) false hl).symm
  · exact innerChainWeight_on_piece G l r w p
      ⟨lt_of_le_of_ne hx.1 (Ne.symm he), hx.2⟩

section PhysicalWeight

variable {D : ReferenceData} (N K : ℕ) (a γ : ℝ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)

def innerMorseInnerWeight : ℝ → ℝ :=
  innerChainWeight G l r (innerMorseInnerCutWeight N K a γ)

theorem innerMorseInnerWeight_pos (x : ℝ) : 0 < innerMorseInnerWeight N K a γ G l r x :=
  innerChainWeight_pos G l r _ x

theorem innerMorseInnerWeight_measurable : Measurable (innerMorseInnerWeight N K a γ G l r) :=
  innerChainWeight_measurable G l r _

theorem innerMorseInnerWeight_finite_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, |innerMorseInnerWeight N K a γ G l r x| ≤ C ∧
      |(innerMorseInnerWeight N K a γ G l r x)⁻¹| ≤ C :=
  innerChainWeight_finite_bounds G l r _ (innerMorseInnerCutWeight_pos N K a γ)

theorem innerMorseInnerWeight_on_model (p : Fin (2 * K + 1)) {x : ℝ}
    (hx : x ∈ Ioc (G.left (innerModelChainPiece p)) (G.right (innerModelChainPiece p))) :
    innerMorseInnerWeight N K a γ G l r x =
      innerInterpolatedWeight (l (innerModelChainPiece p)) (r (innerModelChainPiece p))
        (innerMorseInnerModelWeight N K a γ p 0) (innerMorseInnerModelWeight N K a γ p 1) x := by
  rw [innerMorseInnerWeight, innerChainWeight_on_piece G l r _ _ hx,
    innerMorseInnerCutWeight_model_left, innerMorseInnerCutWeight_model_right]

theorem innerMorseInnerWeight_on_center {x : ℝ}
    (hx : x ∈ Ioc (G.left (innerModelChainPiece (innerMorseInnerCenter K)))
      (G.right (innerModelChainPiece (innerMorseInnerCenter K)))) :
    innerMorseInnerWeight N K a γ G l r x = 1 := by
  rw [innerMorseInnerWeight_on_model N K a γ G l r _ hx,
    innerMorseInnerModelWeight_center, innerMorseInnerModelWeight_center]
  exact innerInterpolatedWeight_same _ _ zero_lt_one x

theorem innerMorseInnerWeight_on_gap (g : Fin (2 * K + 2)) {x : ℝ}
    (hx : x ∈ Ioc (G.left (innerModelChainGap g)) (G.right (innerModelChainGap g))) :
    innerMorseInnerWeight N K a γ G l r x =
      innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ :=
  innerChainWeight_constant_piece G l r _ (innerMorseInnerCutWeight_pos N K a γ)
    _ (innerMorseInnerCutWeight_gap N K a γ g) hx

theorem innerMorseInnerWeight_at_interface
    (hlr : ∀ p, l p < r p) (hr : ∀ p, r p ≤ G.right p)
    (i : Fin (2 * (2 * K + 1))) :
    innerMorseInnerWeight N K a γ G l r (G.cuts i.castSucc.succ) =
      innerMorseInnerInterfaceWeight N K a γ i :=
  innerChainWeight_right_cut G l r _ (innerMorseInnerCutWeight_pos N K a γ)
    hlr hr i.castSucc

theorem innerMorseInnerWeight_on_closed_model
    (hlr : ∀ p, l p < r p) (hr : ∀ p, r p ≤ G.right p)
    (p : Fin (2 * K + 1)) (hl : G.left (innerModelChainPiece p) ≤ l (innerModelChainPiece p))
    {x : ℝ} (hx : x ∈ Icc (G.left (innerModelChainPiece p)) (G.right (innerModelChainPiece p))) :
    innerMorseInnerWeight N K a γ G l r x =
      innerInterpolatedWeight (l (innerModelChainPiece p)) (r (innerModelChainPiece p))
        (innerMorseInnerModelWeight N K a γ p 0) (innerMorseInnerModelWeight N K a γ p 1) x := by
  have hp : 0 < (innerModelChainPiece p).val := by
    simp only [innerModelChainPiece] <;> omega
  rw [innerMorseInnerWeight, innerChainWeight_on_closed_internal_piece G l r _
    (innerMorseInnerCutWeight_pos N K a γ) hlr hr _ hp hl hx,
    innerMorseInnerCutWeight_model_left, innerMorseInnerCutWeight_model_right]

theorem innerMorseInnerWeight_on_closed_center
    (hlr : ∀ p, l p < r p) (hr : ∀ p, r p ≤ G.right p)
    (hl : G.left (innerModelChainPiece (innerMorseInnerCenter K)) ≤
      l (innerModelChainPiece (innerMorseInnerCenter K))) {x : ℝ}
    (hx : x ∈ Icc (G.left (innerModelChainPiece (innerMorseInnerCenter K)))
      (G.right (innerModelChainPiece (innerMorseInnerCenter K)))) :
    innerMorseInnerWeight N K a γ G l r x = 1 := by
  rw [innerMorseInnerWeight_on_closed_model N K a γ G l r hlr hr _ hl hx,
    innerMorseInnerModelWeight_center, innerMorseInnerModelWeight_center]
  exact innerInterpolatedWeight_same _ _ zero_lt_one x

end PhysicalWeight

end ContinuousFlexibility.Radial
