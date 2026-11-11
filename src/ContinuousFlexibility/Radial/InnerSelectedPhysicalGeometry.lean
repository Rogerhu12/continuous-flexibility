import ContinuousFlexibility.Radial.InnerMorseAllBandsGeometry
import ContinuousFlexibility.Radial.InnerRadialGapChartConstruction
import ContinuousFlexibility.Radial.CentralRadius

/-!
# The original selected tails in one physical reference

The selected tail family is kept on its original reference. Each side is
then placed in the final reference by its own positive radius and height
scales. The first inner boundary is the selected first join itself; later
boundaries are the actual outer endpoints of the preceding retained cell.

Only raw profile identities, ordering and positivity of the two fixed
middle connectors are inputs. Finite chains and quantitative gap bounds
are constructed from these data in the subsequent modules.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- Every retained cell stays on its original side of the first entry.
The index orientation changes with the side; physical radius is increasing
on both model charts. -/
theorem innerMorseRetained_entry_bound
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (side : Bool) {m : ℕ} (hm : T.index ≤ m) :
    ∀ x ∈ Icc (T.leftX side m) (T.rightX side m),
      if side then T.radius side T.index (T.leftX side T.index) ≤ T.radius side m x
      else T.radius side m x ≤ T.radius side T.index (T.rightX side T.index) := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro x hx
    have hd := h.retained_data side T.index le_rfl
    have hab := (hd.2.2.2.1.trans hd.2.2.2.2.1).le
    have hmono := (h.radius_strictMonoOn side T.index le_rfl).monotoneOn
    cases side with
    | false => exact hmono hx (right_mem_Icc.mpr hab) hx.2
    | true => exact hmono (left_mem_Icc.mpr hab) hx hx.1
  | succ m hm ih =>
    intro x hx
    have hm1 : T.index ≤ m + 1 := hm.trans (Nat.le_succ m)
    have hd := h.retained_data side m hm
    have hd1 := h.retained_data side (m + 1) hm1
    have hab := (hd.2.2.2.1.trans hd.2.2.2.2.1).le
    have hab1 := (hd1.2.2.2.1.trans hd1.2.2.2.2.1).le
    have hj := h.join_data side m hm
    have hmono := (h.radius_strictMonoOn side (m + 1) hm1).monotoneOn
    cases side with
    | false =>
      have hp := ih (T.leftX false m) (left_mem_Icc.mpr hab)
      simp only [Bool.false_eq_true, ite_false] at hp hj ⊢
      have hstep : T.radius false (m + 1) (T.rightX false (m + 1)) <
          T.radius false m (T.leftX false m) := by
        calc
          _ = T.joinLeft false m := hj.2.1.symm
          _ < T.joinRight false m := hj.1
          _ = _ := hj.2.2.1
      exact (hmono hx (right_mem_Icc.mpr hab1) hx.2).trans (hstep.le.trans hp)
    | true =>
      have hp := ih (T.rightX true m) (right_mem_Icc.mpr hab)
      simp only [ite_true] at hp hj ⊢
      have hstep : T.radius true m (T.rightX true m) <
          T.radius true (m + 1) (T.leftX true (m + 1)) := by
        calc
          _ = T.joinLeft true m := hj.2.1.symm
          _ < T.joinRight true m := hj.1
          _ = _ := hj.2.2.1
      exact hp.trans (hstep.le.trans (hmono (left_mem_Icc.mpr hab1) hx hx.1))

/-- Raw section-six geometry from one selected tail construction.
The two scaling factors are independent on the two sides. -/
structure InnerSelectedPhysicalGeometry (S : SelectedTailData)
    (D : ReferenceData) (X₀ : ℝ) where
  selected : IsSelectedTail S
  geometry : RadialProfileGeometry D
  index_ge : 10 ≤ S.chain.index
  cut_pos : 0 < X₀
  radiusScale : Bool → ℝ
  heightScale : Bool → ℝ
  radiusScale_pos : ∀ side, 0 < radiusScale side
  heightScale_pos : ∀ side, 0 < heightScale side
  left_endpoint : D.a = radiusScale false * (S.family S.sigma).a
  right_endpoint : D.b = radiusScale true * (S.family S.sigma).b
  firstJoin_entry : ∀ side,
    S.entry side S.chain.index = S.chain.radius side S.chain.index
      (if side then S.chain.leftX side S.chain.index
       else S.chain.rightX side S.chain.index) ∧
    (if side then S.joinInner side S.chain.index < S.entry side S.chain.index
     else S.entry side S.chain.index < S.joinInner side S.chain.index)
  center_left : radiusScale false * S.joinInner false S.chain.index < centralRadius (-X₀)
  center_right : centralRadius X₀ < radiusScale true * S.joinInner true S.chain.index
  profile_tail : ∀ side r,
    r ∈ radialTailInterval (S.family S.sigma) side (S.joinInner side S.chain.index) →
    D.w (radiusScale side * r) = heightScale side * radiusScale side * (S.family S.sigma).w r
  laterJoin : ∀ side K, 0 < K →
    S.joinInner side (S.chain.index + K) =
      innerMorseInnerOuterPoint S.chain S.chain.index K side
  centralHeight : ℝ
  centralHeight_pos : 0 < centralHeight
  central_profile : ∀ x ∈ Icc (-X₀) X₀,
    D.w (centralRadius x) = centralHeight * centralDensityRoot x ^ 2 * deriv centralRadius x
  middle_deriv_pos : ∀ (side : Bool) r,
    r ∈ Icc
      (if side then centralRadius X₀ else
        radiusScale false * innerMorseChainCut S.chain false S.chain.index 1)
      (if side then radiusScale true * innerMorseChainCut S.chain true S.chain.index 0
       else centralRadius (-X₀)) →
    0 < deriv D.w r

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

include P

theorem realization :
    MorseChainRealization S.chain S.sigma (S.family S.sigma) S.constants :=
  (P.selected.2.2.2.1 S.sigma P.selected.2.2.1).1

theorem center_order : centralRadius (-X₀) < centralRadius X₀ := by
  apply strictMono_centralRadius
  linarith only [P.cut_pos]

/-- The entire original retained cell is in the same selected outer
interval, including its endpoints. -/
theorem retained_in_tail (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m)
    {x : ℝ} (hx : x ∈ Icc (S.chain.leftX side m) (S.chain.rightX side m)) :
    S.chain.radius side m x ∈
      radialTailInterval (S.family S.sigma) side (S.joinInner side S.chain.index) := by
  have hc := P.realization.radius_mem_core side m hm x hx
  have hb := innerMorseRetained_entry_bound P.realization side hm x hx
  obtain ⟨he, hj⟩ := P.firstJoin_entry side
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at he hj hb
    rw [he] at hj
    exact ⟨hc.1, hb.trans_lt hj⟩
  | true =>
    simp only [ite_true] at he hj hb
    rw [he] at hj
    exact ⟨hj.trans_le hb, hc.2⟩

theorem retained_profile (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m)
    {x : ℝ} (hx : x ∈ Icc (S.chain.leftX side m) (S.chain.rightX side m)) :
    D.w (P.radiusScale side * S.chain.radius side m x) =
      P.heightScale side * P.radiusScale side * (S.family S.sigma).w (S.chain.radius side m x) :=
  P.profile_tail side _ (P.retained_in_tail side hm hx)

theorem retained_core (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m)
    {x : ℝ} (hx : x ∈ Icc (S.chain.leftX side m) (S.chain.rightX side m)) :
    P.radiusScale side * S.chain.radius side m x ∈ radialCore D := by
  apply innerRadialProfile_positive_mem_core P.geometry
  rw [P.retained_profile side hm hx]
  exact mul_pos (mul_pos (P.heightScale_pos side) (P.radiusScale_pos side))
    (P.realization.geometry.2.2.2.2.1 _
      (P.realization.radius_mem_core side m hm x hx))

theorem buffer_subset_retained (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m) :
    Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA S.chain m) (morseChainB S.chain m)) ⊆
      Icc (S.chain.leftX side m) (S.chain.rightX side m) := by
  have hd := P.realization.retained_data side m hm
  have ho := innerMorseBuffer_cut_order hd.1 hd.2.1
  obtain ⟨hl, hr⟩ := innerMorseChain_retained_endpoints P.realization side hm
  intro x hx
  rw [hl, hr]
  exact ⟨ho.1.le.trans hx.1, hx.2.trans ho.2.2.le⟩

/-- The actual scaled profile identity on the full closed cut model.
It is independent of a frequency, finite truncation or selected inverse. -/
theorem tail_profile (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m)
    {x : ℝ} (hx : x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA S.chain m) (morseChainB S.chain m))) :
    D.w (P.radiusScale side * S.chain.radius side m x) =
      P.heightScale side * P.radiusScale side * (S.family S.sigma).w (S.chain.radius side m x) :=
  P.retained_profile side hm (P.buffer_subset_retained side hm hx)

theorem tail_cut_core (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m) (i : Fin 2) :
    P.radiusScale side * innerMorseChainCut S.chain side m i ∈ radialCore D := by
  have hd := P.realization.retained_data side m hm
  have ho := innerMorseBuffer_cut_order hd.1 hd.2.1
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · rw [innerMorseChainCut_zero]
    exact P.retained_core side hm (P.buffer_subset_retained side hm
      (left_mem_Icc.mpr ho.2.1.le))
  · rw [innerMorseChainCut_one]
    exact P.retained_core side hm (P.buffer_subset_retained side hm
      (right_mem_Icc.mpr ho.2.1.le))

theorem central_core {x : ℝ} (hx : x ∈ Icc (-X₀) X₀) :
    centralRadius x ∈ radialCore D := by
  apply innerRadialProfile_positive_mem_core P.geometry
  rw [P.central_profile x hx]
  exact mul_pos (mul_pos P.centralHeight_pos (sq_pos_of_pos (centralDensityRoot_pos x)))
    (deriv_centralRadius_pos x)

theorem firstJoin_cut (side : Bool) :
    if side then P.radiusScale side * S.joinInner side S.chain.index <
        P.radiusScale side * innerMorseChainCut S.chain side S.chain.index 0
    else P.radiusScale side * innerMorseChainCut S.chain side S.chain.index 1 <
        P.radiusScale side * S.joinInner side S.chain.index := by
  have hc := innerMorseChainCut_geometry P.realization side (m := S.chain.index) le_rfl
  obtain ⟨he, hj⟩ := P.firstJoin_entry side
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at he hj ⊢
    rw [he] at hj
    exact mul_lt_mul_of_pos_left (hc.2.2.1.trans hj) (P.radiusScale_pos false)
  | true =>
    simp only [ite_true] at he hj ⊢
    rw [he] at hj
    exact mul_lt_mul_of_pos_left (hj.trans hc.1) (P.radiusScale_pos true)

def middleLeft (side : Bool) : ℝ :=
  if side then centralRadius X₀ else
    P.radiusScale false * innerMorseChainCut S.chain false S.chain.index 1

def middleRight (side : Bool) : ℝ :=
  if side then P.radiusScale true * innerMorseChainCut S.chain true S.chain.index 0
  else centralRadius (-X₀)

theorem middle_order (side : Bool) : P.middleLeft side < P.middleRight side := by
  have hj := P.firstJoin_cut side
  cases side with
  | false => exact hj.trans P.center_left
  | true => exact P.center_right.trans hj

theorem firstJoin_core (side : Bool) :
    P.radiusScale side * S.joinInner side S.chain.index ∈ radialCore D := by
  have hj := P.firstJoin_cut side
  cases side with
  | false =>
    have hc := P.central_core (x := -X₀) (by constructor <;> linarith only [P.cut_pos])
    exact ⟨(P.tail_cut_core false le_rfl 1).1.trans hj, P.center_left.trans hc.2⟩
  | true =>
    have hc := P.central_core (x := X₀) (by constructor <;> linarith only [P.cut_pos])
    exact ⟨hc.1.trans P.center_right, hj.trans (P.tail_cut_core true le_rfl 0).2⟩

theorem middle_core (side : Bool) :
    Icc (P.middleLeft side) (P.middleRight side) ⊆ radialCore D := by
  intro r hr
  cases side with
  | false =>
    have hc := P.central_core (x := -X₀) (by constructor <;> linarith only [P.cut_pos])
    exact ⟨(P.tail_cut_core false le_rfl 1).1.trans_le hr.1, hr.2.trans_lt hc.2⟩
  | true =>
    have hc := P.central_core (x := X₀) (by constructor <;> linarith only [P.cut_pos])
    exact ⟨hc.1.trans_le hr.1, hr.2.trans_lt (P.tail_cut_core true le_rfl 0).2⟩

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
