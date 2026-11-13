import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaWordBounds
import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations

/-!
# Fixed-state boundary fields

Fixing the state is a continuous linear restriction of the original
joint tower. Every word containing a state slot then vanishes. Bounds
at the fixed state and unit sampling radius therefore give all state
orders, with any later parameter shift and the same angular reserve.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E} {f : E × ℝ → F}

def n04PositiveGeometry_fixedStateLinear : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (0 : (E × ℝ) →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E ℝ)

theorem n04PositiveGeometry_fixedStateLinear_apply (y : E × ℝ) :
    n04PositiveGeometry_fixedStateLinear y = (0, y.2) := by
  simp only [n04PositiveGeometry_fixedStateLinear, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_snd']

def n04PositiveGeometry_fixedState_joint
    (J : SmoothDirections (U ×ˢ univ) f) (h0 : (0 : E) ∈ U) :
    SmoothDirections (U ×ˢ univ) (fun y => f (0, y.2)) := by
  let L : (E × ℝ) →L[ℝ] (E × ℝ) := n04PositiveGeometry_fixedStateLinear
  have hmap : MapsTo L (U ×ˢ (univ : Set ℝ)) (U ×ˢ (univ : Set ℝ)) := by
    intro y _
    rw [n04PositiveGeometry_fixedStateLinear_apply]
    exact ⟨h0, mem_univ _⟩
  exact (J.compLinear L J.open_domain hmap).congrOn
    (fun y _ => congrArg f (n04PositiveGeometry_fixedStateLinear_apply y))

theorem n04PositiveGeometry_fixedState_joint_apply
    (J : SmoothDirections (U ×ˢ univ) f) (h0 : (0 : E) ∈ U)
    (Q : SmoothDirections (U ×ˢ univ) (fun y => f (0, y.2)))
    {x : E} (hx : x ∈ U) (θ : ℝ) (n : ℕ) (v : Fin n → E × ℝ) :
    Q.D n (x, θ) v = J.D n (0, θ) (fun i => (0, (v i).2)) := by
  have he := congrArg (fun A : (E × ℝ) [×n]→L[ℝ] F => A v)
    (Q.unique (n04PositiveGeometry_fixedState_joint J h0) n (x, θ) ⟨hx, mem_univ _⟩)
  simpa only [n04PositiveGeometry_fixedState_joint, SmoothDirections.congrOn,
    SmoothDirections.compLinear, SmoothDirections.compAffine_apply, zero_add,
    n04PositiveGeometry_fixedStateLinear_apply] using he

theorem n04PositiveGeometry_fixedState_stateWord_zero
    (J : SmoothDirections (U ×ˢ univ) f) (h0 : (0 : E) ∈ U)
    (Q : SmoothDirections (U ×ˢ univ) (fun y => f (0, y.2)))
    {x : E} (hx : x ∈ U) (θ : ℝ) {n : ℕ} (w : StateAngleWord n)
    (hw : 0 < w.stateArity) (v : Fin n → E × ℝ)
    (hv : ∀ i, w.isState i = true → (v i).2 = 0) : Q.D n (x, θ) v = 0 := by
  classical
  have hex : ∃ i, w.isState i = true := by
    by_contra h
    have hs : (∑ i : Fin n, if w.isState i then (1 : ℕ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi
      · exact False.elim (h ⟨i, hi⟩)
      · rfl
    rw [← w.stateArity_eq_sum] at hs
    omega
  obtain ⟨i, hi⟩ := hex
  exact (n04PositiveGeometry_fixedState_joint_apply J h0 Q hx θ n v).trans
    ((J.D n (0, θ)).map_coord_zero i (Prod.ext rfl (hv i hi)))

theorem N04BoundaryWordBounds.fixedState
    {J : SmoothDirections (U ×ˢ univ) f}
    {s d c : ℕ} {θ M H : ℝ} {P₀ : E → Prop}
    (h : N04BoundaryWordBounds J 0 s d 0 θ P₀ M H 1 c)
    (h0 : (0 : E) ∈ U) (hP₀ : P₀ 0)
    (Q : SmoothDirections (U ×ˢ univ) (fun y => f (0, y.2)))
    {x : E} (hx : x ∈ U) (hM : 0 ≤ M) (hH : 0 ≤ H)
    {t : ℝ} (ht : 1 ≤ t) (K shift : ℕ) (P : E → Prop) :
    N04BoundaryWordBounds Q K s d x θ P M H t shift := by
  intro n w _ ha v hv _
  by_cases hw : w.stateArity = 0
  · have hpure : w.IsPure (fun i => ((0 : E), (v i).2)) := by
      refine ⟨hv.1, fun i hi => ?_⟩
      exact Prod.ext rfl (congrArg Prod.snd (hv.2 i hi))
    have hb := h n w (by omega) ha (fun i => ((0 : E), (v i).2)) hpure (fun _ => hP₀)
    have hb' : ‖J.D n (0, θ) (fun i => ((0 : E), (v i).2))‖ ≤
        M * parameterHeightWeight H w.stateArity := by
      simpa only [one_pow, mul_one] using hb
    exact (congrArg norm
      (n04PositiveGeometry_fixedState_joint_apply J h0 Q hx θ n v)).trans_le
        (hb'.trans (le_mul_of_one_le_right
          (mul_nonneg hM (parameterHeightWeight_nonneg hH _)) (one_le_pow₀ ht)))
  · have he := n04PositiveGeometry_fixedState_stateWord_zero J h0 Q hx θ w
      (Nat.pos_of_ne_zero hw) v hv.1
    exact (congrArg norm he).trans_le (by
      simpa only [norm_zero] using mul_nonneg
        (mul_nonneg hM (parameterHeightWeight_nonneg hH w.stateArity))
        (pow_nonneg (zero_le_one.trans ht) ((w.angleArity - d) + shift * w.stateArity)))

end ContinuousFlexibility.Analysis
