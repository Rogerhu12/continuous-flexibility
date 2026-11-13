import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedFormula

/-!
# The surviving original-state blocks in an inverse partition

The state output of a fiber-preserving map is affine. Hence a selected
state block is zero except for one original state slot. Every remaining
block is precisely the actual spatial-output derivative of the inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open scoped Topology ContDiff BigOperators

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem projectedGraph_state_one
    {g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    (b : Fin 1 → Bool) (v : Fin 1 → P × V) :
    n04PositiveGeometry_slotProjection true
      (n04PositiveGeometry_projectedJet b (n04PositiveGeometry_fiberLift g) x v) =
      if b 0 then ((v 0).1, 0) else 0 := by
  rw [n04PositiveGeometry_projectedJet_apply, iteratedFDeriv_one_apply,
    n04PositiveGeometry_fiberLift_fderiv hg]
  cases hb : b 0 <;>
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      n04PositiveGeometry_slotProjection_apply, hb, Bool.false_eq_true,
      if_false, if_true]

/-- At every positive order, the selected state graph jet has norm at
most one. This bound is independent of all inverse derivatives. -/
theorem n04PositiveGeometry_projectedGraph_state_norm_le
    {g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (hn : 0 < n) (b : Fin n → Bool) :
    ‖(n04PositiveGeometry_slotProjection true).compContinuousMultilinearMap
      (n04PositiveGeometry_projectedJet b (n04PositiveGeometry_fiberLift g) x)‖ ≤ 1 := by
  by_cases hn1 : n = 1
  · subst n
    apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
    intro v
    change ‖n04PositiveGeometry_slotProjection true
      (n04PositiveGeometry_projectedJet b (n04PositiveGeometry_fiberLift g) x v)‖ ≤ _
    rw [projectedGraph_state_one hg, one_mul, Fin.prod_univ_one]
    cases hb : b 0
    · simp only [hb, Bool.false_eq_true, if_false, norm_zero]
      exact norm_nonneg _
    · simp only [hb, if_true, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      exact norm_fst_le _
  · have hn2 : 2 ≤ n := by omega
    have he : (n04PositiveGeometry_slotProjection true).compContinuousMultilinearMap
        (n04PositiveGeometry_projectedJet b (n04PositiveGeometry_fiberLift g) x) = 0 := by
      ext v
      change n04PositiveGeometry_slotProjection true
        (n04PositiveGeometry_projectedJet b (n04PositiveGeometry_fiberLift g) x v) = 0
      rw [n04PositiveGeometry_projectedJet_apply, n04PositiveGeometry_fiberLift_jet hg hn2]
      rfl
    rw [he, norm_zero]
    exact zero_le_one

/-- A nonzero selected state block contains exactly one original state
slot and no original spatial slot. -/
theorem n04PositiveGeometry_projectedGraph_state_eq_zero
    {g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n)
    (hbad : ¬ (w.stateArity = 1 ∧ w.angleArity = 0)) :
    (n04PositiveGeometry_slotProjection true).compContinuousMultilinearMap
      (n04PositiveGeometry_projectedJet w.isState (n04PositiveGeometry_fiberLift g) x) = 0 := by
  by_cases hn1 : n = 1
  · subst n
    cases w with
    | state w =>
        cases w
        exact (hbad ⟨rfl, rfl⟩).elim
    | angle w =>
        cases w
        ext v
        change n04PositiveGeometry_slotProjection true
          (n04PositiveGeometry_projectedJet (StateAngleWord.angle .nil).isState
            (n04PositiveGeometry_fiberLift g) x v) = 0
        rw [projectedGraph_state_one hg]
        rfl
  · have hn2 : 2 ≤ n := by omega
    ext v
    change n04PositiveGeometry_slotProjection true
      (n04PositiveGeometry_projectedJet w.isState (n04PositiveGeometry_fiberLift g) x v) = 0
    rw [n04PositiveGeometry_projectedJet_apply, n04PositiveGeometry_fiberLift_jet hg hn2]
    rfl

/-- The selected spatial graph jet is just the spatial inverse jet
inserted into the product with zero state component. -/
theorem n04PositiveGeometry_projectedGraph_space_eq
    {g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (b : Fin n → Bool) :
    (n04PositiveGeometry_slotProjection false).compContinuousMultilinearMap
      (n04PositiveGeometry_projectedJet b (n04PositiveGeometry_fiberLift g) x) =
      (ContinuousLinearMap.inr ℝ P V).compContinuousMultilinearMap
        (n04PositiveGeometry_projectedJet b g x) := by
  ext v
  change n04PositiveGeometry_slotProjection false
      (n04PositiveGeometry_projectedJet b (n04PositiveGeometry_fiberLift g) x v) =
    (0, n04PositiveGeometry_projectedJet b g x v)
  rw [n04PositiveGeometry_projectedJet_apply, n04PositiveGeometry_projectedJet_apply]
  change n04PositiveGeometry_slotProjection false
      (iteratedFDeriv ℝ n (fun q : P × V => (q.1, g q)) x _) = _
  rw [iteratedFDeriv_prodMk contDiffAt_fst hg (by simp)]
  rfl

theorem n04PositiveGeometry_projectedGraph_space_norm_le
    {g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (b : Fin n → Bool) :
    ‖(n04PositiveGeometry_slotProjection false).compContinuousMultilinearMap
      (n04PositiveGeometry_projectedJet b (n04PositiveGeometry_fiberLift g) x)‖ ≤
      ‖n04PositiveGeometry_projectedJet b g x‖ := by
  rw [n04PositiveGeometry_projectedGraph_space_eq hg]
  have hinr : ‖(ContinuousLinearMap.inr ℝ P V)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp only [ContinuousLinearMap.inr_apply, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _), one_mul, le_refl]
  exact (n04PositiveGeometry_clm_multilinear_norm_le _ _).trans
    ((mul_le_mul_of_nonneg_right hinr (norm_nonneg _)).trans_eq (one_mul _))

theorem n04PositiveGeometry_inverseSelectedBlock_state_norm_le
    {g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (b : Fin n → Bool) (c : OrderedFinpartition n)
    (s : Finset (Fin c.length)) (i : Fin c.length) (hi : i ∈ s) :
    ‖n04PositiveGeometry_inverseSelectedBlock b g x c s i‖ ≤ 1 := by
  classical
  simp only [n04PositiveGeometry_inverseSelectedBlock, hi, decide_true]
  exact n04PositiveGeometry_projectedGraph_state_norm_le hg (c.partSize_pos i) _

theorem n04PositiveGeometry_inverseSelectedBlock_space_norm_le
    {g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (b : Fin n → Bool) (c : OrderedFinpartition n)
    (s : Finset (Fin c.length)) (i : Fin c.length) (hi : i ∉ s) :
    ‖n04PositiveGeometry_inverseSelectedBlock b g x c s i‖ ≤
      ‖n04PositiveGeometry_projectedJet (b ∘ c.emb i) g x‖ := by
  classical
  simp only [n04PositiveGeometry_inverseSelectedBlock, hi, decide_false]
  exact n04PositiveGeometry_projectedGraph_space_norm_le hg _

theorem n04PositiveGeometry_inverseSelectedBlock_state_eq_zero
    {g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (w : StateAngleWord n) (c : OrderedFinpartition n)
    (s : Finset (Fin c.length)) (i : Fin c.length) (hi : i ∈ s)
    (hbad : ¬ ((w.restrict (c.emb i)).stateArity = 1 ∧
      (w.restrict (c.emb i)).angleArity = 0)) :
    n04PositiveGeometry_inverseSelectedBlock w.isState g x c s i = 0 := by
  classical
  have hb : w.isState ∘ c.emb i = (w.restrict (c.emb i)).isState := by
    funext j
    exact (StateAngleWord.isState_restrict w (c.emb i) j).symm
  simp only [n04PositiveGeometry_inverseSelectedBlock, hi, decide_true, hb]
  exact n04PositiveGeometry_projectedGraph_state_eq_zero hg (c.partSize_pos i) _ hbad

theorem n04PositiveGeometry_inverseSelectedTerm_eq_zero
    {f g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (w : StateAngleWord n) (c : OrderedFinpartition n)
    (s : Finset (Fin c.length)) (i : Fin c.length) (hi : i ∈ s)
    (hbad : ¬ ((w.restrict (c.emb i)).stateArity = 1 ∧
      (w.restrict (c.emb i)).angleArity = 0)) :
    n04PositiveGeometry_inverseSelectedTerm w.isState f g x c s = 0 := by
  have hz := n04PositiveGeometry_inverseSelectedBlock_state_eq_zero hg w c s i hi hbad
  ext v
  change (n04PositiveGeometry_projectedJet (fun j => decide (j ∈ s)) f
    (n04PositiveGeometry_fiberLift g x))
    (fun j => n04PositiveGeometry_inverseSelectedBlock w.isState g x c s j (v ∘ c.emb j)) = 0
  apply ContinuousMultilinearMap.map_coord_zero _ i
  rw [hz, ContinuousMultilinearMap.zero_apply]

theorem n04PositiveGeometry_fiberInverse_state_one
    {f g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    (hfg : n04PositiveGeometry_fiberLift f ∘ n04PositiveGeometry_fiberLift g
      =ᶠ[𝓝 x] id)
    (B : V →L[ℝ] V)
    (hB : B.comp ((fderiv ℝ f (n04PositiveGeometry_fiberLift g x)).comp
      (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V)
    (b : Fin 1 → Bool) (hb : b 0 = true) :
    n04PositiveGeometry_projectedJet b g x =
      -B.compContinuousMultilinearMap
        (n04PositiveGeometry_projectedJet b f (n04PositiveGeometry_fiberLift g x)) := by
  ext v
  simp only [ContinuousMultilinearMap.neg_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, comp_apply,
    n04PositiveGeometry_projectedJet_apply, iteratedFDeriv_one_apply]
  rw [n04PositiveGeometry_fiberInverse_firstJet hf hg hfg B hB]
  simp only [n04PositiveGeometry_slotProjection_apply, hb, if_true,
    zero_sub, map_neg]

theorem n04PositiveGeometry_fiberInverse_space_one_norm
    {f g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    (hfg : n04PositiveGeometry_fiberLift f ∘ n04PositiveGeometry_fiberLift g
      =ᶠ[𝓝 x] id)
    (B : V →L[ℝ] V)
    (hB : B.comp ((fderiv ℝ f (n04PositiveGeometry_fiberLift g x)).comp
      (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V)
    (b : Fin 1 → Bool) (hb : b 0 = false) :
    ‖n04PositiveGeometry_projectedJet b g x‖ ≤ ‖B‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg B)
  intro v
  rw [n04PositiveGeometry_projectedJet_apply, iteratedFDeriv_one_apply,
    n04PositiveGeometry_fiberInverse_firstJet hf hg hfg B hB]
  simp only [n04PositiveGeometry_slotProjection_apply, hb, Bool.false_eq_true,
    if_false, Prod.mk_zero_zero, map_zero, sub_zero, Fin.prod_univ_one]
  exact (B.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_snd_le _) (norm_nonneg B))

theorem n04PositiveGeometry_fiberInverse_state_one_norm
    {f g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    (hfg : n04PositiveGeometry_fiberLift f ∘ n04PositiveGeometry_fiberLift g
      =ᶠ[𝓝 x] id)
    (B : V →L[ℝ] V)
    (hB : B.comp ((fderiv ℝ f (n04PositiveGeometry_fiberLift g x)).comp
      (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V)
    (b : Fin 1 → Bool) (hb : b 0 = true) :
    ‖n04PositiveGeometry_projectedJet b g x‖ ≤
      ‖B‖ * ‖n04PositiveGeometry_projectedJet b f (n04PositiveGeometry_fiberLift g x)‖ := by
  rw [n04PositiveGeometry_fiberInverse_state_one hf hg hfg B hB b hb, norm_neg]
  exact n04PositiveGeometry_clm_multilinear_norm_le _ _

end ContinuousFlexibility.Analysis
