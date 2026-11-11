import ContinuousFlexibility.Radial.TailEdgePerturbedGreen

/-!
# Pointwise bounds for the perturbed Green and Poisson functions

The three-point kernel comparison makes the interval between the
unperturbed solution and its scaled majorant invariant under the actual
integral iteration. The bounds pass to its fixed point.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology

/-- A nonnegative unperturbed function satisfying the kernel comparison
gives both pointwise bounds for the corresponding perturbed solution. -/
theorem exists_tailEdgeGreen_solution_with_bounds {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ t, 0 ≤ q t) (hδ : tailEdgeDiagonalSize hab q < 1)
    (base : TailEdgeContinuous a b) (hb : ∀ s, 0 ≤ base s)
    (hcomp : ∀ s t : Icc a b,
      tailEdgeGreen a b s t * base t ≤ base s * tailEdgeGreen a b t t) :
    ∃ u : TailEdgeContinuous a b, u = base + tailEdgeGreenAction hab q u ∧
      ∀ s, base s ≤ u s ∧ u s ≤ base s / (1 - tailEdgeDiagonalSize hab q) := by
  let δ := tailEdgeDiagonalSize hab q
  have hδ₀ : 0 ≤ δ := by
    apply intervalIntegral.integral_nonneg hab.le
    intro t ht
    rw [IccExtend_of_mem hab.le q ht]
    exact mul_nonneg (tailEdgeGreen_nonneg hab ht ht) (hq ⟨t, ht⟩)
  have hd : 0 < 1 - δ := sub_pos.mpr hδ
  let F : TailEdgeContinuous a b → TailEdgeContinuous a b := fun v =>
    base + tailEdgeGreenAction hab q v
  have hF := tailEdgeGreenStep_contracting hab hq hδ base
  let u := ContractingWith.fixedPoint F hF
  have hfix : F u = u := hF.fixedPoint_isFixedPt
  have hstep (v : TailEdgeContinuous a b)
      (hv : ∀ s, base s ≤ v s ∧ v s ≤ base s / (1 - δ)) (s : Icc a b) :
      base s ≤ F v s ∧ F v s ≤ base s / (1 - δ) := by
    let g : ℝ → ℝ := fun t =>
      tailEdgeGreen a b s t * IccExtend hab.le (q * v) t
    let w : ℝ → ℝ := fun t => tailEdgeGreen a b t t * IccExtend hab.le q t
    have happly : F v s = base s + ∫ t in a..b, g t := by
      change base s + tailEdgeGreenAction hab q v s = _
      rw [tailEdgeGreenAction_apply]
    have hpos : 0 ≤ ∫ t in a..b, g t := by
      apply intervalIntegral.integral_nonneg hab.le
      intro t ht
      dsimp only [g]
      rw [IccExtend_of_mem hab.le (q * v) ht, ContinuousMap.mul_apply]
      exact mul_nonneg (tailEdgeGreen_nonneg hab s.property ht)
        (mul_nonneg (hq ⟨t, ht⟩) ((hb ⟨t, ht⟩).trans (hv ⟨t, ht⟩).1))
    have hG : Continuous (tailEdgeGreen a b s) := by
      unfold tailEdgeGreen
      exact (((continuous_const.min continuous_id).sub continuous_const).mul
        (continuous_const.sub (continuous_const.max continuous_id))).div_const _
    have hdiag : Continuous (fun t => tailEdgeGreen a b t t) := by
      simp only [tailEdgeGreen_self]
      exact (((continuous_id.sub continuous_const).mul
        (continuous_const.sub continuous_id)).div_const _)
    have hg : Continuous g := hG.mul (q * v).continuous.Icc_extend'
    have hw : Continuous w := hdiag.mul q.continuous.Icc_extend'
    have hle : (∫ t in a..b, g t) ≤
        ∫ t in a..b, (base s / (1 - δ)) * w t := by
      apply intervalIntegral.integral_mono_on hab.le (hg.intervalIntegrable a b)
        ((continuous_const.mul hw).intervalIntegrable a b)
      intro t ht
      change tailEdgeGreen a b s t * IccExtend hab.le (q * v) t ≤
        (base s / (1 - δ)) * (tailEdgeGreen a b t t * IccExtend hab.le q t)
      rw [IccExtend_of_mem hab.le (q * v) ht, IccExtend_of_mem hab.le q ht, ContinuousMap.mul_apply]
      let z : Icc a b := ⟨t, ht⟩
      have hkn := tailEdgeGreen_nonneg hab s.property ht
      calc
        _ = (tailEdgeGreen a b s t * v z) * q z := by ring
        _ ≤ (tailEdgeGreen a b s t * (base z / (1 - δ))) * q z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv z).2 hkn) (hq z)
        _ = (tailEdgeGreen a b s t * base z) / (1 - δ) * q z := by ring
        _ ≤ (base s * tailEdgeGreen a b t t) / (1 - δ) * q z :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hcomp s z) hd.le) (hq z)
        _ = _ := by ring
    rw [intervalIntegral.integral_const_mul] at hle
    change (∫ t in a..b, g t) ≤ base s / (1 - δ) * δ at hle
    rw [happly]
    refine ⟨le_add_of_nonneg_right hpos, (add_le_add le_rfl hle).trans_eq ?_⟩
    field_simp [hd.ne']
    ring
  have hiter (n : ℕ) (s : Icc a b) :
      base s ≤ F^[n] base s ∧ F^[n] base s ≤ base s / (1 - δ) := by
    induction n generalizing s with
    | zero =>
      refine ⟨le_rfl, (le_div_iff₀ hd).mpr ?_⟩
      exact mul_le_of_le_one_right (hb s) (by linarith only [hδ₀])
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ ih s
  refine ⟨u, hfix.symm, fun s => ?_⟩
  have hconv : Tendsto (fun n => F^[n] base s) atTop (𝓝 (u s)) :=
    (continuous_eval_const s).continuousAt.tendsto.comp (hF.tendsto_iterate_fixedPoint base)
  exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hconv (fun n => (hiter n s).1),
    le_of_tendsto' hconv (fun n => (hiter n s).2)⟩

/-- Every actual Green column satisfies (G_0le G_qle G_0/(1-delta)). -/
theorem exists_tailEdgeGreen_column {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ s, 0 ≤ q s) (hδ : tailEdgeDiagonalSize hab q < 1)
    (t : Icc a b) :
    ∃ G : TailEdgeContinuous a b,
      (∀ s : Icc a b, G s = tailEdgeGreen a b s t + tailEdgeGreenAction hab q G s) ∧
      ∀ s : Icc a b, tailEdgeGreen a b s t ≤ G s ∧
        G s ≤ tailEdgeGreen a b s t / (1 - tailEdgeDiagonalSize hab q) := by
  have hc : Continuous (fun s : ℝ => tailEdgeGreen a b s t) := by
    unfold tailEdgeGreen
    exact (((continuous_id.min continuous_const).sub continuous_const).mul
      (continuous_const.sub (continuous_id.max continuous_const))).div_const _
  let base : TailEdgeContinuous a b :=
    ⟨fun s => tailEdgeGreen a b s t, hc.comp continuous_subtype_val⟩
  obtain ⟨G, hG, hbound⟩ := exists_tailEdgeGreen_solution_with_bounds hab hq hδ base
    (fun s => tailEdgeGreen_nonneg hab s.property t.property) (fun s z =>
      tailEdgeGreen_threePoint hab s.property z.property t.property)
  exact ⟨G, fun s => congrArg (fun v : TailEdgeContinuous a b => v s) hG, hbound⟩

/-- Both perturbed endpoint height functions satisfy the corresponding
linear-height comparison on the same physical edge. -/
theorem exists_tailEdgePoisson_height {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ s, 0 ≤ q s) (hδ : tailEdgeDiagonalSize hab q < 1)
    (right : Bool) :
    let l : ℝ → ℝ := if right then tailEdgeRightHeight a b else tailEdgeLeftHeight a b
    ∃ v : TailEdgeContinuous a b,
      (∀ s : Icc a b, v s = l s + tailEdgeGreenAction hab q v s) ∧
      ∀ s : Icc a b, l s ≤ v s ∧ v s ≤ l s / (1 - tailEdgeDiagonalSize hab q) := by
  dsimp only
  let l : ℝ → ℝ := if right then tailEdgeRightHeight a b else tailEdgeLeftHeight a b
  have hc : Continuous l := by
    cases right
    · change Continuous (fun s : ℝ => (b - s) / (b - a))
      exact (continuous_const.sub continuous_id).div_const _
    · change Continuous (fun s : ℝ => (s - a) / (b - a))
      exact (continuous_id.sub continuous_const).div_const _
  let base : TailEdgeContinuous a b := ⟨fun s => l s, hc.comp continuous_subtype_val⟩
  have hn (s : Icc a b) : 0 ≤ base s := by
    cases right
    · exact div_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr hab.le)
    · exact div_nonneg (sub_nonneg.mpr s.property.1) (sub_nonneg.mpr hab.le)
  have hcomp (s t : Icc a b) :
      tailEdgeGreen a b s t * base t ≤ base s * tailEdgeGreen a b t t := by
    cases right
    · exact tailEdgeGreen_leftHeight hab s.property t.property
    · exact tailEdgeGreen_rightHeight hab s.property t.property
  obtain ⟨v, hv, hbound⟩ := exists_tailEdgeGreen_solution_with_bounds hab hq hδ base hn hcomp
  exact ⟨v, fun s => congrArg (fun u : TailEdgeContinuous a b => u s) hv, hbound⟩

end ContinuousFlexibility.Radial
