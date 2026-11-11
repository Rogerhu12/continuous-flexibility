import ContinuousFlexibility.Analysis.IntervalSobolevExtension
import ContinuousFlexibility.Analysis.SeeleyNaturality

/-!
# The interval extension preserves closed linear relations

Only values in the original interval are assumed to satisfy the relation.
Each endpoint cutoff vanishes before leaving that interval, so arbitrary values
of the chosen representatives outside the domain play no role.  The two
reflected pieces preserve the relation, as does their sum.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

variable {ι F G : Type*} [Countable ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A common cutoff transports a relation from the interval to the half-line;
outside the interval both cut-off values are zero. -/
theorem intervalCutoff_mem_linearRelation (P : Submodule ℝ (F × G))
    {L c : ℝ} (hc : c < L) (χ : ℝ → ℝ)
    (hzero : ∀ y, c ≤ y → χ y = 0) {u : ℝ → F} {v : ℝ → G}
    (hrel : ∀ y ∈ Icc 0 L, (u y, v y) ∈ P) {x : ℝ} (hx : 0 ≤ x) :
    (χ x • u x, χ x • v x) ∈ P := by
  by_cases hxL : x ≤ L
  · simpa only [Prod.smul_mk] using P.smul_mem (χ x) (hrel x ⟨hx, hxL⟩)
  · rw [hzero x (hc.le.trans (lt_of_not_ge hxL).le), zero_smul, zero_smul]
    exact P.zero_mem

/-- The actual interval extension preserves any closed linear relation, with
the relation required only on the original closed interval. -/
theorem intervalSeeleyCoreExtension_mem_closedLinearRelation
    (S : SeeleyData ι) (L : ℝ) (hL : 0 < L)
    (P : Submodule ℝ (F × G)) (hP : IsClosed (P : Set (F × G)))
    (u : IntervalSobolevCore F L hL) (v : IntervalSobolevCore G L hL)
    (hrel : ∀ y ∈ Icc 0 L, (u y, v y) ∈ P) (x : ℝ) :
    (intervalSeeleyCoreExtension S L hL u x,
      intervalSeeleyCoreExtension S L hL v x) ∈ P := by
  have hleft : ∀ y, 0 ≤ y →
      (intervalLeftCutoffCore L hL u y, intervalLeftCutoffCore L hL v y) ∈ P := by
    intro y hy
    rw [intervalLeftCutoffCore_apply, intervalLeftCutoffCore_apply]
    exact intervalCutoff_mem_linearRelation P (show 2 * L / 3 < L by linarith)
      (intervalSobolevCutoff L hL) (fun z hz ↦ intervalSobolevCutoff_zero L hL hz) hrel hy
  have hreflect : ∀ y ∈ Icc 0 L,
      (intervalSobolevReflect L hL u y, intervalSobolevReflect L hL v y) ∈ P := by
    intro y hy
    rw [intervalSobolevReflect_apply, intervalSobolevReflect_apply]
    exact hrel (L - y) ⟨sub_nonneg.mpr hy.2, sub_le_self _ hy.1⟩
  have hright : ∀ y, 0 ≤ y →
      (intervalRightCutoffCore L hL (intervalSobolevReflect L hL u) y,
        intervalRightCutoffCore L hL (intervalSobolevReflect L hL v) y) ∈ P := by
    intro y hy
    rw [intervalRightCutoffCore_apply, intervalRightCutoffCore_apply]
    exact intervalCutoff_mem_linearRelation P (show 2 * L / 3 < L by linarith)
      (intervalSobolevRightCutoff L hL)
      (fun z hz ↦ intervalSobolevRightCutoff_zero L hL hz) hreflect hy
  have hl := seeleyExtend_mem_closedLinearRelation S P hP
    (HalfLineSobolevCore.bounded (intervalLeftCutoffCore L hL u))
    (HalfLineSobolevCore.bounded (intervalLeftCutoffCore L hL v)) hleft x
  have hr := seeleyExtend_mem_closedLinearRelation S P hP
    (HalfLineSobolevCore.bounded
      (intervalRightCutoffCore L hL (intervalSobolevReflect L hL u)))
    (HalfLineSobolevCore.bounded
      (intervalRightCutoffCore L hL (intervalSobolevReflect L hL v))) hright (L - x)
  simpa only [intervalSeeleyCoreExtension, LinearMap.add_apply, LinearMap.comp_apply,
    Submodule.coe_add, Pi.add_apply, lineSobolevReflect_apply,
    seeleySobolevCoreExtension_coe, Prod.mk_add_mk] using P.add_mem hl hr

end ContinuousFlexibility.Analysis
