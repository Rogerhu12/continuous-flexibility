import ContinuousFlexibility.Radial.TailActualSolutionNodes
import ContinuousFlexibility.Radial.TailMassCells
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The actual state and mass integrals of a natural solution

The frozen natural equation supplies a continuous value and physical flux
up to the regular entrance. Its square integrability also makes the
disjoint physical mass-cell integrals summable, before any estimate of
the point values at the nodes is available.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem tailNaturalEquation_continuousOn {T : DeepTailData} {u : ℝ → ℝ}
    (hu : TailNaturalEquation T u) : ContinuousOn u (Ico T.entrance T.endpoint) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxeq | hxgt
  · subst x
    exact hu.1.continuousAt.continuousWithinAt
  · exact (hu.2.1.contDiffAt (isOpen_Ioo.mem_nhds ⟨hxgt, hx.2⟩)).continuousAt.continuousWithinAt

theorem tailNaturalEquation_deriv_continuousOn {T : DeepTailData} {u : ℝ → ℝ}
    (hu : TailNaturalEquation T u) : ContinuousOn (deriv u) (Ico T.entrance T.endpoint) := by
  have hd : ContDiffOn ℝ ∞ (deriv u) (Ioo T.entrance T.endpoint) :=
    hu.2.1.deriv_of_isOpen isOpen_Ioo (by simp)
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxeq | hxgt
  · subst x
    exact (hu.1.derivWithin (m := ∞) (by simp)).continuousAt.continuousWithinAt
  · exact (hd.contDiffAt (isOpen_Ioo.mem_nhds ⟨hxgt, hx.2⟩)).continuousAt.continuousWithinAt

theorem tailNaturalEquation_flux_continuousOn {T : DeepTailData}
    (hT : DeepTailHypotheses T) {u : ℝ → ℝ} (hu : TailNaturalEquation T u) :
    ContinuousOn (fun x => T.p x * deriv u x) (Ico T.entrance T.endpoint) :=
  (deepTail_contDiffOn hT).continuousOn.mul (tailNaturalEquation_deriv_continuousOn hu)

/-- The physical flux in the frozen second-order equation satisfies the actual first-order system. -/
theorem tailNaturalEquation_system {T : DeepTailData}
    (hT : DeepTailHypotheses T) {u : ℝ → ℝ} (hu : TailNaturalEquation T u) :
    TailFirstOrderSystem T.p T.Λ u (fun x => T.p x * deriv u x)
      (Ioo T.entrance T.endpoint) := by
  have hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint) :=
    (deepTail_contDiffOn hT).mono (fun _ hx => ⟨hx.1.le, hx.2⟩)
  have hd : ContDiffOn ℝ ∞ (deriv u) (Ioo T.entrance T.endpoint) :=
    hu.2.1.deriv_of_isOpen isOpen_Ioo (by simp)
  intro x hx
  have hmem := isOpen_Ioo.mem_nhds hx
  have hdu := (hu.2.1.contDiffAt hmem).differentiableAt (by simp)
  have hdv := ((hp.mul hd).contDiffAt hmem).differentiableAt (by simp)
  refine ⟨hdu.hasDerivAt.congr_deriv ?_, hdv.hasDerivAt.congr_deriv ?_⟩
  · dsimp only
    field_simp [(deepTail_pos hT x ⟨hx.1.le, hx.2⟩).ne']
  · dsimp only
    linarith only [hu.2.2.2 x hx]

theorem tailNaturalEquation_node_recurrence {T : DeepTailData}
    (hT : DeepTailHypotheses T) {u : ℝ → ℝ} (hu : TailNaturalEquation T u) (n : ℕ) :
    -tailActualInteriorDiagonal T hT n * u (T.node (n + 1)) =
      tailActualNodeCoupling T hT n * u (T.node n) +
        tailActualNodeCoupling T hT (n + 1) * u (T.node (n + 2)) := by
  have hco : Ico (T.node 0) T.endpoint ⊆ Ico T.entrance T.endpoint :=
    fun _ hx => ⟨(deepTail_entrance_le_node hT 0).trans hx.1, hx.2⟩
  have hoo : Ioo (T.node 0) T.endpoint ⊆ Ioo T.entrance T.endpoint :=
    fun _ hx => ⟨(deepTail_entrance_le_node hT 0).trans_lt hx.1, hx.2⟩
  exact tailActualSolution_node_recurrence hT
    ((tailNaturalEquation_continuousOn hu).mono hco)
    ((tailNaturalEquation_flux_continuousOn hT hu).mono hco)
    ((tailNaturalEquation_system hT hu).mono hoo) n

/-- The actual mass-cell square integrals are summable solely from weighted `MemLp`. -/
theorem tailMassCell_sq_integral_summable {T : DeepTailData}
    (hT : DeepTailHypotheses T) {u : ℝ → ℝ} (hu : MemLp u 2 (deepTailMeasure T)) :
    Summable (fun n => ∫ x in T.node n..T.massEnd n, T.p x * u x ^ 2) := by
  have hs := (hasSum_integral_iUnion (tailMassCell_measurable T)
    (tailMassCell_pairwiseDisjoint hT) hu.integrable_sq.integrableOn).summable
  apply hs.congr
  intro n
  rw [tail_setIntegral_density hT (tailMassCell_measurable T n) (tailMassCell_subset hT n),
    intervalIntegral.integral_of_le (deepTail_node_lt_massEnd hT n).le,
    integral_Ioc_eq_integral_Ioo]
  rfl

end ContinuousFlexibility.Radial
