import ContinuousFlexibility.Radial.TailActualMassRecovery
import ContinuousFlexibility.Radial.TailNaturalSolution
import ContinuousFlexibility.Radial.TailNodeUniqueness

/-!
# Uniqueness of the actual square-integrable natural line

Mass recovery gives the weighted node summability required by the
Casoratian argument. The resulting proportional node values also give
proportional physical fluxes at the first interior node. Initial-value
uniqueness then extends the identity over the entire open tail, including
the actual initial gap.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem TailFirstOrderSystem.const_mul {p u v : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (h : TailFirstOrderSystem p Λ u v s) (c : ℝ) :
    TailFirstOrderSystem p Λ (fun x => c * u x) (fun x => c * v x) s := by
  intro x hx
  constructor
  · exact ((h x hx).1.const_mul c).congr_deriv (by ring)
  · exact ((h x hx).2.const_mul c).congr_deriv (by ring)

theorem tailActualNodeCoupling_normalized_bound {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) :
    |tailActualNodeCoupling T hT n| ≤
      (T.Λ / 8) * (Real.sqrt (tailMass T n) * Real.sqrt (tailMass T (n + 1))) :=
  tailNaturalNode_normalized_coupling_bound
    (fun n => (tailActualNodeCoupling_pos hT n).le) (tailMass_pos hT) (tailResistance_pos hT)
    hT.2.2.1 hK (tailActualNodeCoupling_upper hT hη)
    (fun n => (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.1)
    (fun n => (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.1) n

/-- Actual natural solutions are proportional at the nodes, with no assumed node summability. -/
theorem tailNaturalEquation_nodes_eq_mul {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hu : TailNaturalEquation T u) (hv : TailNaturalEquation T v)
    (hune : ∀ n, u (T.node n) ≠ 0) :
    ∀ n, v (T.node n) = (v (T.node 0) / u (T.node 0)) * u (T.node n) := by
  exact tailNodeLine_eq_mul_of_summable
    (b := fun n => -tailNaturalDiagonal T hT n)
    (c := tailActualNodeCoupling T hT) (μ := tailMass T)
    (y := fun n => u (T.node n)) (z := fun n => v (T.node n))
    (tailMass_pos hT) (fun n => (tailActualNodeCoupling_pos hT n).ne')
    ⟨T.Λ / 8, tailActualNodeCoupling_normalized_bound hT hη hK⟩
    (tailNaturalEquation_node_recurrence hT hu)
    (tailNaturalEquation_node_recurrence hT hv) hune
    (tailNaturalEquation_node_sq_summable hT hη hK hu)
    (tailNaturalEquation_node_sq_summable hT hη hK hv)

/-- Proportional node values determine the whole solution on the actual open tail. -/
theorem tailNaturalEquation_eq_mul {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ} (hu : TailNaturalEquation T u) (hv : TailNaturalEquation T v)
    (hune : ∀ n, u (T.node n) ≠ 0) :
    ∀ x ∈ Ioo T.entrance T.endpoint,
      v x = (v (T.node 0) / u (T.node 0)) * u x := by
  let c : ℝ := v (T.node 0) / u (T.node 0)
  have hnode : ∀ n, v (T.node n) = c * u (T.node n) :=
    tailNaturalEquation_nodes_eq_mul hT hη hK hu hv hune
  have hedge : Ioo (T.node 1) (T.node (1 + 1)) ⊆ Ioo T.entrance T.endpoint :=
    fun _ hx => ⟨(deepTail_entrance_le_node hT 1).trans_lt hx.1,
      hx.2.trans (deepTail_node_lt_endpoint hT (1 + 1))⟩
  have hflux (w : ℝ → ℝ) (hw : TailNaturalEquation T w) :
      T.p (T.node 1) * deriv w (T.node 1) =
        -tailActualEdgeDiagonal T hT 1 (tailActualEdgePoisson T hT 1) false * w (T.node 1) +
          tailActualNodeCoupling T hT 1 * w (T.node (1 + 1)) :=
    (tailActualEdge_solution_flux_endpoints hT 1
      ((tailNaturalEquation_continuousOn hw).mono (tailActualEdge_interval_subset hT 1))
      ((tailNaturalEquation_flux_continuousOn hT hw).mono (tailActualEdge_interval_subset hT 1))
      ((tailNaturalEquation_system hT hw).mono hedge)).1
  have hflux₁ : T.p (T.node 1) * deriv v (T.node 1) =
      c * (T.p (T.node 1) * deriv u (T.node 1)) := by
    rw [hflux v hv, hflux u hu, hnode 1, hnode (1 + 1)]
    ring
  have hx₁ : T.node 1 ∈ Ioo T.entrance T.endpoint :=
    ⟨deepTail_entrance_lt_succ_node hT 0, deepTail_node_lt_endpoint hT 1⟩
  have hp : ContinuousOn T.p (Ioo T.entrance T.endpoint) :=
    (deepTail_contDiffOn hT).continuousOn.mono (fun _ hx => ⟨hx.1.le, hx.2⟩)
  have hp₀ : ∀ x ∈ Ioo T.entrance T.endpoint, T.p x ≠ 0 :=
    fun x hx => (deepTail_pos hT x ⟨hx.1.le, hx.2⟩).ne'
  have hstate := tailFirstOrderSystem_eq_of_initial hx₁ hp hp₀
    (tailNaturalEquation_system hT hv) ((tailNaturalEquation_system hT hu).const_mul c)
    (hnode 1) hflux₁
  exact fun x hx => (hstate x hx).1

/-- The actual tail has the unique square-integrable line and the stated node decay. -/
theorem tailNaturalLineAndKernel {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) :
    TailNaturalLineAndKernel T := by
  obtain ⟨u, _, hu, _, _, _, _, _, hune, hnonzero, hstep, _⟩ :=
    exists_tailNaturalSolution hT hη hK
  refine ⟨u, hu, hnonzero, ?_, ⟨8, by norm_num, hstep⟩⟩
  intro v hv
  exact ⟨v (T.node 0) / u (T.node 0), tailNaturalEquation_eq_mul hT hη hK hu hv hune⟩

end ContinuousFlexibility.Radial
