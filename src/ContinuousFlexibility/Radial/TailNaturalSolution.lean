import ContinuousFlexibility.Radial.TailActualNaturalNodes
import ContinuousFlexibility.Radial.TailNaturalInitialExtension
import ContinuousFlexibility.Radial.TailNaturalIntegrability
import ContinuousFlexibility.Radial.TailNaturalEntrance

/-!
# Existence of the actual square-integrable natural solution

The continued-fraction sequence is interpolated using the canonical
physical Poisson basis. The initial gap and the entrance extension preserve
the actual equation and the node values. The same solution belongs to both
weighted L¹ and L² and has the mass--resistance step decay.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem exists_tailNaturalSolution {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) :
    ∃ u v : ℝ → ℝ,
      TailNaturalEquation T u ∧
      ContDiffOn ℝ ∞ u (Iio T.endpoint) ∧ ContDiffOn ℝ ∞ v (Iio T.endpoint) ∧
      TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint) ∧
      Integrable u (deepTailMeasure T) ∧ u (T.node 0) = 1 ∧
      (∀ n, u (T.node n) ≠ 0) ∧
      (∃ x ∈ Ioo T.entrance T.endpoint, u x ≠ 0) ∧
      (∀ n, |u (T.node (n + 1))| ≤
        8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |u (T.node n)|) ∧
      u T.entrance ≠ 0 := by
  obtain ⟨a, ha₀, hane, hrec, hasq, haabs, hstep, _⟩ :=
    exists_tailActualNaturalNodes hT hη hK
  obtain ⟨u, v, hu, hv, hsys, hueq, hveq⟩ := exists_tailSmoothNaturalState hT hrec
  have hinit : ContinuousOn u (Icc T.entrance (T.node 0)) :=
    hu.continuousOn.mono (fun _ hx => hx.2.trans_lt (deepTail_node_lt_endpoint hT 0))
  have hLp : MemLp u 2 (deepTailMeasure T) :=
    tailActualExtension_memLp_two hT hη hK hasq hinit hueq
  have hL1 : Integrable u (deepTailMeasure T) :=
    tailActualExtension_integrable hT hη haabs hinit hueq
  have hnode (n : ℕ) : u (T.node n) = a n :=
    (hueq ⟨(deepTail_node_strictMono hT).monotone (Nat.zero_le n),
      deepTail_node_lt_endpoint hT n⟩).trans (tailPoissonInterpolation_node hT a n)
  have hneq (n : ℕ) : u (T.node n) ≠ 0 := by rw [hnode]; exact hane n
  have hODE := tailFirstOrderSystem_equation isOpen_Ioo
    (fun x hx => (deepTail_pos hT x ⟨hx.1.le, hx.2⟩).ne')
    (hsys.mono Ioo_subset_Ico_self)
  have ha₁ : |a 1| ≤ 1 := by
    have h := hstep 0
    rw [ha₀, abs_one, mul_one] at h
    apply h.trans
    apply (div_le_one (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT 1))
      (tailResistance_pos hT 0))).mpr
    linarith only [hK, (hT.2.2.2.2.2.2.2.2.2.2 0).2.2.2.2.1]
  have hv₀ : T.Λ * tailMass T 0 / 2 ≤ v (T.node 0) := by
    rw [hveq ⟨le_rfl, deepTail_node_lt_endpoint hT 0⟩]
    exact tailNaturalFirstFlux_lower hT hη hK ha₀ ha₁
  refine ⟨u, v, ⟨hu.contDiffAt (isOpen_Iio.mem_nhds hT.1),
    hu.mono (fun _ hx => hx.2), hLp, hODE⟩, hu, hv, hsys, hL1,
    (hnode 0).trans ha₀, hneq, ?_, ?_,
    tailActualState_entrance_ne_zero hT hK hsys ((hnode 0).trans ha₀) hv₀⟩
  · exact ⟨T.node 1, ⟨hT.2.1.trans_lt (tailActualEdge_order hT 0),
      deepTail_node_lt_endpoint hT 1⟩, hneq 1⟩
  · intro n
    simpa only [hnode] using hstep n

end ContinuousFlexibility.Radial
