import ContinuousFlexibility.Radial.ClosedGradientResolvent
import ContinuousFlexibility.Radial.TailFormCore

/-!
# The positive Friedrichs resolvent of a deep tail

The form closure in the statement layer uses the product topology. Transport
it to the equivalent Hilbert product topology and apply orthogonal projection.
This identifies the actual Friedrichs graph with its positive resolvent and
proves strong convergence for increasing Dirichlet truncations.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
open ContinuousFlexibility.Statements

/-- The energy closure, viewed as a closed subspace of the Hilbert product. -/
def tailGradientSpace (T : DeepTailData) (endCut : ℝ) :
    ClosedSubmodule ℝ (GradientHilbert (DeepTailL2 T)) :=
  (⟨tailFormSubmodule T endCut, by
      rw [coe_tailFormSubmodule]
      exact tailFormLift_isClosed T endCut⟩ :
    ClosedSubmodule ℝ (DeepTailL2 T × DeepTailL2 T)).comap
      (WithLp.prodContinuousLinearEquiv 2 ℝ (DeepTailL2 T) (DeepTailL2 T)).toContinuousLinearMap

theorem mem_tailGradientSpace (T : DeepTailData) (endCut : ℝ)
    (q : GradientHilbert (DeepTailL2 T)) :
    q ∈ tailGradientSpace T endCut ↔ WithLp.ofLp q ∈ TailFormLift T endCut := by
  simp only [tailGradientSpace, ClosedSubmodule.mem_comap,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_apply,
    ← mem_tailFormSubmodule]

theorem coe_tailGradientSpace (T : DeepTailData) (endCut : ℝ) :
    (tailGradientSpace T endCut : Set (GradientHilbert (DeepTailL2 T))) =
      WithLp.ofLp ⁻¹' TailFormLift T endCut := by
  ext q
  exact mem_tailGradientSpace T endCut q

theorem tailGradientSpace_mono (T : DeepTailData) {a b : ℝ} (hab : a ≤ b) :
    tailGradientSpace T a ≤ tailGradientSpace T b := by
  intro q hq
  exact (mem_tailGradientSpace T b q).mpr
    (tailFormLift_mono T hab ((mem_tailGradientSpace T a q).mp hq))

/-- Orthogonal projection constructs `(A + 1)⁻¹` on the ambient weighted L² space. -/
def tailPositiveResolvent (T : DeepTailData) (endCut : ℝ) :
    DeepTailL2 T →L[ℝ] DeepTailL2 T :=
  closedGradientResolvent (tailGradientSpace T endCut)

theorem tailFriedrichsGraph_iff_closedGradientGraph (T : DeepTailData) (endCut : ℝ)
    (u f : DeepTailL2 T) :
    TailFriedrichsGraph T endCut u f ↔ ClosedGradientGraph (tailGradientSpace T endCut) u f := by
  constructor
  · rintro ⟨du, hdu, hform⟩
    refine ⟨WithLp.toLp 2 (u, du), ?_, WithLp.toLp_fst _, ?_⟩
    · apply (mem_tailGradientSpace T endCut _).mpr
      simpa only [WithLp.ofLp_toLp] using hdu
    · intro r hr
      have h := hform (WithLp.ofLp r) ((mem_tailGradientSpace T endCut r).mp hr)
      simpa only [WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.toLp_snd] using h
  · rintro ⟨q, hq, hqu, hform⟩
    refine ⟨q.snd, ?_, ?_⟩
    · rw [← hqu]
      have hq' := (mem_tailGradientSpace T endCut q).mp hq
      have heq : (q.fst, q.snd) = WithLp.ofLp q :=
        Prod.ext (WithLp.ofLp_fst q).symm (WithLp.ofLp_snd q).symm
      rwa [heq]
    · intro p hp
      have hmem : WithLp.toLp 2 p ∈ tailGradientSpace T endCut := by
        apply (mem_tailGradientSpace T endCut _).mpr
        simpa only [WithLp.ofLp_toLp] using hp
      simpa only [WithLp.toLp_fst, WithLp.toLp_snd] using hform (WithLp.toLp 2 p) hmem

theorem tailPositiveResolvent_graph (T : DeepTailData) (endCut : ℝ) (f : DeepTailL2 T) :
    TailFriedrichsGraph T endCut (tailPositiveResolvent T endCut f)
      (f - tailPositiveResolvent T endCut f) := by
  apply (tailFriedrichsGraph_iff_closedGradientGraph T endCut _ _).mpr
  exact closedGradientResolvent_graph (tailGradientSpace T endCut) f

/-- This equivalence includes the boundary conditions: it is the Friedrichs
graph, rather than just the differential expression in the interior. -/
theorem tailFriedrichsGraph_iff_positiveResolvent (T : DeepTailData) (endCut : ℝ)
    (u f : DeepTailL2 T) :
    TailFriedrichsGraph T endCut u f ↔ tailPositiveResolvent T endCut (f + u) = u := by
  rw [tailFriedrichsGraph_iff_closedGradientGraph]
  exact closedGradientGraph_iff_resolvent (tailGradientSpace T endCut) u f

theorem tailPositiveResolvent_norm_le (T : DeepTailData) (endCut : ℝ) :
    ‖tailPositiveResolvent T endCut‖ ≤ 1 :=
  closedGradientResolvent_norm_le (tailGradientSpace T endCut)

theorem tailPositiveResolvent_isSymmetric (T : DeepTailData) (endCut : ℝ) :
    (tailPositiveResolvent T endCut).toLinearMap.IsSymmetric :=
  closedGradientResolvent_isSymmetric (tailGradientSpace T endCut)

theorem tailGradientSpace_eq_closure_iSup {T : DeepTailData} (hT : DeepTailHypotheses T) :
    (tailGradientSpace T T.endpoint).toSubmodule =
      (⨆ n : ℕ, (tailGradientSpace T (T.node (n + 1))).toSubmodule).topologicalClosure := by
  have hm : Monotone (fun n : ℕ => (tailGradientSpace T (T.node (n + 1))).toSubmodule) := by
    intro m n hmn
    exact tailGradientSpace_mono T
      ((deepTail_node_strictMono hT).monotone (Nat.add_le_add_right hmn 1))
  apply SetLike.coe_injective
  rw [Submodule.topologicalClosure_coe, Submodule.coe_iSup_of_directed _ hm.directed_le]
  simp only [ClosedSubmodule.coe_toSubmodule, coe_tailGradientSpace]
  rw [tailFormLift_eq_closure_iUnion hT]
  have he := (WithLp.prodContinuousLinearEquiv 2 ℝ (DeepTailL2 T) (DeepTailL2 T)).toHomeomorph.preimage_closure
    (⋃ n : ℕ, TailFormLift T (T.node (n + 1)))
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph,
    WithLp.prodContinuousLinearEquiv_apply, preimage_iUnion] using he

/-- The positive resolvents of finite Dirichlet intervals converge strongly
to the positive Friedrichs resolvent of the full tail. -/
theorem tailPositiveResolvent_truncation_tendsto {T : DeepTailData}
    (hT : DeepTailHypotheses T) (f : DeepTailL2 T) :
    Tendsto (fun n : ℕ => tailPositiveResolvent T (T.node (n + 1)) f) atTop
      (𝓝 (tailPositiveResolvent T T.endpoint f)) := by
  apply closedGradientResolvent_tendsto (tailGradientSpace T T.endpoint)
    (fun n => tailGradientSpace T (T.node (n + 1)))
  · intro m n hmn
    exact tailGradientSpace_mono T
      ((deepTail_node_strictMono hT).monotone (Nat.add_le_add_right hmn 1))
  · exact tailGradientSpace_eq_closure_iSup hT

end ContinuousFlexibility.Radial
