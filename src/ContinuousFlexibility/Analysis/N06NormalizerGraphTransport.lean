module

public import ContinuousFlexibility.Analysis.N06NormalizerGraphShear

/-!
# Source-preserving graph equivalences transport the selected inverse

These statements separate the elementary graph algebra from the large
dependent canonical data. They preserve the actual source projection.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem n06NormalizerGraphEquiv_source (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (v : G) (hv : ℓ v.val.1 = 0) (x : G) :
    (n06NormalizerGraphEquiv G ℓ v hv x).val.2 = x.val.2 := by
  have h := congrArg Prod.snd (n06NormalizerGraphEquiv_apply G ℓ v hv x)
  exact h

theorem n06NormalizerGraphEquiv_unknown (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (v : G) (hv : ℓ v.val.1 = 0) (x : G) :
    (n06NormalizerGraphEquiv G ℓ v hv x).val.1 =
      n06NormalizerUnknownShear ℓ v.val.1 x.val.1 := by
  have h := congrArg Prod.fst (n06NormalizerGraphEquiv_apply G ℓ v hv x)
  exact h.trans (n06NormalizerUnknownShear_apply ℓ v.val.1 x.val.1).symm

theorem n06_graph_equiv_inverse_right
    {G H : Submodule ℝ (X × E)} (e : G ≃L[ℝ] H)
    (hs : ∀ x : G, (e x).val.2 = x.val.2)
    (J : E →L[ℝ] G) (hJ : ∀ F, (J F).val.2 = F) (F : E) :
    ((e.toContinuousLinearMap.comp J) F).val.2 = F :=
  (hs (J F)).trans (hJ F)

theorem n06_graph_equiv_inverse_left
    {G H : Submodule ℝ (X × E)} (e : G ≃L[ℝ] H)
    (hs : ∀ x : G, (e x).val.2 = x.val.2)
    (J : E →L[ℝ] G) (hJ : ∀ x : G, J x.val.2 = x) (u : H) :
    (e.toContinuousLinearMap.comp J) u.val.2 = u := by
  have hs' : (e.symm u).val.2 = u.val.2 := by
    have he := hs (e.symm u)
    rw [e.apply_symm_apply] at he
    exact he.symm
  have hi := hJ (e.symm u)
  rw [hs'] at hi
  change e (J u.val.2) = u
  exact (congrArg e hi).trans (e.apply_symm_apply u)

theorem n06_graph_equiv_global_inverse
    {G H : Submodule ℝ (X × E)} (e : G ≃L[ℝ] H)
    (A : X →L[ℝ] X) (he : ∀ x : G, (e x).val.1 = A x.val.1)
    (J : E →L[ℝ] G) {Y : Type*} (f : E → Y) (g : Y → X)
    (hg : ∀ F, (J F).val.1 = g (f F)) (F : E) :
    ((e.toContinuousLinearMap.comp J) F).val.1 = A (g (f F)) :=
  (he (J F)).trans (congrArg A (hg F))

theorem n06_graph_equiv_source_bound
    {G H : Submodule ℝ (X × E)} (e : G ≃L[ℝ] H)
    (hs : ∀ x : G, (e x).val.2 = x.val.2)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ x : G, ‖x‖ ≤ C * ‖x.val.2‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : H, ‖x‖ ≤ C * ‖x.val.2‖ := by
  obtain ⟨C, hC, hb⟩ := h
  let M : ℝ := ‖e.toContinuousLinearMap‖
  have hM : 0 ≤ M := show 0 ≤ ‖e.toContinuousLinearMap‖ from
    ContinuousLinearMap.opNorm_nonneg e.toContinuousLinearMap
  refine ⟨(1 + M) * C, mul_pos (by positivity) hC, ?_⟩
  intro x
  have hs' : (e.symm x).val.2 = x.val.2 := by
    have he := hs (e.symm x)
    rw [e.apply_symm_apply] at he
    exact he.symm
  calc
    ‖x‖ = ‖e (e.symm x)‖ := congrArg norm (e.apply_symm_apply x).symm
    _ ≤ M * ‖e.symm x‖ := e.toContinuousLinearMap.le_opNorm _
    _ ≤ M * (C * ‖(e.symm x).val.2‖) :=
      mul_le_mul_of_nonneg_left (hb (e.symm x)) hM
    _ = M * C * ‖x.val.2‖ := by rw [hs', mul_assoc]
    _ ≤ (1 + M) * C * ‖x.val.2‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hC.le) (norm_nonneg _)

end ContinuousFlexibility.Analysis
