import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# Linear coordinate maps for local tame calculus

Projections, injections and finite tuple coordinates have zero derivative
loss for the sum gradings used in the local estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators NNReal
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section LinearEstimates

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

theorem inverseTame_fst (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    IsTameLinear (pairGrading p q) p (ContinuousLinearMap.fst ℝ E F).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  simp only [Nat.add_zero, NNReal.coe_one, one_mul, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.fst_apply, pairGrading_apply]
  exact le_add_of_nonneg_right (apply_nonneg _ _)

theorem inverseTame_snd (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    IsTameLinear (pairGrading p q) q (ContinuousLinearMap.snd ℝ E F).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  simp only [Nat.add_zero, NNReal.coe_one, one_mul, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.snd_apply, pairGrading_apply]
  exact le_add_of_nonneg_left (apply_nonneg _ _)

theorem inverseTame_inl (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    IsTameLinear p (pairGrading p q) (ContinuousLinearMap.inl ℝ E F).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  simp only [Nat.add_zero, NNReal.coe_one, one_mul, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.inl_apply, pairGrading_apply, map_zero, add_zero]

theorem inverseTame_inr (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    IsTameLinear q (pairGrading p q) (ContinuousLinearMap.inr ℝ E F).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  simp only [Nat.add_zero, NNReal.coe_one, one_mul, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.inr_apply, pairGrading_apply, map_zero, zero_add]

theorem inverseTame_comp_zero
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {A : E →L[ℝ] F} {B : F →L[ℝ] G}
    (hB : IsTameLinear q r B.toLinearMap 0 0)
    (hA : IsTameLinear p q A.toLinearMap 0 0) :
    IsTameLinear p r (B.comp A).toLinearMap 0 0 := by
  simpa only [Nat.zero_add, max_self] using hB.comp hA

theorem inverseLocallyTame_fst
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : E → F × G} (hf : LocallyTameOn p (pairGrading q r) U f) :
    LocallyTameOn p q U (fun x => (f x).1) :=
  (locallyTameOn_of_isTameLinear (ContinuousLinearMap.fst ℝ F G)
    (inverseTame_fst q r) univ).comp hf (fun _ _ => mem_univ _)

theorem inverseLocallyTame_snd
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : E → F × G} (hf : LocallyTameOn p (pairGrading q r) U f) :
    LocallyTameOn p r U (fun x => (f x).2) :=
  (locallyTameOn_of_isTameLinear (ContinuousLinearMap.snd ℝ F G)
    (inverseTame_snd q r) univ).comp hf (fun _ _ => mem_univ _)

theorem inverseTame_tupleProjection (p : ℕ → Seminorm ℝ E) {n : ℕ} (i : Fin n) :
    IsTameLinear (tupleGrading (fun _ : Fin n => p)) p
      (ContinuousLinearMap.proj i).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  simp only [Nat.add_zero, NNReal.coe_one, one_mul, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.proj_apply, tupleGrading_apply]
  exact Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)

end LinearEstimates

end ContinuousFlexibility.Analysis
