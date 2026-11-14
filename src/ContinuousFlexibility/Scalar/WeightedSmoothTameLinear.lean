module

public import ContinuousFlexibility.Scalar.WeightedSmoothTameAlgebra
public import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-!
# Linear operations on the full scalar product domains

The coordinate projections have zero loss for the prescribed sum grading.
Postcomposition by a fixed tame linear map retains the original domain,
including unrestricted independent operator arguments.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section Projections

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

theorem scalar_pair_fst_isTame (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    IsTameLinear (pairGrading p q) p
      (ContinuousLinearMap.fst ℝ E F).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun z => ?_⟩
  change p s z.1 ≤ (1 : ℝ) * (p (s + 0) z.1 + q (s + 0) z.2)
  simpa only [Nat.add_zero, one_mul] using
    (le_add_of_nonneg_right (apply_nonneg (q s) z.2) : p s z.1 ≤ p s z.1 + q s z.2)

theorem scalar_pair_snd_isTame (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    IsTameLinear (pairGrading p q) q
      (ContinuousLinearMap.snd ℝ E F).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun z => ?_⟩
  change q s z.2 ≤ (1 : ℝ) * (p (s + 0) z.1 + q (s + 0) z.2)
  simpa only [Nat.add_zero, one_mul] using
    (le_add_of_nonneg_left (apply_nonneg (p s) z.1) : q s z.2 ≤ p s z.1 + q s z.2)

theorem smoothTameOn_continuousLinear_on
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} (hU : IsOpen U) (L : E →L[ℝ] F)
    {loss base : ℕ} (hL : IsTameLinear p q L.toLinearMap loss base) :
    SmoothTameOn p q U L :=
  ((fixedNeighborhoodSmoothTame_continuousLinear L hL).restrict hU (subset_univ _)).1

end Projections

section Postcomposition

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {fbond : ∀ n, F (n + 1) →L[ℝ] F n}
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit F fbond)}
  {U : Set X} {f : X → Y} {loss base : ℕ}

theorem smoothTameOn_postcompose_generic
    (hp : Monotone p) (ht : WithSeminorms p) (hqt : WithSeminorms q)
    (hf : SmoothTameOn p q U f)
    (L : Y →L[ℝ] ProjectiveLimit F fbond)
    (hL : IsTameLinear q r L.toLinearMap loss base) :
    SmoothTameOn p r U (fun x => L (f x)) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  letI : IsTopologicalAddGroup Y := hqt.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := hqt.continuousSMul
  letI : LocallyConvexSpace ℝ Y := hqt.toLocallyConvexSpace
  have hc := smoothTameOn_comp_generic
    (f := f) (g := fun y : Y => L y) hp ht hqt hf
    (smoothTameOn_continuousLinear L hL) (fun _ _ => mem_univ _)
  simpa only [Function.comp_def] using hc

end Postcomposition

end ContinuousFlexibility.Statements
