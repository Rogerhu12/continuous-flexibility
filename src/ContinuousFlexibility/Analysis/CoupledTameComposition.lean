module

public import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear
public import ContinuousFlexibility.Analysis.SolveNewtonBridge
public import ContinuousFlexibility.Analysis.ProjectiveLimitSubspace

/-!
# Composition with represented projective codomains

The scalar calculus already permits arbitrary locally convex source and
intermediate spaces.  A continuous linear equivalence of the output with
a complete projective limit therefore suffices for composition in the
original output grading. This includes Banach control spaces and closed
subspaces and products of the physical spaces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements

section Composition

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {fbond : ∀ n, F (n + 1) →L[ℝ] F n}

theorem coupled_smoothTameOn_comp_equiv
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    (e : Z ≃L[ℝ] ProjectiveLimit F fbond)
    {U : Set X} {V : Set Y} {f : X → Y} {g : Y → Z}
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn q r V g)
    (hmap : MapsTo f U V) : SmoothTameOn p r U (g ∘ f) := by
  let r' : ℕ → Seminorm ℝ (ProjectiveLimit F fbond) :=
    fun n => (r n).comp e.symm.toLinearMap
  have hge : SmoothTameOn q r' V (fun y => e (g y)) :=
    solve_smoothTameOn_postcomp hg e.toContinuousLinearMap (B := 1) (by norm_num)
      (fun n z => by
        change r n (e.symm (e z)) ≤ 1 * r n z
        simp only [ContinuousLinearEquiv.symm_apply_apply, one_mul, le_refl])
  have hc := smoothTameOn_comp_generic hp htp htq hf hge hmap
  have hb : SmoothTameOn p r U (fun x => e.symm (e (g (f x)))) :=
    solve_smoothTameOn_postcomp hc e.symm.toContinuousLinearMap
      (B := 1) (by norm_num) (fun n w => by
        change r n (e.symm w) ≤ 1 * r n (e.symm w)
        simp only [one_mul, le_refl])
  exact smoothTameOn_congr hb (fun x _ => e.symm_apply_apply (g (f x)))

end Composition

section BanachComposition

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

theorem coupled_smoothTameOn_comp_banach
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    {U : Set X} {V : Set Y} {f : X → Y} {g : Y → Z}
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn q r V g)
    (hmap : MapsTo f U V) : SmoothTameOn p r U (g ∘ f) :=
  coupled_smoothTameOn_comp_equiv hp htp htq (constEquiv Z) hf hg hmap

end BanachComposition

end ContinuousFlexibility.Analysis
