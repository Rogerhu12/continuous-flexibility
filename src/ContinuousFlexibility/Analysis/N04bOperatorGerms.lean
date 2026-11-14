module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Operator locality and genuine smooth test extensions

A divergence operator depends only on the germ of its test function, even
when its stored coefficient fields have no regularity. This permits a
locally smooth test to be replaced by a globally smooth compactly supported
test after preserving the whole germ, rather than only finitely many jets.

The extension hypothesis is smoothness on an open neighborhood. Smoothness
at a single point of order infinity alone does not supply this hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open Set Filter Function
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Actual divergence operators preserve equality of test-function germs.
No regularity assumption is made on the coefficient fields. -/
theorem n04b_divergenceOperator_congr_germ
    {A : SymmetricCoefficients} {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hfg : f =ᶠ[𝓝 x] g) :
    divergenceOperator A f x = divergenceOperator A g x := by
  have hd : fderiv ℝ f =ᶠ[𝓝 x] fderiv ℝ g := hfg.fderiv
  have hr :
      (fun y => A.a y * radialPartial f y + A.b y * angularPartial f y) =ᶠ[𝓝 x]
        (fun y => A.a y * radialPartial g y + A.b y * angularPartial g y) := by
    filter_upwards [hd] with y hy
    simp only [radialPartial, angularPartial, hy]
  have ht :
      (fun y => A.b y * radialPartial f y + A.c y * angularPartial f y) =ᶠ[𝓝 x]
        (fun y => A.b y * radialPartial g y + A.c y * angularPartial g y) := by
    filter_upwards [hd] with y hy
    simp only [radialPartial, angularPartial, hy]
  unfold divergenceOperator
  apply congrArg₂ (· + ·)
  · exact congrArg (fun d : PolarPoint →L[ℝ] ℝ => d (1, 0)) hr.fderiv_eq
  · exact congrArg (fun d : PolarPoint →L[ℝ] ℝ => d (0, 1)) ht.fderiv_eq

/-- A smooth germ given on an open set has a globally smooth, compactly
supported representative. The representative agrees on a neighborhood. -/
theorem n04b_exists_contDiff_germ_extension
    {U : Set PolarPoint} {x : PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ W : PolarPoint → ℝ, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      W =ᶠ[𝓝 x] f := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let χ : ContDiffBump x :=
    ⟨ε / 2 / 2, ε / 2, half_pos (half_pos hε), half_lt_self (half_pos hε)⟩
  let W : PolarPoint → ℝ := fun y => χ y * f y
  have hsupp : tsupport (χ : PolarPoint → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    intro y hy
    apply hεU
    change dist y x ≤ ε / 2 at hy
    change dist y x < ε
    exact hy.trans_lt (half_lt_self hε)
  have hcompact : HasCompactSupport W := by
    change HasCompactSupport ((χ : PolarPoint → ℝ) * f)
    exact χ.hasCompactSupport.mul_right
  refine ⟨W, contDiff_iff_contDiffAt.mpr ?_, hcompact, ?_⟩
  · intro y
    by_cases hy : y ∈ tsupport (χ : PolarPoint → ℝ)
    · exact χ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hsupp hy)))
    · have hχ := notMem_tsupport_iff_eventuallyEq.mp hy
      apply (contDiffAt_const :
        ContDiffAt ℝ ∞ (fun _ : PolarPoint => (0 : ℝ)) y).congr_of_eventuallyEq
      filter_upwards [hχ] with z hz
      change χ z = 0 at hz
      change χ z * f z = 0
      rw [hz, zero_mul]
  · filter_upwards [χ.eventuallyEq_one] with y hy
    change χ y = 1 at hy
    change χ y * f y = f y
    rw [hy, one_mul]

/-- A global smooth test can realize the actual local operator evaluation
without any differentiability assumption on the stored coefficients. -/
theorem n04b_exists_contDiff_operator_test
    {A : SymmetricCoefficients} {U : Set PolarPoint} {x : PolarPoint}
    {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ W : PolarPoint → ℝ, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      W =ᶠ[𝓝 x] f ∧ divergenceOperator A W x = divergenceOperator A f x := by
  obtain ⟨W, hW, hc, he⟩ := n04b_exists_contDiff_germ_extension hU hx hf
  exact ⟨W, hW, hc, he, n04b_divergenceOperator_congr_germ he⟩

end ContinuousFlexibility.Analysis
