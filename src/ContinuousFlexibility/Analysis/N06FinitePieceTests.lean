module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Closed finite-piece distribution tests

At a fixed parameter, a finite sum of L² test pairings and scalar columns is a continuous
linear functional. Hence all such distributional identities are closed conditions. The
piece measures and the maps extracting each height and source coordinate are explicit.

This does not assert that a global physical test meets only finitely many canonical pieces,
or identify the physical relation with these tests. Those are separate geometric obligations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped RealInnerProductSpace InnerProductSpace BigOperators

variable {ι α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite distributional residual with its scalar columns retained. -/
def n06FinitePieceResidual (μ : ι → Measure α) (I : Finset ι)
    (U F : ∀ m, E →L[ℝ] Lp ℝ 2 (μ m))
    (heightTest sourceTest : ∀ m, Lp ℝ 2 (μ m)) (scalar : E →L[ℝ] ℝ) :
    E →L[ℝ] ℝ :=
  (∑ m ∈ I, ((innerSL ℝ (heightTest m)).comp (U m) -
    (innerSL ℝ (sourceTest m)).comp (F m))) + scalar

theorem n06FinitePieceResidual_apply (μ : ι → Measure α) (I : Finset ι)
    (U F : ∀ m, E →L[ℝ] Lp ℝ 2 (μ m))
    (heightTest sourceTest : ∀ m, Lp ℝ 2 (μ m)) (scalar : E →L[ℝ] ℝ) (u : E) :
    n06FinitePieceResidual μ I U F heightTest sourceTest scalar u =
      (∑ m ∈ I, ((∫ p, U m u p * heightTest m p ∂μ m) -
        ∫ p, F m u p * sourceTest m p ∂μ m)) + scalar u := by
  simp only [n06FinitePieceResidual, add_apply, sum_apply, sub_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def,
    RCLike.inner_apply, conj_trivial]

/-- One finite-piece weak equation is a closed condition on the original domain. -/
theorem isClosed_n06FinitePieceTest (μ : ι → Measure α) (I : Finset ι)
    (U F : ∀ m, E →L[ℝ] Lp ℝ 2 (μ m))
    (heightTest sourceTest : ∀ m, Lp ℝ 2 (μ m)) (scalar : E →L[ℝ] ℝ) :
    IsClosed {u : E |
      (∑ m ∈ I, ((∫ p, U m u p * heightTest m p ∂μ m) -
        ∫ p, F m u p * sourceTest m p ∂μ m)) + scalar u = 0} := by
  simpa only [n06FinitePieceResidual_apply] using
    (isClosed_eq (n06FinitePieceResidual μ I U F heightTest sourceTest scalar).continuous
      continuous_const)

/-- Any collection of genuine finite-piece distribution tests gives a closed relation. -/
theorem isClosed_n06FinitePieceDistributionRelation {Test : Type*}
    (μ : ι → Measure α) (I : Test → Finset ι)
    (U F : ∀ m, E →L[ℝ] Lp ℝ 2 (μ m))
    (heightTest sourceTest : ∀ t : Test, ∀ m, Lp ℝ 2 (μ m))
    (scalar : Test → E →L[ℝ] ℝ) :
    IsClosed {u : E | ∀ t : Test,
      (∑ m ∈ I t, ((∫ p, U m u p * heightTest t m p ∂μ m) -
        ∫ p, F m u p * sourceTest t m p ∂μ m)) + scalar t u = 0} := by
  simpa only [Set.ofPred_forall] using
    (isClosed_iInter fun t : Test =>
      isClosed_n06FinitePieceTest μ (I t) U F (heightTest t) (sourceTest t) (scalar t))

end ContinuousFlexibility.Analysis
