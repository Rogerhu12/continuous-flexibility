import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Parameter differentiation of an actual integral trajectory

The trajectory is only assumed continuous at its endpoints and solves its
ordinary differential equation in the open interval. Its parameter
derivative is obtained by differentiating that integral identity. No
parameter variational differential equation is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology Interval

set_option backward.isDefEq.respectTransparency false

/-- The parameter slice of a genuine projective tower has the usual real
derivative. This is stated abstractly to avoid expanding the state spaces. -/
theorem n08_hasDerivAt_parameterSlice
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set (E × ℝ)} {F : E × ℝ → ℝ}
    (J : SmoothDirections U F) {x : E} {q : ℝ} (hz : (x, q) ∈ U) :
    HasDerivAt (fun t : ℝ => F (x, t))
      (J.D 1 (x, q) (Fin.cons ((0 : E), (1 : ℝ)) Fin.elim0)) q := by
  have hd := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hz ((0 : E), (1 : ℝ))
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    projectiveFirstJetValue, zero_add, Prod.smul_mk, Prod.mk_add_mk,
    smul_zero, add_zero, smul_eq_mul, mul_one] using hd

/-- A moving angular argument contributes no first derivative when the
zero-parameter slice of the speed is constant in that argument. -/
theorem n08_hasDerivAt_comp_of_zeroSlice_const
    {F : ℝ × ℝ → ℝ} {c : ℝ → ℝ} {dc A a : ℝ}
    (hF : DifferentiableAt ℝ F (0, c 0))
    (hc : HasDerivAt c dc 0)
    (hzero : ∀ θ, F (0, θ) = a)
    (hparameter : HasDerivAt (fun q : ℝ => F (q, c 0)) A 0) :
    HasDerivAt (fun q : ℝ => F (q, c q)) A 0 := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := fderiv ℝ F (0, c 0)
  have hL : HasFDerivAt F L (0, c 0) := hF.hasFDerivAt
  have hq : HasDerivAt (fun q : ℝ => F (q, c 0)) (L (1, 0)) 0 := by
    simpa only [Function.comp_def] using
      hL.comp_hasDerivAt 0 ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 (c 0)))
  have hθ : HasDerivAt (fun t : ℝ => F (0, c 0 + t * dc)) (L (0, dc)) 0 := by
    have hi : HasDerivAt (fun t : ℝ => (0, c 0 + t * dc)) (0, dc) 0 := by
      simpa only [mul_one, one_mul] using
        (hasDerivAt_const 0 (0 : ℝ)).prodMk
          (((hasDerivAt_id 0).mul_const dc).const_add (c 0))
    simpa only [Function.comp_def, zero_mul, add_zero] using hL.comp_hasDerivAt_of_eq 0 hi (by simp only [zero_mul, add_zero])
  have hθzero : HasDerivAt (fun t : ℝ => F (0, c 0 + t * dc)) 0 0 :=
    (hasDerivAt_const 0 a).congr_of_eventuallyEq
      (Eventually.of_forall fun t => hzero (c 0 + t * dc))
  have hvalue : L (1, dc) = A := by
    calc
      L (1, dc) = L ((1, 0) + (0, dc)) := by
        simp only [Prod.mk_add_mk, add_zero, zero_add]
      _ = L (1, 0) + L (0, dc) := map_add L _ _
      _ = A := by rw [hq.unique hparameter, hθ.unique hθzero, add_zero]
  have hactual := hL.comp_hasDerivAt 0 ((hasDerivAt_id 0).prodMk hc)
  simpa only [Function.comp_def, hvalue] using hactual

/-- Differentiate the integral identity of the given trajectories. The
hypotheses concern the original time equation and the actual parameter
variation of its right hand side, not a differentiated time equation. -/
theorem n08_hasDerivAt_integralTrajectory
    {a b θ : ℝ} (hab : a ≤ b)
    {O : Set ℝ} (hO : O ∈ 𝓝 (0 : ℝ))
    {f V : ℝ → ℝ → ℝ} {W : ℝ → ℝ} {K : ℝ≥0}
    (hf : ∀ q ∈ O, ContinuousOn (f q) (Icc a b))
    (hinit : ∀ q ∈ O, f q a = θ)
    (htime : ∀ q ∈ O, ∀ r ∈ Ioo a b, HasDerivAt (f q) (V q r) r)
    (hVint : ∀ q ∈ O, IntervalIntegrable (V q) volume a b)
    (hWint : IntervalIntegrable W volume a b)
    (hlip : ∀ r ∈ Ioc a b, LipschitzOnWith K (fun q => V q r) O)
    (hparameter : ∀ r ∈ Ioc a b, HasDerivAt (fun q => V q r) (W r) 0) :
    HasDerivAt (fun q => f q b) (∫ r in a..b, W r) 0 := by
  have hzero : (0 : ℝ) ∈ O := mem_of_mem_nhds hO
  have hintegral : ∀ q ∈ O, f q b = θ + ∫ r in a..b, V q r := by
    intro q hq
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (hf q hq) (htime q hq) (hVint q hq)
    rw [hinit q hq] at h
    linarith only [h]
  have hder := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (F := V) (F' := W) (μ := volume) (a := a) (b := b)
    (bound := fun _ => (K : ℝ)) hO
    (hO.mono fun q hq => (hVint q hq).def'.aestronglyMeasurable)
    (hVint 0 hzero) hWint.def'.aestronglyMeasurable
    (Eventually.of_forall fun r hr => by
      simpa only [Real.nnabs_coe] using hlip r (by simpa only [uIoc_of_le hab] using hr))
    intervalIntegrable_const
    (Eventually.of_forall fun r hr =>
      hparameter r (by simpa only [uIoc_of_le hab] using hr))
  exact (hder.2.const_add θ).congr_of_eventuallyEq (hO.mono hintegral)

end ContinuousFlexibility.Analysis
