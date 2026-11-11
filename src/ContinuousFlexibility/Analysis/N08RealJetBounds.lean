import ContinuousFlexibility.Analysis.N08StateLinearOperations
import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation

/-! # Scalar first-jet bounds on a fixed-parameter affine line -/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A scalar tower's first jet equals the derivative of its actual affine
line with the final real parameter fixed. -/
theorem n08_realFirstJet_fixedParameter
    {U : Set (E × ℝ)} {f : E × ℝ → ℝ} (J : SmoothDirections U f)
    {x v : E} {q df : ℝ} (hx : (x, q) ∈ U)
    (hd : HasDerivAt (fun t : ℝ => f (x + n08RealSMul t v, q)) df 0) :
    J.D 1 (x, q) (Fin.cons (v, 0) Fin.elim0) = df := by
  have hline := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hx (v, 0)
  have h : HasDerivAt (fun t : ℝ => f ((x, q) + t • (v, 0)))
      (J.D 1 (x, q) (Fin.cons (v, 0) Fin.elim0)) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr hline
  have hfixed : HasDerivAt (fun t : ℝ => f (x + n08RealSMul t v, q))
      (J.D 1 (x, q) (Fin.cons (v, 0) Fin.elim0)) 0 := by
    simpa only [n08RealSMul, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using h
  exact hfixed.unique hd

theorem n08_oneHigh_first_product_zero
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (v : E) :
    oneHighVariationWeight (pairGrading p realGrading) base high
      (0 : E × ℝ) (Fin.cons (v, 0) Fin.elim0) = p base v + p high v := by
  simp [oneHighVariationWeight, pairGrading, realGrading]

/-- Extract a first-order one-high estimate before instantiating the large
physical state space. All derivative identification is on the actual line. -/
theorem n08_realFirstJet_reference_bound
    {U : Set (E × ℝ)} {f : E × ℝ → ℝ} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x0 : E) (K : ℝ) (df : E → ℝ)
    (hx : (x0, 0) ∈ U)
    (hd : ∀ v : E, HasDerivAt (fun t : ℝ => f (x0 + n08RealSMul t v, 0)) (df v) 0)
    (hbound : ∀ z ∈ U, ∀ vs : Fin 1 → E × ℝ,
      |J.D 1 z vs| ≤ K * oneHighVariationWeight (pairGrading p realGrading)
        base high (z - (x0, 0)) vs) :
    ∀ v : E, |df v| ≤ K * (p base v + p high v) := by
  intro v
  have hvalue := n08_realFirstJet_fixedParameter J hx (hd v)
  have h := hbound (x0, 0) hx (Fin.cons (v, 0) Fin.elim0)
  simpa only [hvalue, sub_self, n08_oneHigh_first_product_zero] using h

end ContinuousFlexibility.Statements
