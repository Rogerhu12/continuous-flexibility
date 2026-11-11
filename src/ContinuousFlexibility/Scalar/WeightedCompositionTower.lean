import ContinuousFlexibility.Scalar.WeightedConservation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual pointwise derivatives of weighted composition maps

Continuous linear observations identify every directional derivative of a
composition tower.  The identity is proved from the genuine line derivatives
in `SmoothDirections`, so later estimates apply to the actual tower rather
than a separately postulated family of formal derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

section ScalarObservation

variable {E G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
  {U : Set E} {f : E → G}

/-- A scalar smooth function of one continuous linear observation has its
usual all-order derivative formula in every genuine projective tower. -/
theorem SmoothDirections.scalar_comp_linear
    (J : SmoothDirections U f) (L : G →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hvalue : ∀ x ∈ U, L (f x) = F (ℓ x)) :
    ∀ k x, x ∈ U → ∀ v : Fin k → E,
      L (J.D k x v) = iteratedDeriv k F (ℓ x) * ∏ i, ℓ (v i) := by
  intro k
  induction k with
  | zero =>
    intro x hx v
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    rw [hv, J.zero x hx, hvalue x hx]
    simp only [iteratedDeriv_zero, Fin.prod_univ_zero, mul_one]
  | succ k ih =>
    intro x hx v
    have hk : ContDiff ℝ ∞ (iteratedDeriv k F) := by
      rw [iteratedDeriv_eq_iterate]
      exact hF.iterate_deriv k
    have hdF (y : ℝ) : HasDerivAt (iteratedDeriv k F) (iteratedDeriv (k + 1) F y) y := by
      simpa only [iteratedDeriv_succ] using (hk.differentiable (by simp) y).hasDerivAt
    have hpath : Continuous (fun t : ℝ => x + t • v 0) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have htend : Tendsto (fun t : ℝ => x + t • v 0) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul, add_zero] using hpath.tendsto 0
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • v 0 ∈ U :=
      htend.eventually (J.open_domain.mem_nhds hx)
    have heq : (fun t : ℝ => L (J.D k (x + t • v 0) (Fin.tail v))) =ᶠ[𝓝 0]
        (fun t : ℝ => iteratedDeriv k F (ℓ x + t * ℓ (v 0)) *
          ∏ i : Fin k, ℓ (Fin.tail v i)) := by
      filter_upwards [hnear] with t ht
      rw [ih (x + t • v 0) ht]
      simp only [map_add, map_smul, smul_eq_mul]
    have hline : HasDerivAt (fun t : ℝ => ℓ x + t * ℓ (v 0)) (ℓ (v 0)) 0 := by
      simpa only [one_mul, zero_add] using
        (hasDerivAt_const (0 : ℝ) (ℓ x)).add ((hasDerivAt_id 0).mul_const (ℓ (v 0)))
    have hscalar : HasDerivAt
        (fun t : ℝ => iteratedDeriv k F (ℓ x + t * ℓ (v 0)) *
          ∏ i : Fin k, ℓ (Fin.tail v i))
        ((iteratedDeriv (k + 1) F (ℓ x) * ℓ (v 0)) *
          ∏ i : Fin k, ℓ (Fin.tail v i)) 0 := by
      simpa only [zero_mul, add_zero, Function.comp_def] using
        ((hdF (ℓ x + (0 : ℝ) * ℓ (v 0))).comp 0 hline).mul_const
          (∏ i : Fin k, ℓ (Fin.tail v i))
    have hJ := J.hasDerivAt_linear_output L k x hx (Fin.tail v) (v 0)
    have hresult := hJ.deriv.symm.trans (heq.deriv_eq.trans hscalar.deriv)
    simpa only [Fin.cons_self_tail, Fin.prod_univ_succ, Fin.tail, mul_assoc] using hresult

end ScalarObservation

/-- The pointwise formula for every derivative of an actual Sobolev
composition map, with the original input and output decoder. -/
theorem sobolevCompositionTower_decode
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hA : IsSobolevModel D T γ A)
    {U : Set A.Space} {f : A.Space → A.Space}
    (J : SmoothDirections U f) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hdecode : ∀ x ∈ U, ∀ p, A.decode (f x) p = F (A.decode x p))
    (k : ℕ) (x : A.Space) (hx : x ∈ U) (v : Fin k → A.Space) (p : PolarPoint) :
    A.decode (J.D k x v) p = iteratedDeriv k F (A.decode x p) *
      ∏ i, A.decode (v i) p := by
  let L : A.Space →L[ℝ] ℝ := A.evaluationCLM hA.2.2.1 p
  have hv : ∀ y ∈ U, L (f y) = F (L y) := by
    intro y hy
    simpa only [L, SobolevModelData.evaluationCLM_apply] using hdecode y hy p
  simpa only [L, SobolevModelData.evaluationCLM_apply] using
    J.scalar_comp_linear L L hF hv k x hx v

end ContinuousFlexibility.Statements
