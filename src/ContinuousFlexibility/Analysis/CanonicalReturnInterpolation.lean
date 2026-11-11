import ContinuousFlexibility.Analysis.CanonicalReturnJacobianBounds
import ContinuousFlexibility.Analysis.CircleInverseExistence

/-!
# Explicit interpolation for the corrected return flow

The return adjustment and its interpolation are the actual maps used to
correct an ordinary characteristic flow. Positive Jacobians are preserved
by the convex interpolation. The two endpoint return equations follow
from the existing inverse identities, including the reflected equation.

This module constructs the flow candidate and proves these properties.
It does not identify the candidate with an arbitrary previously supplied
return correction or assert the coefficient and error estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def circleReturnAdjustment (g k l : ℝ → ℝ) (T θ : ℝ) : ℝ :=
  g (k (l θ - T))

def circleReturnInterpolation (u : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (1 - u) * θ + u * G θ

private theorem positive_deriv_differentiable
    {f : ℝ → ℝ} {A : ℝ} (hA : 0 < A) (hf : ∀ θ, A ≤ deriv f θ) :
    Differentiable ℝ f := fun θ =>
  differentiableAt_of_deriv_ne_zero (hA.trans_le (hf θ)).ne'

/-- The explicit return adjustment is a composition of the three actual
positive circle maps. -/
theorem circleReturnAdjustment_deriv_bounds
    {g k l : ℝ → ℝ} (T : ℝ)
    (hg : ∀ θ, (1 / 2 : ℝ) ≤ deriv g θ ∧ deriv g θ ≤ 2)
    (hk : ∀ θ, (1 / 4 : ℝ) ≤ deriv k θ ∧ deriv k θ ≤ 4)
    (hl : ∀ θ, (1 / 2 : ℝ) ≤ deriv l θ ∧ deriv l θ ≤ 2) (θ : ℝ) :
    (1 / 16 : ℝ) ≤ deriv (circleReturnAdjustment g k l T) θ ∧
      deriv (circleReturnAdjustment g k l T) θ ≤ 16 := by
  have dg := positive_deriv_differentiable (by norm_num : (0 : ℝ) < 1 / 2)
    (fun t => (hg t).1)
  have dk := positive_deriv_differentiable (by norm_num : (0 : ℝ) < 1 / 4)
    (fun t => (hk t).1)
  have dl := positive_deriv_differentiable (by norm_num : (0 : ℝ) < 1 / 2)
    (fun t => (hl t).1)
  have hd := (dg (k (l θ - T))).hasDerivAt.comp θ
    ((dk (l θ - T)).hasDerivAt.comp θ ((dl θ).hasDerivAt.sub_const T))
  have heq : deriv (circleReturnAdjustment g k l T) θ =
      deriv g (k (l θ - T)) * (deriv k (l θ - T) * deriv l θ) :=
    hd.deriv
  rw [heq]
  have hk0 : 0 ≤ deriv k (l θ - T) := le_trans (by norm_num) (hk _).1
  have hl0 : 0 ≤ deriv l θ := le_trans (by norm_num) (hl _).1
  have hkl0 := mul_nonneg hk0 hl0
  have hklLo := mul_le_mul (hk (l θ - T)).1 (hl θ).1
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hk0
  have hklHi := mul_le_mul (hk (l θ - T)).2 (hl θ).2 hl0
    (by norm_num : (0 : ℝ) ≤ 4)
  have hg0 : 0 ≤ deriv g (k (l θ - T)) := le_trans (by norm_num) (hg _).1
  have hlo := mul_le_mul (hg (k (l θ - T))).1 hklLo
    (by norm_num : (0 : ℝ) ≤ 1 / 4 * (1 / 2)) hg0
  have hhi := mul_le_mul (hg (k (l θ - T))).2 hklHi hkl0
    (by norm_num : (0 : ℝ) ≤ 2)
  constructor <;> nlinarith

/-- Convex interpolation with the identity retains a positive derivative
bound; it does not require the adjustment to have a small value. -/
theorem circleReturnInterpolation_deriv_bounds
    {G : ℝ → ℝ}
    (hG : ∀ θ, (1 / 16 : ℝ) ≤ deriv G θ ∧ deriv G θ ≤ 16)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    (1 / 16 : ℝ) ≤ deriv (circleReturnInterpolation u G) θ ∧
      deriv (circleReturnInterpolation u G) θ ≤ 16 := by
  have dG := positive_deriv_differentiable (by norm_num : (0 : ℝ) < 1 / 16)
    (fun t => (hG t).1)
  have hd := ((hasDerivAt_id θ).const_mul (1 - u)).add
    ((dG θ).hasDerivAt.const_mul u)
  have hfun : ((fun y : ℝ => (1 - u) * id y) + fun y => u * G y) =
      circleReturnInterpolation u G := by
    funext y
    simp only [Pi.add_apply, id_eq, circleReturnInterpolation]
  rw [hfun] at hd
  have heq : deriv (circleReturnInterpolation u G) θ = (1 - u) + u * deriv G θ := by
    simpa only [mul_one] using hd.deriv
  rw [heq]
  have hlo := mul_le_mul_of_nonneg_left (hG θ).1 hu.1
  have hhi := mul_le_mul_of_nonneg_left (hG θ).2 hu.1
  constructor <;> nlinarith [hu.2]

/-- The interpolated return has a genuine global inverse. -/
theorem circleReturnInterpolation_bijective
    {G : ℝ → ℝ}
    (hG : ∀ θ, (1 / 16 : ℝ) ≤ deriv G θ ∧ deriv G θ ≤ 16)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Function.Bijective (circleReturnInterpolation u G) :=
  bijective_of_deriv_lower_bound (by norm_num : (0 : ℝ) < 1 / 16)
    (fun θ => (circleReturnInterpolation_deriv_bounds hG hu θ).1)

theorem circleReturnInterpolation_inverse_deriv_bounds
    {G : ℝ → ℝ}
    (hG : ∀ θ, (1 / 16 : ℝ) ≤ deriv G θ ∧ deriv G θ ≤ 16)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    (1 / 16 : ℝ) ≤ deriv (Function.invFun (circleReturnInterpolation u G)) θ ∧
      deriv (Function.invFun (circleReturnInterpolation u G)) θ ≤ 16 := by
  have h := invFun_deriv_bounds (by norm_num : (0 : ℝ) < 1 / 16)
    (fun t => circleReturnInterpolation_deriv_bounds hG hu t) θ
  norm_num at h
  exact h

private theorem composed_circle_deriv_bounds
    {f J : ℝ → ℝ}
    (hf : ∀ t, (1 / 2 : ℝ) ≤ deriv f t ∧ deriv f t ≤ 2)
    (hJ : ∀ t, (1 / 16 : ℝ) ≤ deriv J t ∧ deriv J t ≤ 16) (θ : ℝ) :
    (1 / 32 : ℝ) ≤ deriv (fun t => f (J t)) θ ∧
      deriv (fun t => f (J t)) θ ≤ 32 := by
  have hFd := positive_deriv_differentiable (by norm_num : (0 : ℝ) < 1 / 2)
    (fun t => (hf t).1)
  have hJd := positive_deriv_differentiable (by norm_num : (0 : ℝ) < 1 / 16)
    (fun t => (hJ t).1)
  have hd := (hFd (J θ)).hasDerivAt.comp θ (hJd θ).hasDerivAt
  have hcomp : f ∘ J = fun t => f (J t) := by
    funext t
    exact Function.comp_apply f J t
  rw [hcomp] at hd
  rw [hd.deriv]
  have hF0 : 0 ≤ deriv f (J θ) := le_trans (by norm_num) (hf _).1
  have hJ0 : 0 ≤ deriv J θ := le_trans (by norm_num) (hJ θ).1
  have hlo := mul_le_mul (hf (J θ)).1 (hJ θ).1
    (by norm_num : (0 : ℝ) ≤ 1 / 16) hF0
  have hhi := mul_le_mul (hf (J θ)).2 (hJ θ).2 hJ0 (by norm_num : (0 : ℝ) ≤ 2)
  constructor <;> nlinarith

/-- The return-corrected flow candidate from the original N01 data. -/
def canonicalInterpolatedFlow (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (r θ : ℝ) : ℝ :=
  C.minusFlow z m r
    (circleReturnInterpolation (χ m r)
      (circleReturnAdjustment (C.minusReturnInverse z m) (C.rightChartInverse z m)
        (stateLeftChart S z.1 m) (C.travel m)) θ)

/-- The candidate flow has a uniform positive angular Jacobian on the
whole closed component. -/
theorem canonicalInterpolatedFlow_deriv_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hret : CanonicalReturnJacobianBounds S C base ε)
    {χ : ℕ → ℝ → ℝ} {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (hχ : χ m r ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    (1 / 32 : ℝ) ≤ deriv (canonicalInterpolatedFlow S C χ z m r) θ ∧
      deriv (canonicalInterpolatedFlow S C χ z m r) θ ≤ 32 := by
  let G := circleReturnAdjustment (C.minusReturnInverse z m) (C.rightChartInverse z m)
    (stateLeftChart S z.1 m) (C.travel m)
  let J := circleReturnInterpolation (χ m r) G
  have hL (t : ℝ) := hN.2.2.2.2.2.2.2.1 z hz hs m t
  have hG (t : ℝ) : (1 / 16 : ℝ) ≤ deriv G t ∧ deriv G t ≤ 16 :=
    circleReturnAdjustment_deriv_bounds (C.travel m)
      (fun t => (hret z hz hs m t).1)
      (fun t => (hret z hz hs m t).2.2)
      (fun t => ⟨(hL t).1, (hL t).2.1⟩) t
  have hJ (t : ℝ) : (1 / 16 : ℝ) ≤ deriv J t ∧ deriv J t ≤ 16 :=
    circleReturnInterpolation_deriv_bounds hG hχ t
  exact composed_circle_deriv_bounds (fun t => hflow z hz m r hr t) hJ θ

theorem canonicalInterpolatedFlow_bijective
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hret : CanonicalReturnJacobianBounds S C base ε)
    {χ : ℕ → ℝ → ℝ} {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (hχ : χ m r ∈ Icc (0 : ℝ) 1) :
    Function.Bijective (canonicalInterpolatedFlow S C χ z m r) :=
  bijective_of_deriv_lower_bound (by norm_num : (0 : ℝ) < 1 / 32)
    (fun θ => (canonicalInterpolatedFlow_deriv_bounds hN hflow hret hz hs m hr hχ θ).1)

/-- At the initial endpoint the interpolation is exactly the identity. -/
theorem canonicalInterpolatedFlow_left
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base : ℕ} {ε : ℝ}
    (hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε))
    {χ : ℕ → ℝ → ℝ} {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (m : ℕ)
    (hχ : χ m (C.left m) = 0) (θ : ℝ) :
    canonicalInterpolatedFlow S C χ z m (C.left m) θ = θ := by
  simpa only [canonicalInterpolatedFlow, circleReturnInterpolation, hχ,
    sub_zero, one_mul, zero_mul, add_zero] using (hflow z hz m θ).1

/-- The two required return identities hold for the explicit candidate,
with reflection handled by the odd charts. -/
theorem canonicalInterpolatedFlow_return
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {χ : ℕ → ℝ → ℝ} {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hχ : χ m (C.right m) = 1) (θ : ℝ) :
    rightChartCandidate S C z m
        (canonicalInterpolatedFlow S C χ z m (C.right m) θ) =
      stateLeftChart S z.1 m θ - C.travel m ∧
    rightChartCandidate S C z m
        (-canonicalInterpolatedFlow S C χ z m (C.right m) (-θ)) =
      stateLeftChart S z.1 m θ + C.travel m := by
  have hi (t : ℝ) := hN.2.2.2.2.2.2.2.2.1 z hz hs m t
  have hreturn (t : ℝ) :
      rightChartCandidate S C z m
          (canonicalInterpolatedFlow S C χ z m (C.right m) t) =
        stateLeftChart S z.1 m t - C.travel m := by
    simp only [canonicalInterpolatedFlow, circleReturnInterpolation, hχ,
      sub_self, zero_mul, one_mul, zero_add, circleReturnAdjustment]
    rw [(hi (C.rightChartInverse z m (stateLeftChart S z.1 m t - C.travel m))).1]
    exact (hi (stateLeftChart S z.1 m t - C.travel m)).2.2.1
  have hodd (t : ℝ) :
      rightChartCandidate S C z m (-t) = -rightChartCandidate S C z m t := by
    simp only [rightChartCandidate, oddPart, neg_neg]
    ring
  have hleftOdd := (hN.2.2.2.2.2.2.2.1 z hz hs m θ).2.2.2
  refine ⟨hreturn θ, ?_⟩
  rw [hodd, hreturn, hleftOdd]
  ring

end ContinuousFlexibility.Analysis
