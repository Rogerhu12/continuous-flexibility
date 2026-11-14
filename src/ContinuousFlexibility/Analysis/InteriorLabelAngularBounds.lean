module

public import ContinuousFlexibility.Analysis.InteriorEndpointMaterialJets
public import ContinuousFlexibility.Scalar.Conservation

/-!
# Angular bounds for a genuinely transported section label

The angular derivative of a label transported by the actual inverse
flow is the product of the section-label derivative and the inverse
flow Jacobian. Open-set equality identifies this with the ordinary
angular derivative of the original first integral, including a cut.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem interiorTransportedLabel_angular_bounds
    {u : ℝ → ℝ} {Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    {a b κ K Λ : ℝ} (hab : a < b) (hκ : 0 ≤ κ)
    (hu : ContDiff ℝ ∞ u) (hub : ∀ θ, deriv u θ ∈ Icc κ K)
    (hΨ : ContDiff ℝ ∞ (fun q : N04FlowPoint => Ψ q.1 1 q.2))
    (hΨb : ∀ v ∈ n04FlowParameterBox, ∀ θ,
      deriv (fun η => Ψ v 1 η) θ ∈ Icc (Real.exp (-Λ)) (Real.exp Λ))
    {U : PolarPoint → ℝ} {V : Set PolarPoint} (hV : IsOpen V)
    (hradial : ∀ q ∈ V, q.1 ∈ Icc a b)
    (he : EqOn U (fun q => u (interiorEndpointPullback Ψ a b q)) V)
    {q : PolarPoint} (hq : q ∈ V) :
    angularPartial U q ∈ Icc (κ * Real.exp (-Λ)) (K * Real.exp Λ) := by
  let v := interiorEndpointParameter a b q.1
  let g : PolarPoint → ℝ := interiorEndpointPullback Ψ a b
  have hg : ContDiff ℝ ∞ g := contDiff_interiorEndpointPullback hΨ a b
  have hU : ContDiffAt ℝ ∞ U q := by
    have hh : U =ᶠ[𝓝 q] (u ∘ g) :=
      Filter.eventually_of_mem (hV.mem_nhds hq) (fun y hy => he hy)
    exact (hu.comp hg).contDiffAt.congr_of_eventuallyEq hh
  have hslice : ContDiff ℝ ∞ (fun θ : ℝ => Ψ v 1 θ) :=
    hΨ.comp (contDiff_const.prodMk contDiff_id)
  have hd := ((hu.differentiable (by simp)) (Ψ v 1 q.2)).hasDerivAt.comp q.2
    (((hslice.differentiable (by simp)) q.2).hasDerivAt)
  have hd' : HasDerivAt (fun θ => u (Ψ v 1 θ))
      (deriv u (Ψ v 1 q.2) * deriv (fun θ => Ψ v 1 θ) q.2) q.2 := by
    simpa only [Function.comp_def] using hd
  have hcurve : (fun θ => U (q.1, θ)) =ᶠ[𝓝 q.2]
      (fun θ => u (Ψ v 1 θ)) := by
    have hc : Continuous (fun θ : ℝ => (q.1, θ)) :=
      continuous_const.prodMk continuous_id
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hV.mem_nhds hq)] with θ hθ
    exact he hθ
  have hdiff := hasDerivAt_angular_slice (hU.differentiableAt (by simp))
  have hactual : angularPartial U q =
      deriv u (Ψ v 1 q.2) * deriv (fun θ => Ψ v 1 θ) q.2 :=
    hdiff.unique (hd'.congr_of_eventuallyEq hcurve)
  have hv : v ∈ n04FlowParameterBox := interiorEndpointParameter_mem hab (hradial q hq)
  have huvalue := hub (Ψ v 1 q.2)
  have hflow := hΨb v hv q.2
  rw [hactual]
  constructor
  · exact mul_le_mul huvalue.1 hflow.1 (Real.exp_pos (-Λ)).le (hκ.trans huvalue.1)
  · exact mul_le_mul huvalue.2 hflow.2
      ((Real.exp_pos (-Λ)).le.trans hflow.1) ((hκ.trans huvalue.1).trans huvalue.2)

end ContinuousFlexibility.Analysis
