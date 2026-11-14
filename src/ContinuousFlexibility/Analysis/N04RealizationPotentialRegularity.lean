module

public import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
public import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Genuine potential towers from the raw canonical fields

The two coordinate partials use one construction. Products and sums then
build the actual divergence operator and the reciprocal-height potential.
Only the three principal fields, pulled height, and reciprocal pulled
height have input towers. No potential tower is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {Ω : Set PolarPoint} {f : E → PolarPoint → ℝ}

/-- The actual partial derivative has the shifted genuine mixed tower
on the same open spatial and parameter sets. -/
def n04Realization_mixedJetRegularity_coordinatePartial
    (F : MixedJetRegularity U Ω f) (hΩ : IsOpen Ω) (radial : Bool) :
    MixedJetRegularity U Ω
      (fun x => if radial then radialPartial (f x) else angularPartial (f x)) := by
  cases radial with
  | false =>
      refine
        { spatial := fun x hx =>
            ((F.spatial x hx).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
          parameter := fun a b q hq =>
            (F.parameter a (b + 1) q hq).congr (fun x hx =>
              (mixedDerivative_angularPartial hΩ (F.spatial x hx) a b hq).symm) }
  | true =>
      refine
        { spatial := fun x hx =>
            ((F.spatial x hx).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
          parameter := fun a b q hq =>
            (F.parameter (a + 1) b q hq).congr (fun x hx =>
              (mixedDerivative_radialPartial hΩ (F.spatial x hx) a b hq).symm) }

/-- The stored divergence expression is formed from its genuine raw
principal and height towers, without any separate commutation premise. -/
def n04Realization_mixedJetRegularity_divergence
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    {A : E → SymmetricCoefficients} {u : E → PolarPoint → ℝ}
    (Ra : MixedJetRegularity U Ω (fun x => (A x).a))
    (Rb : MixedJetRegularity U Ω (fun x => (A x).b))
    (Rc : MixedJetRegularity U Ω (fun x => (A x).c))
    (Ru : MixedJetRegularity U Ω u) :
    MixedJetRegularity U Ω (fun x => divergenceOperator (A x) (u x)) := by
  let Rr := n04Realization_mixedJetRegularity_coordinatePartial Ru hΩ true
  let Rt := n04Realization_mixedJetRegularity_coordinatePartial Ru hΩ false
  let Rflux := (Ra.mul Rr hU hΩ).add (Rb.mul Rt hU hΩ) hU hΩ
  let Tflux := (Rb.mul Rr hU hΩ).add (Rc.mul Rt hU hΩ) hU hΩ
  exact (n04Realization_mixedJetRegularity_coordinatePartial Rflux hΩ true).add
    (n04Realization_mixedJetRegularity_coordinatePartial Tflux hΩ false) hU hΩ

/-- Both canonical signs use the same reciprocal-height construction. -/
def n04Realization_mixedJetRegularity_reciprocalHeightPotential
    (hU : IsOpen U) (hΩ : IsOpen Ω) (sign : ℝ)
    {A : E → SymmetricCoefficients} {H Q : E → PolarPoint → ℝ}
    (Ra : MixedJetRegularity U Ω (fun x => (A x).a))
    (Rb : MixedJetRegularity U Ω (fun x => (A x).b))
    (Rc : MixedJetRegularity U Ω (fun x => (A x).c))
    (RH : MixedJetRegularity U Ω H) (RQ : MixedJetRegularity U Ω Q) :
    MixedJetRegularity U Ω
      (fun x q => -sign * H x q * divergenceOperator (A x) (Q x) q) :=
  ((MixedJetRegularity.const hU hΩ (-sign)).mul RH hU hΩ).mul
    (n04Realization_mixedJetRegularity_divergence hU hΩ Ra Rb Rc RQ) hU hΩ

end ContinuousFlexibility.Analysis
