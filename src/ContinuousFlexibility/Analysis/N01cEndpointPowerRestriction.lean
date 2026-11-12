import ContinuousFlexibility.Analysis.N01cWholeSpeedPowerBounds
import ContinuousFlexibility.Analysis.N01cBoundsRestriction

/-!
# Restricting the actual endpoint power control

The spatial loss is kept fixed. The original genuine parameter tower is
restricted to the smaller open set, and uniqueness identifies every
genuine tower used to evaluate its raw estimate. No extension of a tower
from the smaller domain is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {p : ℕ → Seminorm ℝ X} {center : X} {base base' loss : ℕ}
  {U V : Set X} {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
  {f : I → X → PolarPoint → ℝ}

def EndpointPowerControl.n01c_restrict
    (W : EndpointPowerControl p center base loss U Ω δ H E f)
    (hV : IsOpen V) (hVU : V ⊆ U) (hp : Monotone p) (hb : base ≤ base') :
    EndpointPowerControl p center base' loss V Ω δ H E f where
  regular m :=
    { spatial := fun x hx => (W.regular m).spatial x (hVU hx)
      parameter := fun a b q hq => ((W.regular m).parameter a b q hq).restrict hV hVU }
  bounds := by
    intro K s
    obtain ⟨C, A, hC, hA, hbound⟩ := W.bounds K s
    refine ⟨C, A, hC, hA, ?_⟩
    intro m k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
    let J₀ := (W.regular m).parameter a b q hq
    let Jᵣ := J₀.restrict hV hVU
    have hjet := HasProjectiveJetsOn.unique J.open_domain
      J.hasProjectiveJetsOn Jᵣ.hasProjectiveJetsOn k x hx
    have he : J.D k x v = J₀.D k x v := by
      have h := congrArg (fun Q : X [×k]→L[ℝ] ℝ => Q v) hjet
      simpa only [Jᵣ, SmoothDirections.restrict_D] using h
    rw [he]
    exact hbound m k hk a b hab q hq J₀ x (hVU hx)
      ((hp hb (x - center)).trans hlow) v
      (fun i => (hp hb (v i)).trans (hv i)) R hR hhigh hvhigh

@[simp] theorem EndpointPowerControl.n01c_restrict_parameter_D_apply
    (W : EndpointPowerControl p center base loss U Ω δ H E f)
    (hV : IsOpen V) (hVU : V ⊆ U) (hp : Monotone p) (hb : base ≤ base')
    (m : I) (a b : ℕ) (q : PolarPoint) (hq : q ∈ Ω m)
    (k : ℕ) (x : X) (v : Fin k → X) :
    (((W.n01c_restrict hV hVU hp hb).regular m).parameter a b q hq).D k x v =
      ((W.regular m).parameter a b q hq).D k x v := rfl

end ContinuousFlexibility.Analysis
