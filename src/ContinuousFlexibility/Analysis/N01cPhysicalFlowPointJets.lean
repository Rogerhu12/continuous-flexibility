module

public import ContinuousFlexibility.Analysis.N01cPhysicalLieParameterJets
public import ContinuousFlexibility.Analysis.N01cPhysicalGraphJets
public import ContinuousFlexibility.Analysis.N01cStateAngleIdentification

/-!
# Exact point-jet identification for positive radial flow derivatives

The canonical physical tower keeps the angular slice of the actual
state-flow composition as its derivative family. Pure state-and-angle
slots identify that slice with the same joint composition jet. The
word form retains the original direction type, so estimates may be
transported before the two arities are simplified.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]

section Graph

variable {U : Set X} {Θ f : X × ℝ → ℝ}

/-- The actual angular-state slice is the joint graph-composition jet
on the pure slots of any prescribed word. -/
theorem stateFlow_angularSlice_D_pureSlots
    (JΘ : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    (K : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    {n : ℕ} (w : StateAngleWord n) {x : X} (hx : x ∈ U)
    (θ : ℝ) (v : Fin w.stateArity → X) :
    let JC := smoothDirections_realCompTVS (smoothDirections_stateFlowGraph JΘ) K
      (fun p hp => ⟨hp.1, mem_univ _⟩)
    (smoothDirections_angularStateSlice JC w.angleArity θ).D w.stateArity x v =
      JC.D n (x, θ) (w.pureSlots v) := by
  let JC := smoothDirections_realCompTVS (smoothDirections_stateFlowGraph JΘ) K
    (fun p hp => ⟨hp.1, mem_univ _⟩)
  exact (smoothDirections_joint_pureSlots JC
    (fun a η => smoothDirections_angularStateSlice JC a η) w hx θ v).symm

/-- Keeping the whole direction quantifier avoids a dependent tuple
cast when the state-then-angle word is later reduced to its two arities. -/
theorem stateFlow_stateThenAngle_D_pureSlots
    (JΘ : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    (K : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (k b : ℕ) {x : X} (hx : x ∈ U) (θ : ℝ) :
    let w := StateAngleWord.stateThenAngle k b
    let JC := smoothDirections_realCompTVS (smoothDirections_stateFlowGraph JΘ) K
      (fun p hp => ⟨hp.1, mem_univ _⟩)
    ∀ v : Fin w.stateArity → X,
      (smoothDirections_angularStateSlice JC w.angleArity θ).D w.stateArity x v =
        JC.D (b + k) (x, θ) (w.pureSlots v) :=
  fun v => stateFlow_angularSlice_D_pureSlots JΘ K
    (StateAngleWord.stateThenAngle k b) hx θ v

end Graph

section PhysicalPoint

variable {U : Set X} {I : Set ℝ} {lam Θ : X → PolarPoint → ℝ}
  (hU : IsOpen U) (hI : IsOpen I)
  (hlam : ∀ x ∈ U, ContDiffOn ℝ ∞ (lam x) (I ×ˢ (univ : Set ℝ)))
  (hΘ : ∀ x ∈ U, ContDiffOn ℝ ∞ (Θ x) (I ×ˢ (univ : Set ℝ)))
  (hODE : ∀ x ∈ U, ∀ r ∈ I, ∀ θ : ℝ,
    HasDerivAt (fun t => Θ x (t, θ)) (lam x (r, Θ x (r, θ))) r)
  {r : ℝ} (hr : r ∈ I)
  (Jlam : ∀ a : ℕ, SmoothDirections (U ×ˢ (univ : Set ℝ))
    (fun p => mixedDerivative a 0 (lam p.1) (r, p.2)))
  (JΘ : SmoothDirections (U ×ˢ (univ : Set ℝ)) (fun p => Θ p.1 (r, p.2)))

/-- Identification by the physical ODE changes the value assertion, while
every multilinear map remains the actual angular composition jet. -/
theorem physicalFlowPositiveMixed_D_eq_angularComposition
    (n b k : ℕ) (θ : ℝ) (x : X) (v : Fin k → X) :
    let JO := physicalLieJointSmoothDirections hU hI hlam hr Jlam n
    let JC := smoothDirections_realCompTVS (smoothDirections_stateFlowGraph JΘ) JO
      (fun p hp => ⟨hp.1, mem_univ _⟩)
    (physicalFlowPositiveMixedSmoothDirections hU hI hlam hΘ hODE hr Jlam JΘ n b θ).D k x v =
      (smoothDirections_angularStateSlice JC b θ).D k x v := rfl

/-- Any genuine tower of the same positive-radial physical family has
the canonical maps at points of the original open neighbourhood. -/
theorem physicalFlowPositiveMixed_D_eq_canonical
    (n b k : ℕ) (θ : ℝ)
    (J : SmoothDirections U (fun x => mixedDerivative (n + 1) b (Θ x) (r, θ)))
    {x : X} (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v =
      (physicalFlowPositiveMixedSmoothDirections hU hI hlam hΘ hODE hr Jlam JΘ n b θ).D k x v := by
  exact congrArg (fun A : X [×k]→L[ℝ] ℝ => A v)
    (HasProjectiveJetsOn.unique hU J.hasProjectiveJetsOn
      (physicalFlowPositiveMixedSmoothDirections hU hI hlam hΘ hODE hr Jlam JΘ n b θ).hasProjectiveJetsOn k x hx)

end PhysicalPoint

end ContinuousFlexibility.Analysis
