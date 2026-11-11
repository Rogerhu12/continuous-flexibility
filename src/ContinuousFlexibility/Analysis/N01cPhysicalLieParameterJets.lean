import ContinuousFlexibility.Analysis.N01cPhysicalLieAngularExpansion
import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph
import ContinuousFlexibility.Analysis.N01cAngularJetTowers
import ContinuousFlexibility.Analysis.N01cMixedPowerBounds

/-!
# Genuine parameter towers for positive physical radial flow jets

Coordinate words use the actual speed jets. Their finite sums and products
give the physical Lie expression on the joint state-and-angle domain.
Composition with the actual state-flow graph and the physical ODE then
identify every positive radial mixed flow jet. The construction precedes
every parameter order and uses no bound on the angle value of the lift.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- On a whole angular slice, radial and angular differentiation commute
through the actual iterated coordinate derivatives. -/
theorem iteratedDeriv_angularSlice_radialMixed
    {I : Set ℝ} {f : PolarPoint → ℝ} (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ f (I ×ˢ (univ : Set ℝ)))
    {r : ℝ} (hr : r ∈ I) (a b : ℕ) (θ : ℝ) :
    iteratedDeriv b (fun η => mixedDerivative a 0 f (r, η)) θ =
      mixedDerivative a b f (r, θ) := by
  have hΩ : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have he : (fun η => mixedDerivative a 0 f (r, η)) =
      (fun η => ((radialPartial^[a]) f) (r, η)) := by
    funext η
    simpa only [mixedDerivative, iteratedDeriv_zero, Nat.zero_add] using
      (mixedDerivative_iteratedRadialPartial hΩ hf a 0 0
        (p := (r, η)) ⟨hr, mem_univ η⟩).symm
  rw [he]
  simpa only [mixedDerivative, iteratedDeriv_zero, Nat.zero_add] using
    mixedDerivative_iteratedRadialPartial hΩ hf a 0 b ⟨hr, mem_univ θ⟩

section ParameterTowers

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The actual angular jet of a Lie expression has a state tower formed
from its finite order-preserving expansion. -/
def physicalLieAngularStateSmoothDirections
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (F : MixedJetRegularity U Ω f)
    (n b : ℕ) (q : PolarPoint) (hq : q ∈ Ω) :
    SmoothDirections U
      (fun x => mixedDerivative 0 b (physicalFlowLieJet (f x) n) q) := by
  let e := physicalLieAngularExpansion n b
  let terms : e.Index → X → ℝ := fun t x =>
    ∏ i, mixedDerivative (e.words t i).radialOrder (e.words t i).angularOrder (f x) q
  let J : ∀ t, SmoothDirections U (terms t) := fun t =>
    smoothDirections_finiteProduct hU (fun i =>
      F.parameter (e.words t i).radialOrder (e.words t i).angularOrder q hq)
  exact (smoothDirections_finiteSum hU J).congr (fun x hx =>
    (angularPhysicalFlowLieJet_eq_sum_mixedDerivative hΩ (F.spatial x hx) n b hq).symm)

/-- One coordinate word is obtained from the actual radial speed tower
by genuine angular differentiation. -/
def physicalLieWordJointSmoothDirections
    {U : Set X} {I : Set ℝ} {f : X → PolarPoint → ℝ}
    (hI : IsOpen I) (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (I ×ˢ (univ : Set ℝ)))
    {r : ℝ} (hr : r ∈ I)
    (J : ∀ a : ℕ, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p => mixedDerivative a 0 (f p.1) (r, p.2)))
    (w : PhysicalLieWord) :
    SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p => mixedDerivative w.radialOrder w.angularOrder (f p.1) (r, p.2)) :=
  (smoothDirections_angularIterate (J w.radialOrder) w.angularOrder).congr
    (fun p hp => iteratedDeriv_angularSlice_radialMixed hI (hf p.1 hp.1)
      hr w.radialOrder w.angularOrder p.2)

/-- The finite Lie expression itself has a genuine joint tower, uniformly
in the unrestricted angle coordinate. -/
def physicalLieJointSmoothDirections
    {U : Set X} {I : Set ℝ} {f : X → PolarPoint → ℝ}
    (hU : IsOpen U) (hI : IsOpen I)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (I ×ˢ (univ : Set ℝ)))
    {r : ℝ} (hr : r ∈ I)
    (J : ∀ a : ℕ, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p => mixedDerivative a 0 (f p.1) (r, p.2))) (n : ℕ) :
    SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p => physicalFlowLieJet (f p.1) n (r, p.2)) := by
  let e := physicalLieExpansion n
  let terms : e.Index → X × ℝ → ℝ := fun t p =>
    ∏ i, mixedDerivative (e.words t i).radialOrder (e.words t i).angularOrder
      (f p.1) (r, p.2)
  let JT : ∀ t, SmoothDirections (U ×ˢ (univ : Set ℝ)) (terms t) := fun t =>
    smoothDirections_finiteProduct (hU.prod isOpen_univ) (fun i =>
      physicalLieWordJointSmoothDirections hI hf hr J (e.words t i))
  exact (smoothDirections_finiteSum (hU.prod isOpen_univ) JT).congr (fun p hp =>
    (physicalFlowLieJet_eq_sum_mixedDerivative (hI.prod isOpen_univ)
      (hf p.1 hp.1) n ⟨hr, mem_univ p.2⟩).symm)

variable [LocallyConvexSpace ℝ X]

/-- The physical ODE identifies the composed genuine tower with every
positive radial derivative of the same supplied flow. -/
def physicalFlowPositiveMixedSmoothDirections
    {U : Set X} {I : Set ℝ} {lam Θ : X → PolarPoint → ℝ}
    (hU : IsOpen U) (hI : IsOpen I)
    (hlam : ∀ x ∈ U, ContDiffOn ℝ ∞ (lam x) (I ×ˢ (univ : Set ℝ)))
    (hΘ : ∀ x ∈ U, ContDiffOn ℝ ∞ (Θ x) (I ×ˢ (univ : Set ℝ)))
    (hODE : ∀ x ∈ U, ∀ r ∈ I, ∀ θ : ℝ,
      HasDerivAt (fun t => Θ x (t, θ)) (lam x (r, Θ x (r, θ))) r)
    {r : ℝ} (hr : r ∈ I)
    (Jlam : ∀ a : ℕ, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p => mixedDerivative a 0 (lam p.1) (r, p.2)))
    (JΘ : SmoothDirections (U ×ˢ (univ : Set ℝ)) (fun p => Θ p.1 (r, p.2)))
    (n b : ℕ) (θ : ℝ) :
    SmoothDirections U (fun x => mixedDerivative (n + 1) b (Θ x) (r, θ)) := by
  let JO := physicalLieJointSmoothDirections hU hI hlam hr Jlam n
  let JG := smoothDirections_stateFlowGraph JΘ
  let JC := smoothDirections_realCompTVS JG JO (fun p hp => ⟨hp.1, mem_univ _⟩)
  exact (smoothDirections_angularStateSlice JC b θ).congr (fun x hx =>
    (mixedDerivative_physicalFlow_eq_lie hI (hlam x hx) (hΘ x hx)
      (hODE x hx) n b ⟨hr, mem_univ θ⟩).symm)

end ParameterTowers

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The canonical positive-radial tower concerns the original supplied
ordinary flow, on its original state neighbourhood and component. -/
def ordinaryFlowPositiveMixedSmoothDirections
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base : ℕ} {ε : ℝ} (hB : N01PartB D S C base ε) (m : ℕ)
    (hlam : ∀ z ∈ stateNeighborhood S C base ε, ContDiffOn ℝ ∞
      (minusCharacteristicSpeed (originalCoefficients D S C z))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hΘ : ∀ z ∈ stateNeighborhood S C base ε, ContDiffOn ℝ ∞
      (fun q : PolarPoint => C.minusFlow z m q.1 q.2)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m))
    (Jlam : ∀ a : ℕ, SmoothDirections
      (stateNeighborhood S C base ε ×ˢ (univ : Set ℝ))
      (fun p => mixedDerivative a 0
        (minusCharacteristicSpeed (originalCoefficients D S C p.1)) (r, p.2)))
    (JΘ : SmoothDirections (stateNeighborhood S C base ε ×ˢ (univ : Set ℝ))
      (fun p => C.minusFlow p.1 m r p.2)) (n b : ℕ) (θ : ℝ) :
    SmoothDirections (stateNeighborhood S C base ε)
      (fun z => mixedDerivative (n + 1) b (fun q => C.minusFlow z m q.1 q.2) (r, θ)) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  exact physicalFlowPositiveMixedSmoothDirections
    (X := AnnularState S × ℝ) (isOpen_stateNeighborhood S C base ε) isOpen_Ioo
    hlam hΘ (fun z hz t ht η => (hB.1 z hz m η).2.2.1 t ht)
    hr Jlam JΘ n b θ

end ContinuousFlexibility.Statements
