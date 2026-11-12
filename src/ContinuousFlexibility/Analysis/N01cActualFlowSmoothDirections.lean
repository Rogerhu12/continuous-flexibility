import ContinuousFlexibility.Analysis.N01cFlowTopologicalContinuity
import ContinuousFlexibility.Analysis.N01cFlowInitialAngleSmooth
import ContinuousFlexibility.Analysis.N01cAngularJetTowers
import ContinuousFlexibility.Analysis.N01cPhysicalFlowRegularity

/-!
# Genuine state and angle towers of the supplied ordinary trajectories

The compact coordinate contains exactly the original `minusFlow`.
The actual speed tower and its finite-affine spatial smoothness give
joint continuity of those classical trajectories and then their genuine
state-and-initial-angle towers. The closed cosine-coordinate surjection
returns the same towers at every physical radius, including both ends.

The speed tower is an internal input to be constructed from the actual
speed estimates. The neighbourhood and its base are unchanged here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The original supplied flow evaluated in the compact component time. -/
def ordinaryFlowInCosineTime {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (m : ℕ)
    (p : (AnnularState S × ℝ) × PolarPoint) : ℝ :=
  C.minusFlow p.1 m (rootCosinePath (C.left m) (C.right m) p.2.1) p.2.2

section ActualTowers

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
  (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
    r ∈ Icc (C.left i) (C.right i) →
      0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
  (m : ℕ)
  (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
    (componentCosineSpeed D S C m))

include hS hT hA hB hpos J

/-- Joint state, time and initial-angle continuity is derived from the
supplied classical flow and the actual speed's joint continuity. -/
theorem continuousOn_ordinaryFlowInCosineTime :
    ContinuousOn (ordinaryFlowInCosineTime C m)
      (stateNeighborhood S C base ε ×ˢ
        (Icc (0 : ℝ) Real.pi ×ˢ (univ : Set ℝ))) := by
  have hjoint : ContinuousOn (componentCosineSpeed D S C m)
      (stateNeighborhood S C base ε ×ˢ
        (Icc (0 : ℝ) Real.pi ×ˢ (univ : Set ℝ))) :=
    J.continuousOn.mono (fun p hp => ⟨hp.1, mem_univ _⟩)
  exact circleTopologicalFlow_continuousOn
    (fun z hz => contDiff_componentCosineSpeed hS hT hA hB hpos hz m)
    hjoint Real.pi_pos
    (fun z _ => componentCosineSpeed_periodic hS z m)
    (fun z hz => continuousOn_componentCosineFlow hA hB hz m)
    (fun z hz => componentCosineFlow_initial hB hz m)
    (fun z hz t ht θ => hasDerivAt_componentCosineFlow hS hT hA hB hz m θ ht)

/-- One genuine joint tower at any compact time, on the original common
state neighbourhood and with the actual initial angle as a variable. -/
def cosineOrdinaryFlowJointSmoothDirections {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi) :
    SmoothDirections (stateNeighborhood S C base ε ×ˢ (univ : Set ℝ))
      (fun p => ordinaryFlowInCosineTime C m (p.1, (t, p.2))) :=
  topologicalCircleFlowCompactSmoothDirections
    (isOpen_stateNeighborhood S C base ε) J
    (continuousOn_ordinaryFlowInCosineTime hS hT hA hB hpos m J)
    (fun z hz => componentCosineFlow_initial hB hz m)
    (fun z hz t ht θ => hasDerivAt_componentCosineFlow hS hT hA hB hz m θ ht)
    (fun n x _ L =>
      contDiffOn_componentCosineSpeed_finiteAffine hS hT hA hB hpos m x L) ht

/-- The physical-radius joint tower is the tower of the very same
ordinary flow; selecting a compact preimage does not change its values. -/
def ordinaryFlowJointSmoothDirections {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) :
    SmoothDirections (stateNeighborhood S C base ε ×ˢ (univ : Set ℝ))
      (fun p => C.minusFlow p.1 m r p.2) := by
  have hpreimage := rootCosinePath_surjOn (hA.2.2.1.1 m).2.1 hr
  let t : ℝ := Classical.choose hpreimage
  have ht : t ∈ Icc (0 : ℝ) Real.pi := (Classical.choose_spec hpreimage).1
  have he : rootCosinePath (C.left m) (C.right m) t = r :=
    (Classical.choose_spec hpreimage).2
  exact (cosineOrdinaryFlowJointSmoothDirections hS hT hA hB hpos m J ht).congr
    (fun p _ => by
      change C.minusFlow p.1 m (rootCosinePath (C.left m) (C.right m) t) p.2 =
        C.minusFlow p.1 m r p.2
      rw [he])

/-- Every actual angular derivative has a genuine state tower. This
single tower contains all positive state orders simultaneously. -/
def ordinaryFlowAngularStateSmoothDirections {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) (b : ℕ) (θ : ℝ) :
    SmoothDirections (stateNeighborhood S C base ε)
      (fun z => iteratedDeriv b (C.minusFlow z m r) θ) :=
  smoothDirections_angularStateSlice
    (ordinaryFlowJointSmoothDirections hS hT hA hB hpos m J hr) b θ

/-- Literal zero-radial-order interface for the ordinary-flow tame
estimate. The chosen tower does not depend on the requested prefix of
state orders or on the spatial cutoff in a later bound. -/
def ordinaryFlowMixedZeroSmoothDirections (b : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
    SmoothDirections (stateNeighborhood S C base ε)
      (fun z => mixedDerivative 0 b (fun q => C.minusFlow z m q.1 q.2) p) :=
  (ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J hp b p.2).congr
    (fun z _ => by simp only [mixedDerivative, iteratedDeriv_zero])

end ActualTowers

end ContinuousFlexibility.Statements
