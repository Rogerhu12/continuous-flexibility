import ContinuousFlexibility.Analysis.ScalarReanchoredInverseGerm
import ContinuousFlexibility.Analysis.N03RootJointContinuity

/-!
# Reanchoring the original stored trajectories at either root

The true closed canonical root lifts determine the stored endpoint map.
Their exact first-integral equation gives bijectivity and continuity of
the actual chosen inverse. This uses neither a field certificate nor
the N02 gauge identification, and supplies the initial-angle change used
when comparing the right-root controlled flow with the stored family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n03_rootReturn_bijective_and_continuous_invFun
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) :
    let c := if side then C.right m else C.left m
    Function.Bijective (L.minusFlow z m c) ∧
      Continuous (Function.invFun (L.minusFlow z m c)) := by
  let c := if side then C.right m else C.left m
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let F : ℝ → ℝ := fun θ => (K.chart z (K.cutPair m).1 (C.left m, θ)).2
  let G : ℝ → ℝ := fun θ => (K.chart z i (c, θ)).2 +
    if side then 2 * airyTravelPrimitive (K.cutRadius m) else 0
  have hleft (θ : ℝ) := canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m false θ
  have hroot (θ : ℝ) := canonicalCutPair_root_mem_closed_and_zero hA hB hz hs m side θ
  have hl := canonicalBoundaryAngular_bijective hA hz hs (K.cutPair m).1
    (fun θ => (hleft θ).1) (fun θ => (hleft θ).2)
  have hr := canonicalBoundaryAngular_bijective hA hz hs i
    (fun θ => (hroot θ).1) (fun θ => (hroot θ).2)
  have hG : Continuous G := hr.1.continuous.add continuous_const
  have hGinj : Function.Injective G := by
    intro θ η he
    apply hr.2.2.1.1
    exact add_right_cancel he
  have heq (θ : ℝ) : G (L.minusFlow z m c θ) = F θ := by
    cases side
    · change (K.chart z (K.cutPair m).1
        (C.left m, L.minusFlow z m (C.left m) θ)).2 + 0 = _
      rw [(hN03.2.2.2.2.1 z hz hs m θ).1, add_zero]
    · have hh := (canonicalRootAngles_of_n03Flows hS hT hN01 hN03 hA hB hz hs m θ).1
      have hh' : (K.chart z (K.cutPair m).2
          (C.right m, L.minusFlow z m (C.right m) θ)).2 =
        F θ - 2 * airyTravelPrimitive (K.cutRadius m) := hh
      change (K.chart z (K.cutPair m).2
        (C.right m, L.minusFlow z m (C.right m) θ)).2 +
          2 * airyTravelPrimitive (K.cutRadius m) = F θ
      linarith only [hh']
  exact bijective_and_continuous_invFun_of_scalar_equation hl.1.continuous
    (strictMono_of_deriv_pos hl.2.1) hl.2.2.1.2 hG hGinj heq

end ContinuousFlexibility.Analysis
