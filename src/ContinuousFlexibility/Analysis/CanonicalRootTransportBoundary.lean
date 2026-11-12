import ContinuousFlexibility.Analysis.CanonicalClosedTransport
import ContinuousFlexibility.Analysis.CanonicalClosedSymmetry
import ContinuousFlexibility.Analysis.CanonicalCutOrientation
import ContinuousFlexibility.Analysis.N04bRootHeightSymmetry

/-!
# Genuine geometry of transport at the physical root circles

Only the actual geometry and cut images are used. The paired orientations
make the transition Jacobian positive; its fixed root radius and degree-one
angular lift then make both diagonal derivatives positive. These are
consequences for the stored maps, not inputs on a future interpolation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem canonicalCutRoot_mem_closed_and_zero
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hcut : CanonicalCutGeometry S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    (c, θ) ∈ physicalPieceClosed S K z i ∧ (K.chart z i (c, θ)).1 = 0 := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  obtain ⟨_, _, _, _, _, hρ, hlL, hlR, hrL, hrR⟩ := hcut.1 m
  have hleft : K.left i = 0 := by cases side <;> assumption
  have hright : K.right i = K.cutRadius m := by cases side <;> assumption
  have hzero : K.inverseChart z i '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
      ({c} ×ˢ (univ : Set ℝ)) := by
    cases side
    · exact (hcut.2 z hz hs m).2.2.2.2.1
    · exact (hcut.2 z hz hs m).2.2.2.2.2
  have hpImage : (c, θ) ∈ K.inverseChart z i '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) := by
    rw [hzero]
    exact ⟨rfl, mem_univ _⟩
  obtain ⟨q, hq, hqp⟩ := hpImage
  have hq0 : q.1 = 0 := hq.1
  have hqC : q ∈ canonicalClosed S K i := by
    refine ⟨?_, mem_univ _⟩
    simpa only [Set.mem_Icc, hleft, hright, hq0] using
      And.intro (le_refl (0 : ℝ)) hρ.le
  have hboundary := hA.boundary z hz hs i
  have hF : K.chart z i (c, θ) = q := by
    simpa only [hqp] using hboundary.2.2.2.1 q hqC
  exact ⟨hqp ▸ hboundary.2.1 hqC, by rw [hF]; exact hq0⟩

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hA : CanonicalGeometry D S C K base ε)
  (hcut : CanonicalCutGeometry S C K base ε)
  (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
  (hs₀ : stateSector S C.referenceState)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ) (side : Bool)

include hA hcut hz₀ hs₀ hz hs

theorem canonicalCurrentPoint_root_radial (θ : ℝ) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    (canonicalCurrentPoint C K z i (c, θ)).1 = c := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  have hroot := canonicalCutRoot_mem_closed_and_zero hA hcut hz₀ hs₀ m side θ
  have hzero : K.inverseChart z i '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
      ({c} ×ˢ (univ : Set ℝ)) := by
    cases side
    · exact (hcut.2 z hz hs m).2.2.2.2.1
    · exact (hcut.2 z hz hs m).2.2.2.2.2
  have hmem := mem_image_of_mem (K.inverseChart z i)
    (show K.chart (C.referenceState, 0) i (c, θ) ∈
        ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) from ⟨hroot.2, mem_univ _⟩)
  rw [hzero] at hmem
  exact hmem.1

theorem canonicalCurrentPoint_root_jacobian_pos (θ : ℝ) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    0 < planeJacobian (canonicalCurrentPoint C K z i) (c, θ) := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  let p : PolarPoint := (c, θ)
  have hp := (canonicalCutRoot_mem_closed_and_zero hA hcut hz₀ hs₀ m side θ).1
  have hq := (hA.boundary _ hz₀ hs₀ i).1 hp
  have hx := n04Coordinates_currentPoint_mapsTo_closed hA hz₀ hs₀ hz hs i hp
  have hF := ((hA.boundary _ hz₀ hs₀ i).2.2.2.2.1 p hp).1
  have hG := n04b_inverseChart_contDiffAt_closed hA hz hs i hq
  have hJ : planeJacobian (canonicalCurrentPoint C K z i) p =
      (planeJacobian (K.chart z i) (canonicalCurrentPoint C K z i p))⁻¹ *
        planeJacobian (K.chart (C.referenceState, 0) i) p := by
    change planeJacobian (K.inverseChart z i ∘ K.chart (C.referenceState, 0) i) p = _
    rw [planeJacobian_comp (hF.differentiableAt (by simp))
      (hG.differentiableAt (by simp)), canonicalClosed_inverse_planeJacobian hA hz hs i hq]
  have href := canonicalCutPair_planeJacobian_signs hA hcut hz₀ hs₀ m
  have hcur := canonicalCutPair_planeJacobian_signs hA hcut hz hs m
  change 0 < planeJacobian (canonicalCurrentPoint C K z i) p
  rw [hJ]
  cases side
  · exact mul_pos (inv_pos.mpr (hcur.1 _ hx)) (href.1 _ hp)
  · have h := mul_pos (inv_pos.mpr (neg_pos.mpr (hcur.2 _ hx)))
      (neg_pos.mpr (href.2 _ hp))
    simpa only [inv_neg, neg_mul_neg] using h

theorem canonicalCurrentPoint_root_positive_diagonal (θ : ℝ) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    0 < radialPartial (fun p => (canonicalCurrentPoint C K z i p).1) (c, θ) ∧
      0 < angularPartial (fun p => (canonicalCurrentPoint C K z i p).2) (c, θ) := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  let F : PolarPoint → PolarPoint := canonicalCurrentPoint C K z i
  have hp (η : ℝ) :=
    (canonicalCutRoot_mem_closed_and_zero hA hcut hz₀ hs₀ m side η).1
  have hF (η : ℝ) : DifferentiableAt ℝ F (c, η) :=
    (n04Coordinates_currentPoint_contDiffAt_closed hA hz₀ hs₀ hz hs i (hp η)).differentiableAt
      (by simp)
  have hr (η : ℝ) : (F (c, η)).1 = c :=
    canonicalCurrentPoint_root_radial hA hcut hz₀ hs₀ hz hs m side η
  have hJ (η : ℝ) : 0 < planeJacobian F (c, η) :=
    canonicalCurrentPoint_root_jacobian_pos hA hcut hz₀ hs₀ hz hs m side η
  have hperiod (η : ℝ) : (F (c, η + Real.pi)).2 = (F (c, η)).2 + Real.pi := by
    have hq := (hA.boundary _ hz₀ hs₀ i).1 (hp η)
    have hFperiod := canonicalChart_periodic_on_closed hA hz₀ hs₀ i (hp η)
    have hGperiod := canonicalInverse_periodic_on_closed hA hz hs i hq
    have he : F ((c, η) + (0, Real.pi)) = F (c, η) + (0, Real.pi) := by
      change K.inverseChart z i (K.chart (C.referenceState, 0) i ((c, η) + (0, Real.pi))) = _
      rw [hFperiod]
      exact hGperiod
    simpa only [Prod.add_def, zero_add, add_zero] using congrArg Prod.snd he
  have hang := deriv_pos_of_periodic_lift_of_ne_zero Real.pi_pos hperiod
    (boundaryAngular_deriv_ne_zero hF (fun η => (hJ η).ne') hr) θ
  rw [(hasDerivAt_angular_slice (hF θ).snd).deriv] at hang
  have he : (fun η => (F (c, η)).1) = (fun _ : ℝ => c) := funext hr
  have hzero := (hasDerivAt_angular_slice (hF θ).fst).deriv
  rw [he, deriv_const] at hzero
  have hmul := hJ θ
  rw [n04b_planeJacobian_eq_componentPartials (hF θ), ← hzero, mul_zero, sub_zero] at hmul
  exact ⟨(mul_pos_iff_of_pos_right hang).mp hmul, hang⟩

end ContinuousFlexibility.Analysis
