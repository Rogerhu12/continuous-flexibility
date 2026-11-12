import ContinuousFlexibility.Analysis.ActualReferenceNegativeRadialFields
import ContinuousFlexibility.Analysis.CanonicalRootTransportBoundary
import ContinuousFlexibility.Analysis.N04bActualAtlasCuts

/-!
# Actual reference data at a negative root circle

Both orientations use the same stored actual atlas. Its open radial
identities pass to the genuine root circle by ordinary continuity.
The angular identity and the established cut orientation determine the
strict sign of the actual radial derivative there. No radiality outside
the negative component, or common smooth collar for all orders, is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Full ordinary smoothness, exact root values, positive height and the
inward signed radial derivative of the original reference chart.
The two height values on a root circle are equal by actual one-sided
continuity, not by a choice of a radial extension. -/
theorem n04Coordinates_actual_reference_negative_endpoint_data
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (m : ℕ) (side : Bool) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := e.symm (.inl (m, side))
    let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
    let c := if side then C.right m else C.left m
    let σ : ℝ := if side then -1 else 1
    (∀ θ : ℝ, ContDiffAt ℝ ∞ (K.chart z₀ k) (c, θ) ∧
      ContDiffAt ℝ ∞ (K.height z₀ k) (c, θ) ∧
      K.chart z₀ k (c, θ) = (0, θ) ∧
      0 < K.height z₀ k (c, θ) ∧
      K.height z₀ k (c, θ) = K.height z₀ k (c, 0)) ∧
    0 < σ * deriv (fun r : ℝ => (K.chart z₀ k (r, 0)).1) c := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := e.symm (.inl (m, side))
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let c := if side then C.right m else C.left m
  let σ : ℝ := if side then -1 else 1
  let Ω := Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
  have hz₀ : z₀ ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hs₀ : stateSector S z₀.1 := hN.1.1.2.2.1.stateSector
  have hA : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hcut : CanonicalCutGeometry S C K base ε :=
    n04bActualTypedAtlas_cutGeometry hT hS hN hfield e
  have hi : (if side then (K.cutPair m).2 else (K.cutPair m).1) = k := by
    cases side <;> rfl
  have hroot (θ : ℝ) :
      (c, θ) ∈ physicalPieceClosed S K z₀ k ∧ (K.chart z₀ k (c, θ)).1 = 0 := by
    simpa only [hi] using
      canonicalCutRoot_mem_closed_and_zero hA hcut hz₀ hs₀ m side θ
  have hreg (θ : ℝ) :
      ContDiffAt ℝ ∞ (K.chart z₀ k) (c, θ) ∧
        ContDiffAt ℝ ∞ (K.height z₀ k) (c, θ) ∧
        planeJacobian (K.chart z₀ k) (c, θ) ≠ 0 ∧
        0 < K.height z₀ k (c, θ) :=
    (hA.boundary z₀ hz₀ hs₀ k).2.2.2.2.1 _ (hroot θ).1
  have hopen := n04Coordinates_actual_reference_negative_radial_fields
    hT hS hN hfield e m side
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hc : c ∈ Icc (C.left m) (C.right m) := by
    cases side
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  have hcl (θ : ℝ) : (c, θ) ∈ closure Ω := by
    rw [show Ω = Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) from rfl,
      closure_prod_eq, closure_Ioo hab.ne, closure_univ]
    exact ⟨hc, mem_univ _⟩
  have hangle (θ : ℝ) : (K.chart z₀ k (c, θ)).2 = θ := by
    apply sub_eq_zero.mp
    exact ((hreg θ).1.snd.continuousAt.sub continuousAt_snd).continuousWithinAt
      |>.eq_const_of_mem_closure (hcl θ) (fun p hp => by
        apply sub_eq_zero.mpr
        exact congrArg Prod.snd (hopen.2.2.1 p hp))
  have hcircle (θ : ℝ) : K.chart z₀ k (c, θ) = (0, θ) :=
    Prod.ext (hroot θ).2 (hangle θ)
  have hheight (θ : ℝ) : K.height z₀ k (c, θ) = K.height z₀ k (c, 0) := by
    have hzero : ContinuousAt (fun p : PolarPoint => (p.1, (0 : ℝ))) (c, θ) :=
      (continuous_fst.prodMk continuous_const).continuousAt
    have hr : ContinuousAt (fun p : PolarPoint => K.height z₀ k (p.1, 0)) (c, θ) :=
      (hreg 0).2.1.continuousAt.comp hzero
    apply sub_eq_zero.mp
    exact ((hreg θ).2.1.continuousAt.sub hr).continuousWithinAt
      |>.eq_const_of_mem_closure (hcl θ) (fun p hp =>
        sub_eq_zero.mpr (hopen.2.2.2.1 p hp))
  refine ⟨fun θ => ⟨(hreg θ).1, (hreg θ).2.1, hcircle θ,
    (hreg θ).2.2.2, hheight θ⟩, ?_⟩
  have hF : DifferentiableAt ℝ (K.chart z₀ k) (c, 0) :=
    (hreg 0).1.differentiableAt (by simp)
  have hfirst : (fun θ : ℝ => (K.chart z₀ k (c, θ)).1) = (fun _ : ℝ => 0) :=
    funext (fun θ => congrArg Prod.fst (hcircle θ))
  have hsecond : (fun θ : ℝ => (K.chart z₀ k (c, θ)).2) = (id : ℝ → ℝ) :=
    funext hangle
  have hd₁ := (hasDerivAt_angular_slice hF.fst).deriv
  have hd₂ := (hasDerivAt_angular_slice hF.snd).deriv
  rw [hfirst, deriv_const] at hd₁
  rw [hsecond, deriv_id] at hd₂
  have hJ : planeJacobian (K.chart z₀ k) (c, 0) =
      deriv (fun r : ℝ => (K.chart z₀ k (r, 0)).1) c := by
    rw [n04b_planeJacobian_eq_componentPartials hF, ← hd₁, ← hd₂,
      mul_one, mul_zero, sub_zero]
    exact (hasDerivAt_radial_slice hF.fst).deriv.symm
  rw [← hJ]
  have hsign := canonicalCutPair_planeJacobian_signs hA hcut hz₀ hs₀ m
  cases side
  · simpa only [σ, Bool.false_eq_true, ↓reduceIte, one_mul] using
      hsign.1 (c, 0) (hroot 0).1
  · simpa only [σ, Bool.true_eq_true, ↓reduceIte, neg_one_mul, neg_pos] using
      hsign.2 (c, 0) (hroot 0).1

end ContinuousFlexibility.Analysis

