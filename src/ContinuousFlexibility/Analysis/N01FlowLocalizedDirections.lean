import ContinuousFlexibility.Analysis.N01FlowHeightScaling
import ContinuousFlexibility.Analysis.SmoothDirectionsLocalDirections

/-!
# Actual localization of height directions in every N01 parameter jet

Only the infinitesimal height direction is localized. Both parameter
lines stay near their common base point, so the construction does not
require a cutoff-modified base state to belong to the N01 neighborhood.
Actual ODE locality identifies their angular-flow functions; the genuine
directional tower then identifies every further mixed parameter jet.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.ordinaryFlowFamily_height_line_locality_eventually
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (η ξ : HeightPair S) (m b : ℕ) (θ : ℝ)
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (hηξ : ∀ s ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      heightPairField S η (s, ψ) = heightPairField S ξ (s, ψ)) :
    (fun t : ℝ => ordinaryFlowFamily S C m 0 b (r, θ)
      (liftSectorParameter S C (z + t • heightParameterDirection S η))) =ᶠ[𝓝 0]
    (fun t : ℝ => ordinaryFlowFamily S C m 0 b (r, θ)
      (liftSectorParameter S C (z + t • heightParameterDirection S ξ))) := by
  filter_upwards [sectorParameter_line_eventually_mem hz (heightParameterDirection S η),
    sectorParameter_line_eventually_mem hz (heightParameterDirection S ξ)] with t hη hξ
  have htail :
      (liftSectorParameter S C (z + t • heightParameterDirection S η)).1.2 =
      (liftSectorParameter S C (z + t • heightParameterDirection S ξ)).1.2 := by
    rw [liftSectorParameter_height_line_tail, liftSectorParameter_height_line_tail]
  have hq :
      (liftSectorParameter S C (z + t • heightParameterDirection S η)).2 =
      (liftSectorParameter S C (z + t • heightParameterDirection S ξ)).2 := by
    rw [liftSectorParameter_height_line, liftSectorParameter_height_line]
  have hu : ∀ s ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      stateU S (liftSectorParameter S C (z + t • heightParameterDirection S η)).1 (s, ψ) =
      stateU S (liftSectorParameter S C (z + t • heightParameterDirection S ξ)).1 (s, ψ) := by
    intro s hs ψ
    rw [liftSectorParameter_height_line_field, liftSectorParameter_height_line_field,
      hηξ s hs ψ]
  have hflow (ψ : ℝ) := hN.minusFlow_eq_of_height_locality hS hT
    (liftSectorParameter_mem_stateNeighborhood hη le_rfl)
    (liftSectorParameter_mem_stateNeighborhood hξ le_rfl)
    (hN.2.2.1.liftSectorParameter_sector _)
    (congrArg Prod.fst htail) (congrArg (fun v => v.2.1) htail) hq m hu ψ hr
  have heq :
      (fun ψ => C.minusFlow (liftSectorParameter S C
        (z + t • heightParameterDirection S η)) m r ψ -
          C.minusFlow (C.referenceState, 0) m r ψ) =
      (fun ψ => C.minusFlow (liftSectorParameter S C
        (z + t • heightParameterDirection S ξ)) m r ψ -
          C.minusFlow (C.referenceState, 0) m r ψ) := by
    funext ψ
    exact congrArg (fun y => y - C.minusFlow (C.referenceState, 0) m r ψ) (hflow ψ)
  simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero] using
    congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ) heq

theorem N01Properties.ordinaryFlowFamily_first_height_jet_locality
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (η ξ : HeightPair S) (m b : ℕ) (θ : ℝ)
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (hηξ : ∀ s ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      heightPairField S η (s, ψ) = heightPairField S ξ (s, ψ))
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y))) :
    J.D 1 z (fun _ => heightParameterDirection S η) =
      J.D 1 z (fun _ => heightParameterDirection S ξ) := by
  have heq := (hN.ordinaryFlowFamily_height_line_locality_eventually
    hS hT hz η ξ m b θ hr hηξ).deriv_eq
  exact (J.deriv_line z (heightParameterDirection S η) hz).symm.trans
    (heq.trans (J.deriv_line z (heightParameterDirection S ξ) hz))

/-- The same actual physical cutoff can be used in every parameter
derivative, with all other directions left unchanged. -/
theorem N01Properties.ordinaryFlowFamily_height_jet_locality
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (η ξ : HeightPair S) (m b : ℕ) (θ : ℝ)
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (hηξ : ∀ s ∈ Ioo (C.left m) (C.right m), ∀ ψ,
      heightPairField S η (s, ψ) = heightPairField S ξ (s, ψ))
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y)))
    (n : ℕ) (v : Fin n → (StateDirections S × ℝ)) :
    J.D (n + 1) z (Fin.snoc v (heightParameterDirection S η)) =
      J.D (n + 1) z (Fin.snoc v (heightParameterDirection S ξ)) := by
  exact J.snoc_jet_eq_of_first_jet_eq
    (heightParameterDirection S η) (heightParameterDirection S ξ)
    (fun y hy => hN.ordinaryFlowFamily_first_height_jet_locality
      hS hT hy η ξ m b θ hr hηξ J) n z hz v

end ContinuousFlexibility.Statements
