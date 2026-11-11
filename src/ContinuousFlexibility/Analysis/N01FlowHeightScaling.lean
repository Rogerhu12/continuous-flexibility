import ContinuousFlexibility.Analysis.HeightSectorDirections
import ContinuousFlexibility.Analysis.N01FlowLocality
import ContinuousFlexibility.Analysis.SmoothDirectionsMixedScalarLine

/-!
# Actual height scaling in the N01 characteristic flow

Multiplying the full physical height by `1 + t` has precisely the same
effect as multiplying the scalar height parameter by `1 + t`.  ODE
uniqueness proves this identity for the actual flow, including each
closed radial endpoint.  Differentiating it identifies the genuine
height and scalar directions of every angular-flow jet.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

theorem stateProfile_height_parameter_line
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (z : StateDirections S × ℝ) (η : HeightPair S) (t : ℝ) :
    stateProfile D S C (liftSectorParameter S C
      (z + t • heightParameterDirection S η)).1 =
      stateProfile D S C (liftSectorParameter S C z).1 := by
  have ht := liftSectorParameter_height_line_tail S C z η t
  exact stateProfile_eq_of_physical_coordinates
    (congrArg Prod.fst ht) (congrArg (fun v => v.2.1) ht)

theorem originalCoefficients_height_scaling
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (z : StateDirections S × ℝ) (t : ℝ) :
    originalCoefficients D S C (liftSectorParameter S C
      (z + t • heightParameterDirection S (liftSectorParameter S C z).1.1)) =
    originalCoefficients D S C (liftSectorParameter S C
      (z + t • (z.2 • scalarParameterDirection S))) := by
  have hw : stateProfile D S C (liftSectorParameter S C
      (z + t • heightParameterDirection S (liftSectorParameter S C z).1.1)).1 =
      stateProfile D S C (liftSectorParameter S C
        (z + t • (z.2 • scalarParameterDirection S))).1 := by
    rw [smul_smul, liftSectorParameter_scalar_line]
    exact stateProfile_height_parameter_line z _ t
  have hh : stateHeight D S C (liftSectorParameter S C
      (z + t • heightParameterDirection S (liftSectorParameter S C z).1.1)) =
      stateHeight D S C (liftSectorParameter S C
        (z + t • (z.2 • scalarParameterDirection S))) := by
    funext p
    have hfield := liftSectorParameter_height_line_field S C z
      (liftSectorParameter S C z).1.1 t p
    change stateU S (liftSectorParameter S C
      (z + t • heightParameterDirection S (liftSectorParameter S C z).1.1)).1 p =
      stateU S (liftSectorParameter S C z).1 p +
        t * stateU S (liftSectorParameter S C z).1 p at hfield
    simp only [stateHeight, stateRadialHeight, hw, hfield]
    rw [smul_smul, liftSectorParameter_scalar_line]
    have hq : (liftSectorParameter S C
        (z + t • heightParameterDirection S (liftSectorParameter S C z).1.1)).2 = z.2 := by
      rw [liftSectorParameter_height_line]
    rw [hq]
    ring
  simp only [originalCoefficients, hw, hh]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.minusFlow_height_scaling
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (t : ℝ)
    (hl : z + t • heightParameterDirection S (liftSectorParameter S C z).1.1 ∈
      sectorNeighborhood S base ε ε)
    (hr : z + t • (z.2 • scalarParameterDirection S) ∈
      sectorNeighborhood S base ε ε) (m : ℕ) (θ : ℝ) :
    EqOn
      (fun r => C.minusFlow (liftSectorParameter S C
        (z + t • heightParameterDirection S (liftSectorParameter S C z).1.1)) m r θ)
      (fun r => C.minusFlow (liftSectorParameter S C
        (z + t • (z.2 • scalarParameterDirection S))) m r θ)
      (Icc (C.left m) (C.right m)) := by
  apply hN.minusFlow_eq_of_characteristic_speed hS hT
    (liftSectorParameter_mem_stateNeighborhood hl le_rfl)
    (liftSectorParameter_mem_stateNeighborhood hr le_rfl)
    (hN.2.2.1.liftSectorParameter_sector _) m θ
  intro r hr' ψ
  rw [originalCoefficients_height_scaling]

/-- This is an identity of the actual angular derivatives of the same
flow; no formal angular jet is introduced. -/
theorem N01Properties.ordinaryFlowFamily_height_scaling_eventually
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (m b : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    (fun t : ℝ => ordinaryFlowFamily S C m 0 b (r, θ)
      (liftSectorParameter S C
        (z + t • heightParameterDirection S (liftSectorParameter S C z).1.1))) =ᶠ[𝓝 0]
    (fun t : ℝ => ordinaryFlowFamily S C m 0 b (r, θ)
      (liftSectorParameter S C (z + t • (z.2 • scalarParameterDirection S)))) := by
  filter_upwards [sectorParameter_line_eventually_mem hz
      (heightParameterDirection S (liftSectorParameter S C z).1.1),
    sectorParameter_line_eventually_mem hz (z.2 • scalarParameterDirection S)] with t hl ht
  have heq :
      (fun ψ => C.minusFlow (liftSectorParameter S C
        (z + t • heightParameterDirection S (liftSectorParameter S C z).1.1)) m r ψ -
          C.minusFlow (C.referenceState, 0) m r ψ) =
      (fun ψ => C.minusFlow (liftSectorParameter S C
        (z + t • (z.2 • scalarParameterDirection S))) m r ψ -
          C.minusFlow (C.referenceState, 0) m r ψ) := by
    funext ψ
    exact congrArg (fun y => y - C.minusFlow (C.referenceState, 0) m r ψ)
      (hN.minusFlow_height_scaling hS hT z t hl ht m ψ hr)
  simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero] using
    congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ) heq

/-- Euler's identity is proved from genuine derivatives of the actual
flow.  Its height direction contains the full physical height at `z`.
It is therefore available for subsequent physical localization. -/
theorem N01Properties.ordinaryFlowFamily_height_scalar_jet
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (m b : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y))) :
    J.D 1 z (fun _ => heightParameterDirection S (liftSectorParameter S C z).1.1) =
      z.2 * J.D 1 z (fun _ => scalarParameterDirection S) := by
  have hd := (hN.ordinaryFlowFamily_height_scaling_eventually hS hT hz m b θ hr).deriv_eq
  rw [J.deriv_line z _ hz, J.deriv_line z _ hz] at hd
  have hscale := (J.D 1 z).map_smul_univ (fun _ : Fin 1 => z.2)
    (fun _ : Fin 1 => scalarParameterDirection S)
  simpa only [Fin.prod_univ_one, smul_eq_mul] using hd.trans hscale

end ContinuousFlexibility.Statements
