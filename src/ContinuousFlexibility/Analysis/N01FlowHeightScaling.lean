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

local instance n01FlowHeightScalingStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

local instance n01FlowHeightScalingRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

theorem stateProfile_height_parameter_line
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (z : StateDirections S × ℝ) (η : HeightPair S) (t : ℝ) :
    stateProfile D S C (liftSectorParameter S C
      (z + t • heightParameterDirection S η)).1 =
      stateProfile D S C (liftSectorParameter S C z).1 := by
  have ht := liftSectorParameter_height_line_tail S C z η t
  exact stateProfile_eq_of_physical_coordinates
    (congrArg Prod.fst ht) (congrArg (fun v => v.2.1) ht)

private theorem height_scaling_scalar_parameter
    (S : PhysicalSpacesData) (z : StateDirections S × ℝ) (t : ℝ) :
    z + t • (z.2 • scalarParameterDirection S) = (z.1, z.2 + t * z.2) := by
  have hsmul : t • (z.2 • scalarParameterDirection S) =
      (t * z.2) • scalarParameterDirection S :=
    smul_smul t z.2 (scalarParameterDirection S)
  exact (congrArg (fun v : StateDirections S × ℝ => z + v) hsmul).trans
    (scalarParameter_line S z (t * z.2))

private theorem coefficients_eq_of_profile_and_height
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (x y : AnnularState S × ℝ)
    (hw : stateProfile D S C x.1 = stateProfile D S C y.1)
    (hh : stateHeight D S C x = stateHeight D S C y) :
    originalCoefficients D S C x = originalCoefficients D S C y :=
  congrArg₂ (fun (w : ℝ → ℝ) (h : PolarPoint → ℝ) =>
    (⟨polarLinearA w h, polarLinearB w h, polarCorrectedC w h⟩ : SymmetricCoefficients)) hw hh

private theorem scalar_height_scaling_identity (a q u t : ℝ) :
    a + q * (u + t * u) = a + (q + t * q) * u := by ring

theorem originalCoefficients_height_scaling
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (z : StateDirections S × ℝ) (t : ℝ) :
    originalCoefficients D S C (liftSectorParameter S C
      (z + t • heightParameterDirection S (liftSectorParameter S C z).1.1)) =
    originalCoefficients D S C (liftSectorParameter S C
      (z + t • (z.2 • scalarParameterDirection S))) := by
  let ξ : HeightPair S := (liftSectorParameter S C z).1.1
  let zL : AnnularState S × ℝ := liftSectorParameter S C (z + t • heightParameterDirection S ξ)
  let zR : AnnularState S × ℝ := ((liftSectorParameter S C z).1, z.2 + t * z.2)
  have hright : liftSectorParameter S C (z + t • (z.2 • scalarParameterDirection S)) = zR :=
    congrArg (liftSectorParameter S C) (height_scaling_scalar_parameter S z t)
  have hw : stateProfile D S C zL.1 = stateProfile D S C zR.1 :=
    stateProfile_height_parameter_line z ξ t
  have hrad : stateRadialHeight D S C zL.1 = stateRadialHeight D S C zR.1 := by
    funext r
    exact congrArg (fun w : ℝ → ℝ => ∫ a in D.b..r, w a) hw
  have hq : zL.2 = z.2 :=
    congrArg (fun y : AnnularState S × ℝ => y.2) (liftSectorParameter_height_line S C z ξ t)
  have hfield (p : PolarPoint) : stateU S zL.1 p =
      stateU S (liftSectorParameter S C z).1 p +
        t * stateU S (liftSectorParameter S C z).1 p :=
    liftSectorParameter_height_line_field S C z ξ t p
  have hh : stateHeight D S C zL = stateHeight D S C zR := by
    funext p
    change stateRadialHeight D S C zL.1 p.1 + zL.2 * stateU S zL.1 p =
      stateRadialHeight D S C zR.1 p.1 +
        (z.2 + t * z.2) * stateU S (liftSectorParameter S C z).1 p
    exact (congrArg₂ (fun a b : ℝ => a + b) (congrFun hrad p.1)
      (congrArg₂ (fun a b : ℝ => a * b) hq (hfield p))).trans
        (scalar_height_scaling_identity (stateRadialHeight D S C zR.1 p.1) z.2
          (stateU S (liftSectorParameter S C z).1 p) t)
  exact (coefficients_eq_of_profile_and_height zL zR hw hh).trans
    (congrArg (originalCoefficients D S C) hright.symm)

private theorem scalar_first_jet_smul
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (A : E [×1]→L[ℝ] ℝ) (c : ℝ) (w : E) :
    A (fun _ => c • w) = c * A (fun _ => w) := by
  simpa only [Fin.prod_univ_one, smul_eq_mul] using
    A.map_smul_univ (fun _ : Fin 1 => c) (fun _ : Fin 1 => w)

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
  let y : StateDirections S × ℝ :=
    z + t • heightParameterDirection S (liftSectorParameter S C z).1.1
  let y' : StateDirections S × ℝ := z + t • (z.2 • scalarParameterDirection S)
  have hy : liftSectorParameter S C y ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood hl le_rfl
  have hy' : liftSectorParameter S C y' ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood hr le_rfl
  have hsector : stateSector S (liftSectorParameter S C y).1 :=
    hN.2.2.1.liftSectorParameter_sector y
  have hcoeff : originalCoefficients D S C (liftSectorParameter S C y) =
      originalCoefficients D S C (liftSectorParameter S C y') :=
    originalCoefficients_height_scaling z t
  exact hN.minusFlow_eq_of_characteristic_speed hS hT hy hy' hsector m θ
    (fun r _ ψ => congrArg (fun L : SymmetricCoefficients =>
      minusCharacteristicSpeed L (r, ψ)) hcoeff)

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
  have hleft := J.deriv_line z
    (heightParameterDirection S (liftSectorParameter S C z).1.1) hz
  have hright := J.deriv_line z (z.2 • scalarParameterDirection S) hz
  exact hleft.symm.trans (hd.trans (hright.trans
    (scalar_first_jet_smul (J.D 1 z) z.2 (scalarParameterDirection S))))

end ContinuousFlexibility.Statements
