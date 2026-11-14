module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFamily
public import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundary
public import ContinuousFlexibility.Analysis.N04RealizationOneSidedAngularPositivity

/-!
# The literal finite data of the chosen angular inverse at the roots

The angular interpolation has the same full boundary jets as the
original endpoint source. Its boundary inverse is exactly the original
forward N01 root label. Thus the finite inverse pullback is evaluated on
the already controlled root data, without a new angular extension or a
componentwise compactness constant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

namespace N04PositiveGeometryControlData

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

def angle (G : N04PositiveGeometryControlData W X n) (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : PolarPoint → ℝ :=
  wholeComponentEndpointAngle n
    (oneSidedEndpointRepresentative (n + 2) (n04PositiveLeft i) (n04PositiveRight i)
      (fun side p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).2))
    (n04PositiveLeft i) (n04PositiveRight i) (G.buffer.centerLeft i) (G.buffer.centerRight i)
    (G.M i)⁻¹ (G.M i)

def radialRepresentative (G : N04PositiveGeometryControlData W X n)
    (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) : PolarPoint → ℝ :=
  oneSidedEndpointRepresentative (n + 1) (n04PositiveLeft i) (n04PositiveRight i)
    (fun side p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).1) side

theorem angle_eq_transport_snd (G : N04PositiveGeometryControlData W X n)
    (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    G.angle z i = fun p => (G.τ z i p).2 := rfl

theorem coefficients_eq_angularPullback (G : N04PositiveGeometryControlData W X n)
    (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) :
    G.coefficients z i side = radialBoundaryJet
      (angularFiberPullback (G.angle z i) (G.radialRepresentative z i side))
      (if side then n04PositiveRight i else n04PositiveLeft i) := rfl

end N04PositiveGeometryControlData

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

private theorem controlled_boundary_source_data
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) :
    OneSidedTransportEndpoint
      (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z)
      (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z)
      (n04PositiveSourceLeft (X.src i side)) (n04PositiveSourceRight (X.src i side))
      (if side then n04PositiveRight i else n04PositiveLeft i) :=
  n04Coordinates_actualAtlas_positiveEndpoint_of_source W.hT W.hS W.through03 W.field X.e₀
    (X.src i side) (stateNeighborhood_mono W.S W.C G.base_le G.radius_le hz) hs

theorem n04PositiveGeometry_controlled_angle_contDiff
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    ContDiff ℝ ∞ (G.toN04PositiveGeometryControlData.angle z i) :=
  (G.matching z hz hs i).geometry.smooth.snd

theorem n04PositiveGeometry_controlled_radialRepresentative_contDiff
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) :
    ContDiff ℝ ∞ (G.toN04PositiveGeometryControlData.radialRepresentative z i side) :=
  contDiff_oneSidedBoundaryTaylorRepresentative _
    (fun θ => ((controlled_boundary_source_data G hz hs i side).root_smooth θ).fst) _

/-- The finite radial representative retains the source's full
ordinary jets, including its mixed angular evaluations. -/
theorem n04PositiveGeometry_controlled_radialRepresentative_boundary_jets
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (side : Bool) (k : ℕ) (hk : k ≤ n + 1) (θ : ℝ) :
    iteratedFDeriv ℝ k (G.toN04PositiveGeometryControlData.radialRepresentative z i side)
        (if side then n04PositiveRight i else n04PositiveLeft i, θ) =
      iteratedFDeriv ℝ k (fun p =>
        (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).1)
        (if side then n04PositiveRight i else n04PositiveLeft i, θ) := by
  have hsource := controlled_boundary_source_data G hz hs i side
  exact iteratedFDeriv_oneSidedBoundaryTaylorRepresentative hsource.interval
    hsource.smooth_on.fst hsource.endpoint (fun θ => (hsource.root_smooth θ).fst)
    (n + 1) hk θ

theorem n04PositiveGeometry_controlled_angle_positive
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (r θ : ℝ) :
    0 < deriv (fun η => G.toN04PositiveGeometryControlData.angle z i (r, η)) θ := by
  have ho := G.buffer.ordered i
  exact n04Realization_oneSidedTransport_angle_positive n ho.1
    (ho.2.1.trans (ho.2.2.1.trans ho.2.2.2.1)) ho.2.2.2.2
    (inv_pos.mpr (zero_lt_one.trans_le (G.input_one i)))
    (inv_le_one_of_one_le₀ (G.input_one i)) (zero_le_one.trans (G.input_one i))
    (controlled_boundary_source_data G hz hs i) (G.endpoint_bounds z hz hs i) r θ

theorem n04PositiveGeometry_controlled_angle_period
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (r θ : ℝ) :
    G.toN04PositiveGeometryControlData.angle z i (r, θ + Real.pi) =
      G.toN04PositiveGeometryControlData.angle z i (r, θ) + Real.pi := by
  have h := congrArg Prod.snd ((G.matching z hz hs i).geometry.period_add (r, θ))
  simpa only [N04PositiveGeometryControlData.angle_eq_transport_snd,
    Prod.mk_add_mk, add_zero, Prod.snd_add] using h

/-- The full finite ordinary jet agrees, not only its radial evaluation. -/
theorem n04PositiveGeometry_controlled_angle_boundary_jets
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (side : Bool) (k : ℕ) (hk : k ≤ n + 1) (θ : ℝ) :
    iteratedFDeriv ℝ k (G.toN04PositiveGeometryControlData.angle z i)
        (if side then n04PositiveRight i else n04PositiveLeft i, θ) =
      iteratedFDeriv ℝ k (fun p =>
        (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).2)
        (if side then n04PositiveRight i else n04PositiveLeft i, θ) := by
  let L : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have ht : ContDiffAt ℝ ∞ (G.toN04PositiveGeometryControlData.τ z i)
      (if side then n04PositiveRight i else n04PositiveLeft i, θ) :=
    (G.matching z hz hs i).geometry.smooth.contDiffAt
  have hf := (controlled_boundary_source_data G hz hs i side).root_smooth θ
  have he := (G.matching z hz hs i).coordinate_jets side k hk θ
  calc
    _ = L.compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (G.toN04PositiveGeometryControlData.τ z i)
          (if side then n04PositiveRight i else n04PositiveLeft i, θ)) := by
      simpa only [L, ContinuousLinearMap.coe_snd', Function.comp_def,
        N04PositiveGeometryControlData.angle_eq_transport_snd] using
        L.iteratedFDeriv_comp_left ht (by simp : (k : ℕ∞ω) ≤ ∞)
    _ = L.compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z)
          (if side then n04PositiveRight i else n04PositiveLeft i, θ)) :=
      congrArg L.compContinuousMultilinearMap he
    _ = _ := by
      simpa only [L, ContinuousLinearMap.coe_snd', Function.comp_def] using
        (L.iteratedFDeriv_comp_left hf (by simp : (k : ℕ∞ω) ≤ ∞)).symm

/-- The actual inverse angular boundary point is the original forward
label of the supplied adjacent component. -/
theorem n04PositiveGeometry_controlled_angle_inverse_boundary
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (side : Bool) (m : ℕ) (hsource : (X.src i side).val = some m) (θ : ℝ) :
    parameterizedCircleInverse (G.toN04PositiveGeometryControlData.angle z i)
      (if side then n04PositiveRight i else n04PositiveLeft i, θ) =
        n01RootLabel W.S W.C z m (!side) θ := by
  have hzW := stateNeighborhood_mono W.S W.C G.base_le G.radius_le hz
  let β := n01RootLabel W.S W.C z m (!side)
  have hβ : Function.Bijective β := by
    have h := n04b_actualTravel_endpoint_bijections W.through03 W.hS hzW hs m
    cases side with
    | false => exact h.2
    | true => exact h.1
  have hboundary (η : ℝ) : G.toN04PositiveGeometryControlData.angle z i
      (if side then n04PositiveRight i else n04PositiveLeft i, η) = Function.invFun β η := by
    have he := congrArg (fun A : PolarPoint [×0]→L[ℝ] ℝ => A Fin.elim0)
      (n04PositiveGeometry_controlled_angle_boundary_jets G hz hs i side 0 (Nat.zero_le _) η)
    have hsourceValue := congrArg Prod.snd
      (n04PositiveGeometry_source_endpoint_value W X i side m hsource hzW hs η)
    have he' : G.toN04PositiveGeometryControlData.angle z i
        (if side then n04PositiveRight i else n04PositiveLeft i, η) =
      (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z
        (if side then n04PositiveRight i else n04PositiveLeft i, η)).2 := by
      simpa only [iteratedFDeriv_zero_apply] using he
    exact he'.trans hsourceValue
  change Function.invFun
    (fun η => G.toN04PositiveGeometryControlData.angle z i
      (if side then n04PositiveRight i else n04PositiveLeft i, η)) θ = β θ
  rw [funext hboundary]
  have hleft : Function.LeftInverse β (Function.invFun β) :=
    Function.rightInverse_invFun hβ.2
  have hinv := Function.leftInverse_invFun hleft.injective (β θ)
  rw [Function.leftInverse_invFun hβ.1 θ] at hinv
  exact hinv

end ContinuousFlexibility.Analysis
