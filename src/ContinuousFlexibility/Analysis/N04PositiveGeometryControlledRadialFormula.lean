import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsControlled
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsBoundaryData

/-!
# The radial factors of the stored positive transports

The two factors are the displayed forward interpolation and its actual
radial inverse. Their finite kernel packets contain precisely the stored
pulled-back endpoint coefficients. These identities make the kernel
estimates applicable to the same transport used by the atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

namespace N04PositiveGeometryControlData

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

def radial (G : N04PositiveGeometryControlData W X n) (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : PolarPoint → ℝ :=
  endpointFiberPullbackCoordinate n (G.angle z i) (G.radialRepresentative z i)
    (n04PositiveLeft i) (n04PositiveRight i) (G.buffer.centerLeft i) (G.buffer.centerRight i)
    ((G.M i)⁻¹ / 2) (G.Mσ i)

def radialInverse (G : N04PositiveGeometryControlData W X n) (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) : PolarPoint → ℝ :=
  positiveFiberRadialInverse (G.radial z i)

theorem transport_eq_radial_angle (G : N04PositiveGeometryControlData W X n)
    (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (p : PolarPoint) :
    G.τ z i p = (G.radial z i (p.1, G.angle z i p), G.angle z i p) := rfl

theorem inverseTransport_eq_radial_angle (G : N04PositiveGeometryControlData W X n)
    (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (p : PolarPoint) :
    G.σ z i p = (G.radialInverse z i p,
      parameterizedCircleInverse (G.angle z i) (G.radialInverse z i p, p.2)) := rfl

end N04PositiveGeometryControlData

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

theorem n04PositiveGeometry_controlled_coefficients_contDiff
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) (j : ℕ) :
    ContDiff ℝ ∞ (G.toN04PositiveGeometryControlData.coefficients z i side j) := by
  rw [N04PositiveGeometryControlData.coefficients_eq_angularPullback]
  exact contDiff_radialBoundaryJet
    (contDiff_angularFiberPullback Real.pi_ne_zero
      (n04PositiveGeometry_controlled_angle_contDiff G hz hs i)
      (n04PositiveGeometry_controlled_radialRepresentative_contDiff G hz hs i side)
      (fun p => n04PositiveGeometry_controlled_angle_positive G hz hs i p.1 p.2)
      (n04PositiveGeometry_controlled_angle_period G hz hs i)) _ j

theorem n04PositiveGeometry_controlled_coefficients_zero
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) (θ : ℝ) :
    G.toN04PositiveGeometryControlData.coefficients z i side 0 θ =
      n04PositiveEndpoint i side := by
  have hsource := n04Coordinates_actualAtlas_positiveEndpoint_of_source
    W.hT W.hS W.through03 W.field X.e₀ (X.src i side)
    (stateNeighborhood_mono W.S W.C G.base_le G.radius_le hz) hs
  have hv (α : ℝ) : G.toN04PositiveGeometryControlData.radialRepresentative z i side
      (n04PositiveEndpoint i side, α) = n04PositiveEndpoint i side := by
    have he := radialBoundaryJet_oneSidedBoundaryTaylorRepresentative
      (fun p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).1)
      (n + 1) (n04PositiveEndpoint i side) (k := 0) (Nat.zero_le _) α
    have he' : G.toN04PositiveGeometryControlData.radialRepresentative z i side
        (n04PositiveEndpoint i side, α) =
      (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z (n04PositiveEndpoint i side, α)).1 := he
    exact he'.trans (hsource.root_radial α)
  rw [N04PositiveGeometryControlData.coefficients_eq_angularPullback]
  exact angularFiberPullback_boundary (φ := G.toN04PositiveGeometryControlData.angle z i) hv θ

theorem n04PositiveGeometry_controlled_radial_eq_kernel
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (p : PolarPoint) :
    G.toN04PositiveGeometryControlData.radial z i p =
      G.toN04PositiveGeometryControlData.radialKernel i
        ((fun side j => G.toN04PositiveGeometryControlData.coefficients z i side (j + 1) p.2),
          p.1) :=
  n04PositiveGeometry_radialKernel_eq (n04PositiveLeft i) (n04PositiveRight i)
    (G.buffer.centerLeft i) (G.buffer.centerRight i)
    (endpointFiberWidths n (n04PositiveLeft i) (n04PositiveRight i)
      (G.buffer.centerLeft i) (G.buffer.centerRight i) ((G.M i)⁻¹ / 2) (G.Mσ i))
    (G.toN04PositiveGeometryControlData.coefficients z i)
    (fun side j _ => n04PositiveGeometry_controlled_coefficients_contDiff G hz hs i side j)
    (fun side θ => n04PositiveGeometry_controlled_coefficients_zero G hz hs i side θ) p.1 p.2

theorem n04PositiveGeometry_controlled_radialInverse_eq_kernel
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (p : PolarPoint) :
    G.toN04PositiveGeometryControlData.radialInverse z i p =
      G.toN04PositiveGeometryControlData.radialInverseKernel i
        ((fun side j => G.toN04PositiveGeometryControlData.coefficients z i side (j + 1) p.2),
          p.1) := by
  exact congrArg (fun f : ℝ → ℝ => Function.invFun f p.1)
    (funext (fun r => n04PositiveGeometry_controlled_radial_eq_kernel G hz hs i (r, p.2)))

end ContinuousFlexibility.Analysis
