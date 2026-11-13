import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsAngularSmall
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsKernelSlope
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsRadial

/-!
# The finite coefficient kernel of the actual angular interpolation

The angular displacement is a fixed finite kernel of the actual
endpoint displacements and the physical radius. Its ordinary jets have
uniform material powers; only the displayed reciprocal angular width
is charged. The unwrapped angle is added afterwards and is never put
inside a coefficient envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

def n04PositiveGeometry_angularPatchKernel (n : ℕ) (c δ : ℝ)
    (a : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin (n + 1),
    (positiveEndpointCutoff c δ x *
      ((x - c) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ))) * a j

def n04PositiveGeometry_angularKernel (n : ℕ) (l r δ : ℝ)
    (p : N04PositiveRadialCoefficients n × ℝ) : ℝ :=
  n04PositiveGeometry_angularPatchKernel n l δ (p.1 false) p.2 +
    n04PositiveGeometry_angularPatchKernel n r δ (p.1 true) p.2

theorem n04PositiveGeometry_angularKernel_formula
    (n : ℕ) (l r δ x θ : ℝ) (A : Bool → ℕ → ℝ → ℝ) :
    positiveAngularTaylorInterpolation n l r δ A (x, θ) =
      θ + n04PositiveGeometry_angularKernel n l r δ
        ((fun side (j : Fin (n + 1)) => A side j θ -
          if (j : ℕ) = 0 then θ else 0), x) := by
  have hleft := n04PositiveGeometry_angular_patch_displacement_sum n l δ x θ (A false)
  have hright := n04PositiveGeometry_angular_patch_displacement_sum n r δ x θ (A true)
  change positiveAngularTaylorPatch n l δ (A false) (x, θ) +
    positiveAngularTaylorPatch n r δ (A true) (x, θ) - θ =
      θ + (n04PositiveGeometry_angularPatchKernel n l δ
        (fun j => A false j θ - if (j : ℕ) = 0 then θ else 0) x +
        n04PositiveGeometry_angularPatchKernel n r δ
          (fun j => A true j θ - if (j : ℕ) = 0 then θ else 0) x)
  change positiveAngularTaylorPatch n l δ (A false) (x, θ) - θ =
    n04PositiveGeometry_angularPatchKernel n l δ
      (fun j => A false j θ - if (j : ℕ) = 0 then θ else 0) x at hleft
  change positiveAngularTaylorPatch n r δ (A true) (x, θ) - θ =
    n04PositiveGeometry_angularPatchKernel n r δ
      (fun j => A true j θ - if (j : ℕ) = 0 then θ else 0) x at hright
  linarith only [hleft, hright]

private theorem angularPatchKernel_bounds
    {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : I → ℝ} {p : I → E} (hW : ∀ i, 1 ≤ W i) (n : ℕ)
    (a : I → E → Fin (n + 1) → ℝ) (x : I → E → ℝ) (c δ : I → ℝ)
    (ha : ∀ j, N04PositiveKernelJetBounds W p (fun i y => a i y j))
    (hx : N04PositiveKernelJetBounds W p x)
    (hc : HasPositiveEnvelope W (fun i => |c i|))
    (hδ : HasPositiveEnvelope W (fun i => |(δ i)⁻¹|)) :
    N04PositiveKernelJetBounds W p
      (fun i y => n04PositiveGeometry_angularPatchKernel n (c i) (δ i) (a i y) (x i y)) := by
  have hcut := n04PositiveGeometry_endpointCutoffKernel_bounds hW x c δ hx hc hδ
  have hshift := hx.sub (N04PositiveKernelJetBounds.const (p := p) hW c hc) hW
  have hterm (j : Fin (n + 1)) : N04PositiveKernelJetBounds W p
      (fun i y => (positiveEndpointCutoff (c i) (δ i) (x i y) *
        ((x i y - c i) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ))) * a i y j) := by
    have hfactor := N04PositiveKernelJetBounds.const (p := p) hW
      (fun _ => (((j : ℕ).factorial : ℝ))⁻¹)
      (hasPositiveEnvelope_const W hW |(((j : ℕ).factorial : ℝ))⁻¹|)
    simpa only [div_eq_mul_inv] using
      (hcut.mul ((hshift.pow hW j).mul hfactor hW) hW).mul (ha j) hW
  exact N04PositiveKernelJetBounds.sum hW Finset.univ
    (fun j i y => (positiveEndpointCutoff (c i) (δ i) (x i y) *
      ((x i y - c i) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ))) * a i y j)
    (fun j _ => hterm j)

/-- All ordinary coefficient/radial derivatives of the displayed
angular kernel have a common sampled material envelope. The arbitrary
index may include the component, state and evaluation point. -/
theorem n04PositiveGeometry_angularKernel_bounds
    {I : Type*} {W : I → ℝ} (hW : ∀ i, 1 ≤ W i)
    (n : ℕ) (p : I → N04PositiveRadialCoefficients n × ℝ)
    (l r δ : I → ℝ)
    (hp : HasPositiveEnvelope W (fun i => ‖p i‖))
    (hl : HasPositiveEnvelope W (fun i => |l i|))
    (hr : HasPositiveEnvelope W (fun i => |r i|))
    (hδ : HasPositiveEnvelope W (fun i => |(δ i)⁻¹|)) :
    N04PositiveKernelJetBounds W p
      (fun i => n04PositiveGeometry_angularKernel n (l i) (r i) (δ i)) := by
  let Q := N04PositiveRadialCoefficients n × ℝ
  have ha (side : Bool) (j : Fin (n + 1)) : N04PositiveKernelJetBounds W p
      (fun _ (y : Q) => y.1 side j) := by
    let L : Q →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
      ((ContinuousLinearMap.proj side).comp
        (ContinuousLinearMap.fst ℝ (N04PositiveRadialCoefficients n) ℝ))
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_fst'] using N04PositiveKernelJetBounds.linear hW L hp
  have hx : N04PositiveKernelJetBounds W p (fun _ (y : Q) => y.2) :=
    N04PositiveKernelJetBounds.linear hW
      (ContinuousLinearMap.snd ℝ (N04PositiveRadialCoefficients n) ℝ) hp
  exact (angularPatchKernel_bounds hW n (fun _ (y : Q) => y.1 false)
    (fun _ (y : Q) => y.2) l δ (ha false) hx hl hδ).add
      (angularPatchKernel_bounds hW n (fun _ (y : Q) => y.1 true)
        (fun _ (y : Q) => y.2) r δ (ha true) hx hr hδ) hW

end ContinuousFlexibility.Analysis
