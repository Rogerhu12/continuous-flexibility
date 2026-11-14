module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsAngularGraph
public import ContinuousFlexibility.Analysis.N06BoundaryRadialJets

/-!
# The chosen radial coefficients from actual source and inverse jets

This is the literal finite partition formula for the stored pullback
coefficients. Every forward factor is a genuine source jet at the
forward root label; every inverse factor is a lower positive jet of the
actual triangular angular inverse. No new extension is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

theorem n04PositiveGeometry_controlled_coefficient_partition
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (side : Bool) (m : ℕ) (hsource : (X.src i side).val = some m)
    (j : ℕ) (hj : j ≤ n + 1) (θ : ℝ) :
    G.toN04PositiveGeometryControlData.coefficients z i side j θ =
      ∑ c : OrderedFinpartition j,
        iteratedFDeriv ℝ c.length
          (fun p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).1)
          (if side then n04PositiveRight i else n04PositiveLeft i,
            n01RootLabel W.S W.C z m (!side) θ)
          (fun k => iteratedFDeriv ℝ (c.partSize k)
            (n04PositiveGeometry_angularGraphInverse
              (G.toN04PositiveGeometryControlData.angle z i))
            (if side then n04PositiveRight i else n04PositiveLeft i, θ)
            (fun _ => (1, 0))) := by
  let φ := G.toN04PositiveGeometryControlData.angle z i
  let ξ := G.toN04PositiveGeometryControlData.radialRepresentative z i side
  let e := if side then n04PositiveRight i else n04PositiveLeft i
  let β := n01RootLabel W.S W.C z m (!side)
  let g := n04PositiveGeometry_angularGraphInverse φ
  have hφ := n04PositiveGeometry_controlled_angle_contDiff G hz hs i
  have hξ : ContDiff ℝ ∞ ξ :=
    n04PositiveGeometry_controlled_radialRepresentative_contDiff G hz hs i side
  have hp (p : PolarPoint) : 0 < deriv (fun η => φ (p.1, η)) p.2 :=
    n04PositiveGeometry_controlled_angle_positive G hz hs i p.1 p.2
  have hperiod (r θ : ℝ) : φ (r, θ + Real.pi) = φ (r, θ) + Real.pi :=
    n04PositiveGeometry_controlled_angle_period G hz hs i r θ
  have hg : ContDiff ℝ ∞ g :=
    n04PositiveGeometry_angularGraphInverse_contDiff Real.pi_ne_zero hφ hp hperiod
  have hpoint : g (e, θ) = (e, β θ) :=
    Prod.ext rfl (n04PositiveGeometry_controlled_angle_inverse_boundary
      G hz hs i side m hsource θ)
  have hcomp : iteratedFDeriv ℝ j (ξ ∘ g) (e, θ) =
      ∑ c : OrderedFinpartition j,
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length ξ (g (e, θ)))
          (fun k => iteratedFDeriv ℝ (c.partSize k) g (e, θ)) :=
    iteratedFDeriv_comp (hξ.contDiffAt (x := g (e, θ)))
      (hg.contDiffAt (x := (e, θ))) (by simp : (j : ℕ∞ω) ≤ ∞)
  have heval := congrArg
    (fun A : PolarPoint [×j]→L[ℝ] ℝ => A (fun _ => (1, 0))) hcomp
  simp only [ContinuousMultilinearMap.sum_apply,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply] at heval
  rw [N04PositiveGeometryControlData.coefficients_eq_angularPullback]
  change radialBoundaryJet (ξ ∘ g) e j θ = _
  rw [n06_radialBoundaryJet_eq_frechet j ((hξ.comp hg).contDiffAt)]
  refine heval.trans (Finset.sum_congr rfl (fun c _ => ?_))
  rw [hpoint]
  have he := n04PositiveGeometry_controlled_radialRepresentative_boundary_jets
    G hz hs i side c.length (c.length_le.trans hj) (β θ)
  exact congrArg (fun A : PolarPoint [×c.length]→L[ℝ] ℝ =>
    A (fun k => iteratedFDeriv ℝ (c.partSize k) g (e, θ) (fun _ => (1, 0)))) he

end ContinuousFlexibility.Analysis
