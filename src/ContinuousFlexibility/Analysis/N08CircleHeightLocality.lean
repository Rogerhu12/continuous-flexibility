import ContinuousFlexibility.Analysis.N08HeightLocality
import ContinuousFlexibility.Analysis.N08CircleReferenceDiagonal

/-!
# Local height rescaling preserves the genuine control diagonal

The equality of actual return functions persists on the same weighted
control line at the two states. Uniqueness of the actual one-variable
derivative therefore identifies their diagonal entries. This uses the
existing N02 derivative and does not assume a smooth family of inverses.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

private theorem n08_circleMean_eq_of_local_height
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q q' : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q') ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    (hheight : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ, ∃ c : ℝ,
      (fun p => q * stateU S x p) =ᶠ[𝓝 (r, θ)]
        (fun p => q' * stateU S y p + c))
    (hchart : stateLeftChart S x m = stateLeftChart S y m) :
    n08ControlMeanCoordinate S m (n08CircleResidual hS hR (x, q)).val =
      n08ControlMeanCoordinate S m (n08CircleResidual hS hR (y, q')).val :=
  n08CircleResidual_mean_eq_of_decode hS hR (x, q) (y, q') hx hy hsx hsy m
    (funext fun θ => n08_returnResidual_eq_of_local_height hT hS hN hR
      (x := x) (y := y) (q := q) (q' := q') (m := m)
      hx hy hsx hsy hν hκ hheight hchart θ)

private def n08_localHeight_kappaLine (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) (t : ℝ) : AnnularState S :=
  x + n08StateSMul S t (0, (0, (n08ControlBasis hS m, 0)))

private theorem n08_localHeight_kappaLine_sector (hS : IsPhysicalSpaces D T S)
    {x : AnnularState S} (hx : stateSector S x) (m : ℕ) (t : ℝ) :
    stateSector S (n08_localHeight_kappaLine hS x m t) :=
  (stateSectorSubmodule S).add_mem hx
    ((stateSectorSubmodule S).smul_mem t (n08ControlBasis_direction_sector hS m))

private theorem n08_localHeight_kappaLine_height (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) (t : ℝ) :
    stateU S (n08_localHeight_kappaLine hS x m t) = stateU S x :=
  congrArg (heightPairField S)
    (n08_kappaLine_fixed_coordinates S x (n08ControlBasis hS m) t).1

private theorem n08_localHeight_kappaLine_chart (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) (t : ℝ) :
    stateLeftChart S (n08_localHeight_kappaLine hS x m t) m = stateLeftChart S x m :=
  congrArg (fun u : CircleSpace S => fun θ : ℝ =>
    θ + (S.circle (3 / 4 : ℝ)).decode u m θ)
    (n08_kappaLine_fixed_coordinates S x (n08ControlBasis hS m) t).2.2

private theorem n08_localHeight_kappaLine_return_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q q' : ℝ} {m : ℕ}
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    (hheight : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ, ∃ c : ℝ,
      (fun p => q * stateU S x p) =ᶠ[𝓝 (r, θ)]
        (fun p => q' * stateU S y p + c))
    (hchart : stateLeftChart S x m = stateLeftChart S y m) (t : ℝ)
    (hx : (n08_localHeight_kappaLine hS x m t, q) ∈ stateNeighborhood S C base ε)
    (hy : (n08_localHeight_kappaLine hS y m t, q') ∈ stateNeighborhood S C base ε) :
    n08ControlMeanCoordinate S m
        (n08CircleResidual hS hR (n08_localHeight_kappaLine hS x m t, q)).val =
      n08ControlMeanCoordinate S m
        (n08CircleResidual hS hR (n08_localHeight_kappaLine hS y m t, q')).val := by
  have hνt : (n08_localHeight_kappaLine hS x m t).2.1 =
      (n08_localHeight_kappaLine hS y m t).2.1 :=
    (n08_kappaLine_fixed_coordinates S x (n08ControlBasis hS m) t).2.1.trans
      (hν.trans (n08_kappaLine_fixed_coordinates S y (n08ControlBasis hS m) t).2.1.symm)
  have hκt : stateKappa S (n08_localHeight_kappaLine hS x m t) m =
      stateKappa S (n08_localHeight_kappaLine hS y m t) m :=
    (n08_stateKappa_add hS x
        (n08StateSMul S t (0, (0, (n08ControlBasis hS m, 0)))) m).trans
      ((congrArg (fun a : ℝ => a + stateKappa S
          (n08StateSMul S t (0, (0, (n08ControlBasis hS m, 0)))) m) hκ).trans
        (n08_stateKappa_add hS y
          (n08StateSMul S t (0, (0, (n08ControlBasis hS m, 0)))) m).symm)
  have hht : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ, ∃ c : ℝ,
      (fun p => q * stateU S (n08_localHeight_kappaLine hS x m t) p) =ᶠ[𝓝 (r, θ)]
        (fun p => q' * stateU S (n08_localHeight_kappaLine hS y m t) p + c) := by
    simpa only [n08_localHeight_kappaLine_height] using hheight
  exact n08_circleMean_eq_of_local_height hT hS hN hR
    (x := n08_localHeight_kappaLine hS x m t)
    (y := n08_localHeight_kappaLine hS y m t) (q := q) (q' := q') (m := m)
    hx hy (n08_localHeight_kappaLine_sector hS hsx m t)
    (n08_localHeight_kappaLine_sector hS hsy m t) hνt hκt hht
    ((n08_localHeight_kappaLine_chart hS x m t).trans
      (hchart.trans (n08_localHeight_kappaLine_chart hS y m t).symm))

private theorem n08_localHeight_kappaLine_return_germ
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q q' : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q') ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    (hheight : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ, ∃ c : ℝ,
      (fun p => q * stateU S x p) =ᶠ[𝓝 (r, θ)]
        (fun p => q' * stateU S y p + c))
    (hchart : stateLeftChart S x m = stateLeftChart S y m) :
    (fun t => n08ControlMeanCoordinate S m
      (n08CircleResidual hS hR (n08_localHeight_kappaLine hS x m t, q)).val) =ᶠ[𝓝 (0 : ℝ)]
    (fun t => n08ControlMeanCoordinate S m
      (n08CircleResidual hS hR (n08_localHeight_kappaLine hS y m t, q')).val) := by
  filter_upwards [n08_affine_parameter_eventually x
      (0, (0, (n08ControlBasis hS m, 0))) q (n08_isOpen_stateNeighborhood S C base ε) hx,
    n08_affine_parameter_eventually y (0, (0, (n08ControlBasis hS m, 0))) q'
      (n08_isOpen_stateNeighborhood S C base ε) hy] with t hXt hYt
  exact n08_localHeight_kappaLine_return_eq hT hS hN hR
    (x := x) (y := y) (q := q) (q' := q') (m := m)
    hsx hsy hν hκ hheight hchart t hXt hYt

theorem n08CircleDiagonal_eq_of_local_height
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q q' : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q') ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    (hheight : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ, ∃ c : ℝ,
      (fun p => q * stateU S x p) =ᶠ[𝓝 (r, θ)]
        (fun p => q' * stateU S y p + c))
    (hchart : stateLeftChart S x m = stateLeftChart S y m) :
    n08CircleDiagonal hS hR (x, q) m = n08CircleDiagonal hS hR (y, q') m := by
  have hdx : HasDerivAt (fun t => n08ControlMeanCoordinate S m
      (n08CircleResidual hS hR (n08_localHeight_kappaLine hS x m t, q)).val)
      (n08CircleDiagonal hS hR (x, q) m) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr
      ((n08CircleColumn_hasLineDerivAt hS hN.2.2.1 hR (z := (x, q)) hx hsx
        (n08ControlBasis hS m)).clm_comp (n08ControlMeanCoordinate S m))
  have hdy : HasDerivAt (fun t => n08ControlMeanCoordinate S m
      (n08CircleResidual hS hR (n08_localHeight_kappaLine hS y m t, q')).val)
      (n08CircleDiagonal hS hR (y, q') m) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr
      ((n08CircleColumn_hasLineDerivAt hS hN.2.2.1 hR (z := (y, q')) hy hsy
        (n08ControlBasis hS m)).clm_comp (n08ControlMeanCoordinate S m))
  exact hdx.unique (hdy.congr_of_eventuallyEq
    (n08_localHeight_kappaLine_return_germ hT hS hN hR
      (x := x) (y := y) (q := q) (q' := q') (m := m)
      hx hy hsx hsy hν hκ hheight hchart))

end ContinuousFlexibility.Statements
