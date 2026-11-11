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
  let v : AnnularState S := (0, 0, n08ControlBasis hS m, 0)
  let X (t : ℝ) : AnnularState S := x + n08StateSMul S t v
  let Y (t : ℝ) : AnnularState S := y + n08StateSMul S t v
  let fx (t : ℝ) : ℝ := n08ControlMeanCoordinate S m
    (n08CircleResidual hS hR (X t, q)).val
  let fy (t : ℝ) : ℝ := n08ControlMeanCoordinate S m
    (n08CircleResidual hS hR (Y t, q')).val
  have hdx : HasDerivAt fx (n08CircleDiagonal hS hR (x, q) m) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr
      ((n08CircleColumn_hasLineDerivAt hS hN.2.2.1 hR hx hsx
        (n08ControlBasis hS m)).clm_comp (n08ControlMeanCoordinate S m))
  have hdy : HasDerivAt fy (n08CircleDiagonal hS hR (y, q') m) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr
      ((n08CircleColumn_hasLineDerivAt hS hN.2.2.1 hR hy hsy
        (n08ControlBasis hS m)).clm_comp (n08ControlMeanCoordinate S m))
  have hX : ∀ᶠ t : ℝ in 𝓝 0, (X t, q) ∈ stateNeighborhood S C base ε :=
    n08_affine_parameter_eventually x v q (n08_isOpen_stateNeighborhood S C base ε) hx
  have hY : ∀ᶠ t : ℝ in 𝓝 0, (Y t, q') ∈ stateNeighborhood S C base ε :=
    n08_affine_parameter_eventually y v q' (n08_isOpen_stateNeighborhood S C base ε) hy
  have hsX (t : ℝ) : stateSector S (X t) :=
    (stateSectorSubmodule S).add_mem hsx
      ((stateSectorSubmodule S).smul_mem t (n08ControlBasis_direction_sector hS m))
  have hsY (t : ℝ) : stateSector S (Y t) :=
    (stateSectorSubmodule S).add_mem hsy
      ((stateSectorSubmodule S).smul_mem t (n08ControlBasis_direction_sector hS m))
  have hUX (t : ℝ) : stateU S (X t) = stateU S x := by
    exact congrArg (heightPairField S)
      (n08_kappaLine_fixed_coordinates S x (n08ControlBasis hS m) t).1
  have hUY (t : ℝ) : stateU S (Y t) = stateU S y := by
    exact congrArg (heightPairField S)
      (n08_kappaLine_fixed_coordinates S y (n08ControlBasis hS m) t).1
  have heq : fx =ᶠ[𝓝 0] fy := by
    filter_upwards [hX, hY] with t hXt hYt
    have hνt : (X t).2.1 = (Y t).2.1 := by
      exact (n08_kappaLine_fixed_coordinates S x (n08ControlBasis hS m) t).2.1.trans
        (hν.trans (n08_kappaLine_fixed_coordinates S y (n08ControlBasis hS m) t).2.1.symm)
    have hκt : stateKappa S (X t) m = stateKappa S (Y t) m := by
      exact (n08_stateKappa_add hS x (n08StateSMul S t v) m).trans
        ((congrArg (fun a : ℝ => a + stateKappa S (n08StateSMul S t v) m) hκ).trans
          (n08_stateKappa_add hS y (n08StateSMul S t v) m).symm)
    have hht : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ, ∃ c : ℝ,
        (fun p => q * stateU S (X t) p) =ᶠ[𝓝 (r, θ)]
          (fun p => q' * stateU S (Y t) p + c) := by
      simpa only [hUX t, hUY t] using hheight
    have hct : stateLeftChart S (X t) m = stateLeftChart S (Y t) m := by
      have hxchart : (X t).2.2.2 = x.2.2.2 :=
        (n08_kappaLine_fixed_coordinates S x (n08ControlBasis hS m) t).2.2
      have hychart : (Y t).2.2.2 = y.2.2.2 :=
        (n08_kappaLine_fixed_coordinates S y (n08ControlBasis hS m) t).2.2
      simpa only [stateLeftChart, hxchart, hychart] using hchart
    dsimp only [fx, fy]
    rw [n08ControlMeanCoordinate_apply, n08ControlMeanCoordinate_apply,
      n08ControlRestriction_apply hS, n08ControlRestriction_apply hS,
      n08CircleResidual_coe hS hR hXt (hsX t), n08CircleResidual_coe hS hR hYt (hsY t)]
    apply congrArg (fun u : ℝ → ℝ => T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * angularMean u)
    funext θ
    exact n08_returnResidual_eq_of_local_height hT hS hN hR hXt hYt (hsX t) (hsY t)
      hνt hκt hht hct θ
  exact hdx.unique (hdy.congr_of_eventuallyEq heq)

end ContinuousFlexibility.Statements
