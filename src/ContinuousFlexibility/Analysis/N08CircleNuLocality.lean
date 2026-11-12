import ContinuousFlexibility.Analysis.N08CircleReferenceDiagonal

/-!
# Zero-parameter return data depend only on the local control and chart

The true-border cutoff vanishes on every negative radial component. The
controlled profile germ there therefore depends only on that component's
control mean. At zero parameter the actual ordinary flow is its radial
rotation, independently of both the height and the nu coordinate. Equality
on the same control line identifies the genuine diagonal derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology Interval

set_option backward.isDefEq.respectTransparency false

private theorem n08_fixedParameter_affine_mem
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set (E × ℝ)} (hU : IsOpen U) {x : E} {q : ℝ}
    (hx : (x, q) ∈ U) (v : E) :
    ∀ᶠ t : ℝ in 𝓝 0, (x + n08RealSMul t v, q) ∈ U := by
  have hc : Continuous (fun t : ℝ => (x + n08RealSMul t v, q)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const
  have ht : Tendsto (fun t : ℝ => (x + n08RealSMul t v, q))
      (𝓝 0) (𝓝 (x, q)) := by
    simpa only [n08RealSMul, zero_smul, add_zero] using hc.tendsto 0
  exact ht.eventually (hU.mem_nhds hx)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08_chi_zero_on_negative_component
    (hN : N01Properties D T S C base loss ε)
    {m : ℕ} {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) : D.chi r = 0 := by
  by_contra h
  exact lt_asymm (hN.1.2.2.2.1.support_subset h).2 (hN.2.2.2.1.2.2.2.1 m r hr)

/-- The cutoff's derivative is supported where the radial slope is
positive, so its value is constant on every negative component. -/
theorem n08_chiLeft_constant_on_component
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    ∃ c : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), S.chiLeft r = c := by
  obtain ⟨K, _, _, hpositive, hzero⟩ := hS.2.2.1.2.2
  apply isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (hS.2.2.1.1.differentiable (by simp)).differentiableOn
  intro r hr
  exact hzero r (fun hrK =>
    lt_asymm (hpositive r hrK) (hN.2.2.2.1.2.2.2.1 m r hr))

theorem n08_chiLeft_constant_germ_on_component
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    ∃ c : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m),
      S.chiLeft =ᶠ[𝓝 r] (fun _ => c) := by
  obtain ⟨c, hc⟩ := n08_chiLeft_constant_on_component hS hN m
  refine ⟨c, fun r hr => ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
  exact hc s hs

theorem n08_stateProfile_component_germ_of_kappa
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {m : ℕ}
    (hκ : stateKappa S x m = stateKappa S y m)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateProfile D S C x =ᶠ[𝓝 r] stateProfile D S C y := by
  filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
  rw [n08_stateProfile_on_component hN.2.2.2.1 x m hs,
    n08_stateProfile_on_component hN.2.2.2.1 y m hs,
    n08_chi_zero_on_negative_component hN hs, mul_zero, mul_zero, hκ]

private theorem n08_opticalSpeed_eq_of_germ {w v : ℝ → ℝ} {r : ℝ}
    (h : w =ᶠ[𝓝 r] v) : opticalSpeed w r = opticalSpeed v r := by
  rw [opticalSpeed, opticalSpeed, h.deriv_eq, h.eq_of_nhds]

/-- No height, nu, or sector equality is needed for this radial flow
identity. The target radius includes both turning-point endpoints. -/
theorem n08_minusFlow_zero_eq_of_kappa
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {m : ℕ}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hy : (y, 0) ∈ stateNeighborhood S C base ε)
    (hκ : stateKappa S x m = stateKappa S y m)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (x, 0) m r θ = C.minusFlow (y, 0) m r θ := by
  rw [n08_minusFlow_zero_parameter_rotation hS hT hN x hx m θ r hr,
    n08_minusFlow_zero_parameter_rotation hS hT hN y hy m θ r hr]
  apply congrArg (fun t : ℝ => θ - t)
  apply intervalIntegral.integral_congr_Ioo_of_le hr.1
  intro s hs
  exact n08_opticalSpeed_eq_of_germ
    (n08_stateProfile_component_germ_of_kappa hN hκ ⟨hs.1, hs.2.trans_le hr.2⟩)

theorem n08_returnResidual_zero_eq_of_kappa
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {m : ℕ}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hy : (y, 0) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hκ : stateKappa S x m = stateKappa S y m)
    (hchart : stateLeftChart S x m = stateLeftChart S y m) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (R.residual (x, 0)) m θ =
      (S.circle (3 / 4 : ℝ)).decode (R.residual (y, 0)) m θ := by
  rw [hR.2.1 (x, 0) hx hsx m θ, hR.2.1 (y, 0) hy hsy m θ]
  exact n08_returnResidualField_component_eq_of_flow hR hx hy hsx hsy
    (fun φ => n08_minusFlow_zero_eq_of_kappa hT hS hN hx hy hκ φ
      ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩) hchart θ

private def n08_kappaLine (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) (t : ℝ) : AnnularState S :=
  x + n08StateSMul S t (0, (0, (n08ControlBasis hS m, 0)))

private theorem n08_kappaLine_sector (hS : IsPhysicalSpaces D T S)
    {x : AnnularState S} (hx : stateSector S x) (m : ℕ) (t : ℝ) :
    stateSector S (n08_kappaLine hS x m t) :=
  (stateSectorSubmodule S).add_mem hx
    ((stateSectorSubmodule S).smul_mem t (n08ControlBasis_direction_sector hS m))

private theorem n08_kappaLine_chart (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) (t : ℝ) :
    stateLeftChart S (n08_kappaLine hS x m t) m = stateLeftChart S x m :=
  congrArg (fun u : CircleSpace S => fun θ : ℝ =>
    θ + (S.circle (3 / 4 : ℝ)).decode u m θ)
    (n08_kappaLine_fixed_coordinates S x (n08ControlBasis hS m) t).2.2

private theorem n08_kappaLine_kappa_eq (hS : IsPhysicalSpaces D T S)
    {x y : AnnularState S} {m : ℕ}
    (hκ : stateKappa S x m = stateKappa S y m) (t : ℝ) :
    stateKappa S (n08_kappaLine hS x m t) m =
      stateKappa S (n08_kappaLine hS y m t) m :=
  (n08_stateKappa_add hS x
      (n08StateSMul S t (0, (0, (n08ControlBasis hS m, 0)))) m).trans
    ((congrArg (fun a : ℝ => a + stateKappa S
        (n08StateSMul S t (0, (0, (n08ControlBasis hS m, 0)))) m) hκ).trans
      (n08_stateKappa_add hS y
        (n08StateSMul S t (0, (0, (n08ControlBasis hS m, 0)))) m).symm)

private theorem n08_nuMeanCoordinate_eq_of_decode
    (hS : IsPhysicalSpaces D T S) (m : ℕ) (u v : CircleSpace S)
    (h : (S.circle (3 / 4 : ℝ)).decode u m =
      (S.circle (3 / 4 : ℝ)).decode v m) :
    n08ControlMeanCoordinate S m u = n08ControlMeanCoordinate S m v :=
  (n08ControlMeanCoordinate_apply S m u).trans
    ((n08ControlRestriction_apply hS u m).trans
      ((congrArg (fun f : ℝ → ℝ =>
        T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * angularMean f) h).trans
        ((n08ControlRestriction_apply hS v m).symm.trans
          (n08ControlMeanCoordinate_apply S m v).symm)))

private theorem n08_circleMean_zero_eq_of_kappa
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {m : ℕ}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hy : (y, 0) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hκ : stateKappa S x m = stateKappa S y m)
    (hchart : stateLeftChart S x m = stateLeftChart S y m) :
    n08ControlMeanCoordinate S m (n08CircleResidual hS hR (x, 0)).val =
      n08ControlMeanCoordinate S m (n08CircleResidual hS hR (y, 0)).val := by
  have hd : (S.circle (3 / 4 : ℝ)).decode (R.residual (x, 0)) m =
      (S.circle (3 / 4 : ℝ)).decode (R.residual (y, 0)) m :=
    funext fun θ => n08_returnResidual_zero_eq_of_kappa hT hS hN hR
      (x := x) (y := y) (m := m) hx hy hsx hsy hκ hchart θ
  exact (congrArg (n08ControlMeanCoordinate S m)
      (n08CircleResidual_coe hS hR (z := (x, 0)) hx hsx)).trans
    ((n08_nuMeanCoordinate_eq_of_decode hS m _ _ hd).trans
      (congrArg (n08ControlMeanCoordinate S m)
        (n08CircleResidual_coe hS hR (z := (y, 0)) hy hsy)).symm)

private theorem n08_kappaLine_return_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {m : ℕ}
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hκ : stateKappa S x m = stateKappa S y m)
    (hchart : stateLeftChart S x m = stateLeftChart S y m) (t : ℝ)
    (hx : (n08_kappaLine hS x m t, 0) ∈ stateNeighborhood S C base ε)
    (hy : (n08_kappaLine hS y m t, 0) ∈ stateNeighborhood S C base ε) :
    n08ControlMeanCoordinate S m
        (n08CircleResidual hS hR (n08_kappaLine hS x m t, 0)).val =
      n08ControlMeanCoordinate S m
        (n08CircleResidual hS hR (n08_kappaLine hS y m t, 0)).val :=
  n08_circleMean_zero_eq_of_kappa hT hS hN hR
    (x := n08_kappaLine hS x m t) (y := n08_kappaLine hS y m t) (m := m)
    hx hy (n08_kappaLine_sector hS hsx m t) (n08_kappaLine_sector hS hsy m t)
    (n08_kappaLine_kappa_eq hS hκ t)
    ((n08_kappaLine_chart hS x m t).trans
      (hchart.trans (n08_kappaLine_chart hS y m t).symm))

private theorem n08_kappaLine_eventually_mem
    (hS : IsPhysicalSpaces D T S) {x : AnnularState S}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε) (m : ℕ) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (n08_kappaLine hS x m t, 0) ∈ stateNeighborhood S C base ε :=
  n08_fixedParameter_affine_mem (E := AnnularState S)
    (n08_isOpen_stateNeighborhood S C base ε) (x := x) (q := 0) hx
    (0, (0, (n08ControlBasis hS m, 0)))

private theorem n08_kappaLine_return_germ
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {m : ℕ}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hy : (y, 0) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hκ : stateKappa S x m = stateKappa S y m)
    (hchart : stateLeftChart S x m = stateLeftChart S y m) :
    (fun t => n08ControlMeanCoordinate S m
      (n08CircleResidual hS hR (n08_kappaLine hS x m t, 0)).val) =ᶠ[𝓝 (0 : ℝ)]
    (fun t => n08ControlMeanCoordinate S m
      (n08CircleResidual hS hR (n08_kappaLine hS y m t, 0)).val) := by
  filter_upwards [n08_kappaLine_eventually_mem hS hx m,
    n08_kappaLine_eventually_mem hS hy m] with t hXt hYt
  exact n08_kappaLine_return_eq hT hS hN hR
    (x := x) (y := y) (m := m) hsx hsy hκ hchart t hXt hYt

/-- The actual q-zero diagonal depends only on the local control mean and
left chart. In particular, its nu and height coordinates can be removed. -/
theorem n08CircleDiagonal_zero_eq_of_kappa_chart
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {m : ℕ}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hy : (y, 0) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hκ : stateKappa S x m = stateKappa S y m)
    (hchart : stateLeftChart S x m = stateLeftChart S y m) :
    n08CircleDiagonal hS hR (x, 0) m = n08CircleDiagonal hS hR (y, 0) m := by
  have hdx : HasDerivAt (fun t => n08ControlMeanCoordinate S m
      (n08CircleResidual hS hR (n08_kappaLine hS x m t, 0)).val)
      (n08CircleDiagonal hS hR (x, 0) m) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr
      ((n08CircleColumn_hasLineDerivAt hS hN.2.2.1 hR hx hsx
        (n08ControlBasis hS m)).clm_comp (n08ControlMeanCoordinate S m))
  have hdy : HasDerivAt (fun t => n08ControlMeanCoordinate S m
      (n08CircleResidual hS hR (n08_kappaLine hS y m t, 0)).val)
      (n08CircleDiagonal hS hR (y, 0) m) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr
      ((n08CircleColumn_hasLineDerivAt hS hN.2.2.1 hR hy hsy
        (n08ControlBasis hS m)).clm_comp (n08ControlMeanCoordinate S m))
  exact hdx.unique (hdy.congr_of_eventuallyEq
    (n08_kappaLine_return_germ hT hS hN hR hx hy hsx hsy hκ hchart))

end ContinuousFlexibility.Statements
