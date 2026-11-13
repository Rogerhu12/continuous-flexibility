import ContinuousFlexibility.Analysis.N04bSymmetricRootField
import ContinuousFlexibility.Analysis.N04bLeftRootFlowGeometry
import ContinuousFlexibility.Analysis.N04bRootOrientation
import ContinuousFlexibility.Analysis.N04bRootFlowContinuity
import ContinuousFlexibility.Analysis.N04bCorrectedReturnGeometry

/-!
# The actual corrected flow normalized at the right root

The actual inverse terminal map reparametrizes the stored flow so its
right-root value is the identity. Reversing the radial coordinate then
gives the positive-sign physical root equation. The root orientation
and the initial inverse are both derived from the existing data.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The genuine stored flow, normalized by its genuine terminal inverse
and parametrized by inward distance from the right root. -/
def n04bRightRootFlow {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (m : ℕ) (θ x : ℝ) : ℝ :=
  L.minusFlow z m (C.right m - x)
    (Function.invFun (L.minusFlow z m (C.right m)) θ)

/-- The normalization can be undone exactly at every radial parameter,
without any radial regularity assumption. -/
theorem n04b_rightRootFlow_eq_stored
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ x : ℝ) :
    n04bRightRootFlow C L z m (L.minusFlow z m (C.right m) θ) x =
      L.minusFlow z m (C.right m - x) θ := by
  have hgeometry := n04b_corrected_return_geometry hT hS h03 hz hs m
  have hbij := hgeometry.2.2.2.1
  simp only [n04bRightRootFlow, Function.leftInverse_invFun hbij.1 θ]

/-- Construct the actual reverse-root equation on one nontrivial closed
right collar. No angular regularity of the stored interior flow is used. -/
theorem n04b_exists_right_root_symmetric_flow_equations_with_physical_factors
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < ρ ∧ C.left m < C.right m - ρ ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) ∧
      (∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi) ∧
      (∀ r θ, d (r, -θ) = -d (r, θ)) ∧
      (∀ r θ, c₀ (r, -θ) = c₀ (r, θ)) ∧
      (∀ p, 0 < c₀ p) ∧
      (∀ θ, n04bRightRootFlow C L z m θ 0 = θ) ∧
      (∀ θ, ContinuousOn (n04bRightRootFlow C L z m θ) (Icc (0 : ℝ) ρ)) ∧
      (∀ θ x, x ∈ Ioo (0 : ℝ) ρ →
        HasDerivAt (n04bRightRootFlow C L z m θ)
          (rootPhysicalSpeed d c₀ 1 (x, n04bRightRootFlow C L z m θ x)) x) ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        Real.sqrt x * c₀ (x, θ) =
          n04bCharacteristicHalfGap (L.coefficients z) (C.right m - x, θ)) ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        d (x, θ) = -n04bCharacteristicDrift (L.coefficients z) (C.right m - x, θ)) := by
  have hcontrol : controlGeometryConditions D S C := h03.1.1.2.2.2.1
  have hbounds := hcontrol.1 m
  have hroot := hcontrol.2.1 m
  have hr : C.right m ∈ Ioo D.a D.b :=
    ⟨hbounds.1.trans hbounds.2.1, hbounds.2.2⟩
  have hsign : (-1 : ℝ) * deriv (deriv D.w) (C.right m) < 0 := by
    linarith [(n04b_component_root_orientations h03.1.1 m).2]
  obtain ⟨η, d, c₀, hη, hd, hc, hdp, hcp, hdodd, hceven, hcpos, hphysical⟩ :=
    n04b_exists_symmetric_corrected_root_factors hT hS h03 hL hz hs hr hroot.2.1 hsign
  let ρ : ℝ := min η ((C.right m - C.left m) / 2)
  have hρ : 0 < ρ := lt_min_iff.mpr ⟨hη, half_pos (sub_pos.mpr hbounds.2.1)⟩
  have hρη : ρ ≤ η := min_le_left _ _
  have hsmall : C.left m < C.right m - ρ := by
    have hhalf : ρ ≤ (C.right m - C.left m) / 2 := min_le_right _ _
    linarith [hbounds.2.1]
  have hflow := h03.2.2.2.2.2.1 z hz hs m
  have hgeometry := n04b_corrected_return_geometry hT hS h03 hz hs m
  have hbij := hgeometry.2.2.2.1
  refine ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ
    simpa only [n04bRightRootFlow, sub_zero] using
      Function.rightInverse_invFun hbij.2 θ
  · intro θ
    apply (hflow (Function.invFun (L.minusFlow z m (C.right m)) θ)).2.1.comp
      (continuous_const.sub continuous_id).continuousOn
    intro x hx
    change C.right m - x ∈ Icc (C.left m) (C.right m)
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · intro θ x hx
    have hxC : C.right m - x ∈ Ioo (C.left m) (C.right m) :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hactual : HasDerivAt (n04bRightRootFlow C L z m θ)
        (-minusCharacteristicSpeed (L.coefficients z)
          (C.right m - x, n04bRightRootFlow C L z m θ x)) x := by
      change HasDerivAt
        (fun y => L.minusFlow z m (C.right m - y)
          (Function.invFun (L.minusFlow z m (C.right m)) θ))
        (-minusCharacteristicSpeed (L.coefficients z)
          (C.right m - x, L.minusFlow z m (C.right m - x)
            (Function.invFun (L.minusFlow z m (C.right m)) θ))) x
      simpa only [Function.comp_def, mul_neg_one] using
        ((hflow (Function.invFun (L.minusFlow z m (C.right m)) θ)).2.2.1
          (C.right m - x) hxC).comp x ((hasDerivAt_id x).const_sub (C.right m))
    apply hactual.congr_deriv
    have hp : (x, n04bRightRootFlow C L z m θ x) ∈
        Icc (0 : ℝ) η ×ˢ (univ : Set ℝ) :=
      ⟨⟨hx.1.le, hx.2.le.trans hρη⟩, mem_univ _⟩
    have heq := (hphysical _ hp).2.1
    have hspeed :
        -minusCharacteristicSpeed (L.coefficients z)
          (C.right m - x, n04bRightRootFlow C L z m θ x) =
        d (x, n04bRightRootFlow C L z m θ x) +
          Real.sqrt x * c₀ (x, n04bRightRootFlow C L z m θ x) := by
      simpa only [rootProfileShift, neg_one_mul, neg_mul, one_mul, neg_neg,
        sub_neg_eq_add, sub_eq_add_neg]
        using heq
    simpa only [rootPhysicalSpeed, one_mul] using hspeed
  · intro x hx θ
    have hp : (x, θ) ∈ Icc (0 : ℝ) η ×ˢ (univ : Set ℝ) :=
      ⟨⟨hx.1, hx.2.trans hρη⟩, mem_univ _⟩
    have hm := (hphysical (x, θ) hp).2.1
    have hp' := (hphysical (x, θ) hp).2.2
    simp only [rootProfileShift, neg_one_mul, neg_mul, one_mul, neg_neg, sub_neg_eq_add,
      ← sub_eq_add_neg] at hm hp'
    dsimp only [minusCharacteristicSpeed, plusCharacteristicSpeed,
      n04bCharacteristicHalfGap] at hm hp' ⊢
    linarith only [hm, hp']
  · intro x hx θ
    have hp : (x, θ) ∈ Icc (0 : ℝ) η ×ˢ (univ : Set ℝ) :=
      ⟨⟨hx.1, hx.2.trans hρη⟩, mem_univ _⟩
    have hdrift := n04b_rootDrift_eq_of_characteristic_equations
      (hphysical (x, θ) hp).2.1 (hphysical (x, θ) hp).2.2
    simpa only [rootProfileShift, neg_one_mul, ← sub_eq_add_neg] using hdrift

/-- Projection retaining the established half-gap interface. -/
theorem n04b_exists_right_root_symmetric_flow_equations_with_halfGap
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < ρ ∧ C.left m < C.right m - ρ ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) ∧
      (∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi) ∧
      (∀ r θ, d (r, -θ) = -d (r, θ)) ∧
      (∀ r θ, c₀ (r, -θ) = c₀ (r, θ)) ∧
      (∀ p, 0 < c₀ p) ∧
      (∀ θ, n04bRightRootFlow C L z m θ 0 = θ) ∧
      (∀ θ, ContinuousOn (n04bRightRootFlow C L z m θ) (Icc (0 : ℝ) ρ)) ∧
      (∀ θ x, x ∈ Ioo (0 : ℝ) ρ →
        HasDerivAt (n04bRightRootFlow C L z m θ)
          (rootPhysicalSpeed d c₀ 1 (x, n04bRightRootFlow C L z m θ x)) x) ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        Real.sqrt x * c₀ (x, θ) =
          n04bCharacteristicHalfGap (L.coefficients z) (C.right m - x, θ)) := by
  obtain ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos,
      hi, hcont, hflow, hgap, _⟩ :=
    n04b_exists_right_root_symmetric_flow_equations_with_physical_factors hT hS h03 hL hz hs m
  exact ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos,
    hi, hcont, hflow, hgap⟩

/-- Projection retaining the established actual root-flow interface. -/
theorem n04b_exists_right_root_symmetric_flow_equations
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < ρ ∧ C.left m < C.right m - ρ ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) ∧
      (∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi) ∧
      (∀ r θ, d (r, -θ) = -d (r, θ)) ∧
      (∀ r θ, c₀ (r, -θ) = c₀ (r, θ)) ∧
      (∀ p, 0 < c₀ p) ∧
      (∀ θ, n04bRightRootFlow C L z m θ 0 = θ) ∧
      (∀ θ, ContinuousOn (n04bRightRootFlow C L z m θ) (Icc (0 : ℝ) ρ)) ∧
      (∀ θ x, x ∈ Ioo (0 : ℝ) ρ →
        HasDerivAt (n04bRightRootFlow C L z m θ)
          (rootPhysicalSpeed d c₀ 1 (x, n04bRightRootFlow C L z m θ x)) x) := by
  obtain ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos,
      hi, hcont, hflow, _⟩ :=
    n04b_exists_right_root_symmetric_flow_equations_with_halfGap hT hS h03 hL hz hs m
  exact ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos,
    hi, hcont, hflow⟩

/-- Projection of the constructed symmetric right-root data to the
ordinary physical-flow interface. -/
theorem n04b_exists_right_root_flow_equations
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < ρ ∧ C.left m < C.right m - ρ ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) ∧
      (∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi) ∧
      (∀ θ, n04bRightRootFlow C L z m θ 0 = θ) ∧
      (∀ θ, ContinuousOn (n04bRightRootFlow C L z m θ) (Icc (0 : ℝ) ρ)) ∧
      (∀ θ x, x ∈ Ioo (0 : ℝ) ρ →
        HasDerivAt (n04bRightRootFlow C L z m θ)
          (rootPhysicalSpeed d c₀ 1 (x, n04bRightRootFlow C L z m θ x)) x) := by
  obtain ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, _, _, _, hi, hcont, hflow⟩ :=
    n04b_exists_right_root_symmetric_flow_equations hT hS h03 hL hz hs m
  exact ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hi, hcont, hflow⟩

/-- The normalized actual right flow and its inverse have the full
closed angular geometry and joint regularity supplied by the root ODE. -/
theorem n04b_exists_right_root_flow_geometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ C.left m < C.right m - ρ ∧
      (∀ x ∈ Icc (0 : ℝ) ρ,
        let f : ℝ → ℝ := fun θ => n04bRightRootFlow C L z m θ x
        let g : ℝ → ℝ := Function.invFun f
        ContDiff ℝ ∞ f ∧ (∀ θ, 0 < deriv f θ) ∧
          (∀ θ, f (θ + Real.pi) = f θ + Real.pi) ∧ Function.Bijective f ∧
          ContDiff ℝ ∞ g ∧ (∀ θ, 0 < deriv g θ) ∧
          (∀ θ, f (g θ) = θ ∧ g (f θ) = θ) ∧
          (∀ θ, g (θ + Real.pi) = g θ + Real.pi)) ∧
      ContinuousOn (fun p : PolarPoint => n04bRightRootFlow C L z m p.2 p.1)
        (Icc (0 : ℝ) ρ ×ˢ univ) ∧
      ContinuousOn (fun p : PolarPoint =>
        Function.invFun (fun θ => n04bRightRootFlow C L z m θ p.1) p.2)
        (Icc (0 : ℝ) ρ ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun p : PolarPoint => n04bRightRootFlow C L z m p.2 p.1)
        (Ioo (0 : ℝ) ρ ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun p : PolarPoint =>
        Function.invFun (fun θ => n04bRightRootFlow C L z m θ p.1) p.2)
        (Ioo (0 : ℝ) ρ ×ˢ univ) := by
  obtain ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hi, hcont, hflow⟩ :=
    n04b_exists_right_root_flow_equations hT hS h03 hL hz hs m
  have hregular := n04b_rootStoredFlow_joint_regularity hρ Real.pi_ne_zero
    hd hc hdp hcp hi hcont hflow
  exact ⟨ρ, hρ, hsmall,
    fun _ hx => n04b_rootStoredFlow_angular_geometry
      hρ Real.pi_ne_zero hd hc hdp hcp hi hcont hflow hx,
    hregular.1, hregular.2.1,
    n04b_rootStoredFlow_contDiffOn hρ Real.pi_ne_zero hd hc hdp hcp hi hcont hflow,
    hregular.2.2⟩

end ContinuousFlexibility.Analysis
