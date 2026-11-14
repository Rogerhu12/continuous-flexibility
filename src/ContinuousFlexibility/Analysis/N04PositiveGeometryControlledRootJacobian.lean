import ContinuousFlexibility.Analysis.N03RootEndpointMaterialJets
import ContinuousFlexibility.Analysis.N04RealizationRootJacobianKernel

/-!
# Material reciprocal Jacobians of the original root charts

The unit root model has a material reciprocal odd coefficient and an
angular label derivative bounded below by one quarter. Its exact determinant
formula therefore gives a material reciprocal determinant. The actual N03
root-jet identification transfers this bound through an orientation of
absolute value one; the state-dependent identification radius has no cost.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem root_absJacobian_eq_of_unit_firstJet
    {F M : PolarPoint → PolarPoint} {r σ θ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hF : ContDiffAt ℝ ∞ F (r, θ)) (hM : ContDiffAt ℝ ∞ M (0, θ))
    (hjet : iteratedFDeriv ℝ 1 (fun p => F (rootProfileShift r σ p)) (0, θ) =
      iteratedFDeriv ℝ 1 M (0, θ)) :
    |planeJacobian F (r, θ)| = |planeJacobian M (0, θ)| := by
  have hpoint : rootProfileShift r σ (0, θ) = (r, θ) := by
    simp only [rootProfileShift, mul_zero, add_zero]
  have hshift : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hFnorm : ContDiffAt ℝ ∞ (fun p => F (rootProfileShift r σ p)) (0, θ) := by
    simpa only [Function.comp_def] using
      (show ContDiffAt ℝ ∞ F (rootProfileShift r σ (0, θ)) by
        simpa only [hpoint] using hF).comp (0, θ) hshift.contDiffAt
  have hD := root_fderiv_eq_of_firstJet_eq hFnorm hM hjet
  have hJ : planeJacobian (fun p => F (rootProfileShift r σ p)) (0, θ) =
      planeJacobian M (0, θ) := by
    unfold planeJacobian
    rw [hD]
  have hF' : DifferentiableAt ℝ F (rootProfileShift r σ (0, θ)) := by
    simpa only [hpoint] using hF.differentiableAt (by simp)
  have hchain : planeJacobian (fun p => F (rootProfileShift r σ p)) (0, θ) =
      planeJacobian F (r, θ) * σ := by
    simpa only [Function.comp_def, planeJacobian_rootProfileShift, hpoint] using
      planeJacobian_comp (hshift.differentiable (by simp) (0, θ)) hF'
  have hσabs : |σ| = 1 := by
    rcases hσ with h | h <;> rw [h] <;> norm_num
  simpa only [abs_mul, hσabs, mul_one] using congrArg abs (hchain.symm.trans hJ)

private theorem root_material_cost_of_unit_firstJet
    {F M : PolarPoint → PolarPoint} {r σ θ P W : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hP : 1 ≤ P) (hW : 1 ≤ W)
    (hF : ContDiffAt ℝ ∞ F (r, θ))
    (hjet : iteratedFDeriv ℝ 1 (fun p => F (rootProfileShift r σ p)) (0, θ) =
      iteratedFDeriv ℝ 1 M (0, θ))
    (hmodel : ContDiffAt ℝ ∞ M (0, θ) ∧ 0 < planeJacobian M (0, θ) ∧
      (planeJacobian M (0, θ))⁻¹ ≤ 4 * (P * W ^ P)) :
    |planeJacobian F (r, θ)|⁻¹ ≤ (4 * P) * W ^ (4 * P) := by
  have hJac : |planeJacobian F (r, θ)| = planeJacobian M (0, θ) :=
    (root_absJacobian_eq_of_unit_firstJet hσ hF hmodel.1 hjet).trans (abs_of_pos hmodel.2.1)
  rw [hJac]
  calc
    _ ≤ 4 * (P * W ^ P) := hmodel.2.2
    _ = (4 * P) * W ^ P := by ring
    _ ≤ (4 * P) * W ^ (4 * P) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hW (by linarith)) (by linarith)

/-- A fixed neighborhood and one material power control the reciprocal
determinant of every original chart at every genuine root circle. -/
theorem n04PositiveGeometry_actual_root_jacobian_material_cost
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε K₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hK : 0 < K₀) :
    ∃ C0 : ℝ, ∃ newBase : ℕ, ∃ ε' P : ℝ,
      1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧ 1 ≤ P ∧
      ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ side : Bool, ∀ θ : ℝ,
        let r := n01ComponentRoot C m side
        let i := if side then (K.cutPair m).2 else (K.cutPair m).1
        |planeJacobian (K.chart z i) (r, θ)|⁻¹ ≤
          P * (C0 * T.E0 (T.sample j)) ^ P := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  refine (n01_exists_common_root_inputs n04FlowJetsTarget_proof hS hT hN.1.1).elim ?_
  intro rootBase hR1
  refine hR1.elim ?_
  intro flowLoss hR2
  refine hR2.elim ?_
  intro η hR3
  have hb := hR3.1
  have hη := hR3.2.1
  have hηε := hR3.2.2.1
  have hflow := hR3.2.2.2.1
  have hinputs := hR3.2.2.2.2
  have hsub := stateNeighborhood_mono S C hb hηε
  have hN' := nonlinearPropertiesThrough03_restrict hT hN hb le_rfl hη hηε
  have hA' := n04PartA_restrict hA hb hηε
  have hB' := n04PartB_restrict hB hb hηε
  have hfield' : N04bFieldRegularity D S C L rootBase η :=
    { smooth_coefficients := fun z hz => hfield.smooth_coefficients z (hsub hz)
      periodic_coefficients := fun z hz => hfield.periodic_coefficients z (hsub hz)
      positive_a := fun z hz => hfield.positive_a z (hsub hz)
      reference_flow := hfield.reference_flow
      negative_discriminant := fun z hz => hfield.negative_discriminant z (hsub hz) }
  refine (n01_rootOddCoefficient_unit_material_values_of_component_optical
    hS hT hN'.1.1 hflow hK).elim ?_
  intro C0 hV1
  refine hV1.elim ?_
  intro low hV2
  refine hV2.elim ?_
  intro P hV3
  have hC0 := hV3.1
  have hfloor := hV3.2.1
  have hP := hV3.2.2.1
  have hvalues := hV3.2.2.2
  let newBase : ℕ := max rootBase low
  let ε' : ℝ := min η (1 / 2)
  refine ⟨C0, newBase, ε', 4 * P, hC0, hfloor,
    hb.trans (le_max_left _ _), lt_min hη (by norm_num),
    (min_le_left _ _).trans hηε, by linarith, ?_⟩
  intro z hz hs m j hhost hoptical side θ
  have hzroot : z ∈ stateNeighborhood S C rootBase η :=
    stateNeighborhood_mono S C (le_max_left _ _) (min_le_left _ _) hz
  have hsmall : pairGrading (stateGrading S) realGrading newBase
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hz).trans (by
      have he : ε' ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hzlow := (hp (le_max_right rootBase low) _).trans hsmall
  refine (hinputs m side).elim ?_
  intro g hI1
  refine hI1.elim ?_
  intro R hI2
  refine hI2.elim ?_
  intro hR hI3
  refine hI3.elim ?_
  intro κ hI4
  have hg := hI4.1
  have hκ := hI4.2.2.1
  have hfactor := hI4.2.2.2.1
  have hgeometry := hI4.2.2.2.2.1
  have hflows := hI4.2.2.2.2.2
  refine (hflows 1 zero_lt_one).elim ?_
  intro δ hD1
  refine hD1.elim ?_
  intro A hD2
  have hδ := hD2.1
  have hApos := hD2.2.2.2.1
  have hfamily := hD2.2.2.2.2
  have hstrip := (hgeometry.1 z hzroot hs).1
  refine (n03_controlledRootInput_unit_identification
    hS hT hN' hfield' hA' hB' hzroot hs m side hg hR hκ hδ hApos hstrip
    (hfamily z hzroot hs)).elim ?_
  intro Θ hΘi
  have hΘ := hΘi.1
  have hident := hΘi.2 θ
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
    (n01RootLabel S C z m side)
  let d := localizedRootDrift D S C r σ hR z
  let c := localizedRootSpeed D S C g r σ hR z
  let W : ℝ := C0 * T.E0 (T.sample j)
  let M : ℝ := P * W ^ P
  have hW : 1 ≤ W := hfloor j
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hP
    (Real.one_le_rpow hW (zero_le_one.trans hP))
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN'.1.1
    (g := g) (r := r) (σ := σ) (z := z) hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hΘ₁ : N04FlowEquations (rootRegularizedField d c) (rootFlowParameterUnscale Θ δ) :=
    rootFlowParameterUnscale_equations (d := d) (c := c) (Θ := Θ) hδ.ne' hΘ
  have hχ := hvalues z hzroot hs hzlow m j hhost hoptical side g hg hfactor R hR hstrip
    δ hδ.ne' Θ hΘ θ
  have hmodel := n04Realization_rootUnit_jacobian_cost hregular.1 hregular.2
    hperiod.1 hperiod.2 hΘ₁ (n01RootLabel_contDiff hS hT hN'.1.1 hzroot hs m side)
    (n01RootLabel_period_add hN'.1.1 hzroot hs m side)
    (n01RootLabel_deriv_mem_quarter_four hN'.1.1 hflow hzroot hs m side θ).1
    hM hχ.1 hχ.2.2
  have hF : ContDiffAt ℝ ∞ (K.chart z i) (r, θ) :=
    ((hA'.boundary z hzroot hs i).2.2.2.2.1 (r, θ) hident.1).1
  exact root_material_cost_of_unit_firstJet (n01ComponentRootOrientation_eq side)
    hP hW hF (hident.2.2.2.2.1 1) hmodel

end ContinuousFlexibility.Analysis
