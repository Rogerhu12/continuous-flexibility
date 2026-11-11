import ContinuousFlexibility.Analysis.CoupledCircleParameterIndependence

/-!
# The four columns of the same genuine residual jet

All column identities refer to one N08 directional tower. They can therefore
be added by the linearity of its first jet. This also transports that jet to
the ambient state line without asserting ambient smoothness off the sector.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

def coupledSectorKappaDirection (S : PhysicalSpacesData) (κ : CircleSpace S)
    (hκ : ∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode κ m θ =
      (S.circle (3 / 4 : ℝ)).decode κ m φ) : StateDirections S := by
  refine ⟨(0, (0, (κ, 0))), hκ, ?_⟩
  intro m θ
  simp only [map_zero, Pi.zero_apply, neg_zero]

theorem coupledSectorKappaDirection_val (S : PhysicalSpacesData) (κ : CircleSpace S)
    (hκ : ∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode κ m θ =
      (S.circle (3 / 4 : ℝ)).decode κ m φ) :
    (coupledSectorKappaDirection S κ hκ).val = (0, (0, (κ, 0))) := rfl

theorem coupled_sector_direction_decomposition (v : StateDirections S) :
    v = coupledSectorHeightDirection S v.val.1 + coupledSectorNuDirection S v.val.2.1 +
      coupledSectorKappaDirection S v.val.2.2.1 v.property.1 +
      coupledSectorChartDirection S v.val.2.2.2 v.property.2 := by
  apply Subtype.ext
  simp only [Submodule.coe_add, coupledSectorHeightDirection_val,
    coupledSectorNuDirection_val, coupledSectorKappaDirection_val,
    coupledSectorChartDirection_val, Prod.mk_add_mk, zero_add, add_zero]

private theorem coupled_nuDirection_scaled
    {H E : Type*} [AddCommGroup H] [Module ℝ H]
    [AddCommGroup E] [Module ℝ E]
    (W : Submodule ℝ (H × (ℝ × (E × E))))
    (v : ℝ → W) (hv : ∀ t, (v t).val = (0, (t, (0, 0)))) (t : ℝ) :
    (v t, (0 : ℝ)) = coupledScalarAction t (v 1, (0 : ℝ)) := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [coupledScalarAction_fst, coupledScalarAction_subtype_val,
      hv, coupledScalarAction_prod_mk, coupledScalarAction_zero,
      coupledScalarAction_real, mul_one]
  · simp only [coupledScalarAction_snd, coupledScalarAction_zero]

private theorem coupled_linear_scaled_first
    {E F H : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup H] [Module ℝ H]
    (L : E →ₗ[ℝ] F × H) {x y : E} {a : ℝ} {out : F}
    (hxy : x = coupledScalarAction a y) (hy : (L y).1 = out) :
    (L x).1 = a • out := by
  rw [hxy, coupledScalarAction_map, coupledScalarAction_fst, hy]
  rfl

theorem coupled_scalar_nu_firstJet
    (h8 : N08Properties D T S C R G P B base loss ε)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε) (μ : ℝ) :
    (projectiveJetHeadLinear J.D 0 z Fin.elim0 (coupledSectorNuDirection S μ, 0)).1 =
      μ • B.nuColumn (liftSectorParameter S C z) := by
  have hunit :
      (projectiveJetHeadLinear J.D 0 z Fin.elim0 (coupledSectorNuDirection S 1, 0)).1 =
        B.nuColumn (liftSectorParameter S C z) :=
    (coupled_scalar_first_derivative J hz (coupledSectorNuDirection S 1)).unique
      (h8.2.2.2.2.2.2.2.1 _ (liftSectorParameter_mem_stateNeighborhood hz le_rfl))
  exact coupled_linear_scaled_first (projectiveJetHeadLinear J.D 0 z Fin.elim0).toLinearMap
    (coupled_nuDirection_scaled (stateSectorSubmodule S) (coupledSectorNuDirection S)
      (coupledSectorNuDirection_val S) μ) hunit

theorem coupled_scalar_kappa_firstJet
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (κ : CircleSpace S) (hκ : ∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode κ m θ =
      (S.circle (3 / 4 : ℝ)).decode κ m φ) :
    (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorKappaDirection S κ hκ, 0)).1 =
        B.heightColumn (liftSectorParameter S C z) (B.restriction κ) := by
  have hκColumn := h8.2.2.2.2.2.2.2.2.1
  exact (coupled_scalar_first_derivative J hz (coupledSectorKappaDirection S κ hκ)).unique
    (hκColumn _ (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hRef.liftSectorParameter_sector z) κ)

theorem coupled_circle_height_firstJet
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (η : HeightPair S) :
    (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorHeightDirection S η, 0)).2.val =
        z.2 • B.heightRow (liftSectorParameter S C z) η := by
  have hheight := h8.2.2.2.2.2.2.2.2.2.1
  exact (coupled_circle_first_derivative J hz (coupledSectorHeightDirection S η)).unique
    (hheight _ (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hRef.liftSectorParameter_sector z) η)

theorem coupled_circle_kappa_firstJet
    (hRef : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (κ : CircleSpace S) (hκ : ∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode κ m θ =
      (S.circle (3 / 4 : ℝ)).decode κ m φ) :
    (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorKappaDirection S κ hκ, 0)).2.val =
        B.circleColumn (liftSectorParameter S C z) κ := by
  have hκColumn := h8.2.2.2.2.2.2.2.2.2.2.1
  exact (coupled_circle_first_derivative J hz (coupledSectorKappaDirection S κ hκ)).unique
    (hκColumn _ (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hRef.liftSectorParameter_sector z) κ)

theorem coupled_circle_firstJet_of_return_derivative
    (hRef : referenceStateConditions D S C)
    (hcircle : ∀ x ∈ stateNeighborhood S C base ε, stateSector S x.1 →
      (P.circle x).val = R.residual x)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : StateDirections S) (df : CircleSpace S)
    (hd : HasProjectiveLineDerivAt (fun x => R.residual (x, z.2)) df
      (liftSectorParameter S C z).1 v.val) :
    (projectiveJetHeadLinear J.D 0 z Fin.elim0 (v, 0)).2.val = df := by
  apply (coupled_circle_first_derivative J hz v).unique
  apply coupled_lineDerivAt_congr_line hd
  have hnear := coupledScalarAction_eventually_line_mem J.open_domain hz (v, (0 : ℝ))
  filter_upwards [hnear] with t ht
  have he := hcircle _ (liftSectorParameter_mem_stateNeighborhood ht le_rfl)
    (hRef.liftSectorParameter_sector _)
  simpa only [coupled_liftSectorParameter_add, coupledScalarAction] using he

/-- The full genuine sector jet is also the actual ambient state-line
derivative in its included direction. -/
theorem coupled_joint_first_derivative
    {U : Set (StateDirections S × ℝ)}
    (J : SmoothDirections U (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ U) (v : StateDirections S) :
    HasProjectiveLineDerivAt (fun x => jointResidual S P (x, z.2))
      (projectiveJetHeadLinear J.D 0 z Fin.elim0 (v, 0))
      (liftSectorParameter S C z).1 v.val := by
  have hd := coupled_smoothDirections_first_derivative J hz (v, 0)
  simpa only [HasProjectiveLineDerivAt, sectorJointResidual, liftSectorParameter,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Submodule.coe_add, Submodule.coe_smul, smul_zero, add_zero, add_assoc] using hd

end ContinuousFlexibility.Statements
