import ContinuousFlexibility.Analysis.CoupledDerivativeAlgebra
import ContinuousFlexibility.Analysis.NeighborhoodStateBounds
import ContinuousFlexibility.Analysis.SolveReturnEquations
import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
import ContinuousFlexibility.Scalar.WeightedStateDerivative

/-!
# The scalar row of the genuine coupled derivative

The first jet of the existing sector residual already takes values in the
original source space. Its height component is identified by evaluating that
jet and comparing with the finite-dimensional corrected residual derivative.
No source realization of a proposed derivative is assumed. The same argument
identifies the chart component with zero, because the actual scalar field is
independent of the chart.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {P : ResidualData S}

/-- Every height direction belongs to the linear state sector. -/
def coupledSectorHeightDirection (S : PhysicalSpacesData) (η : HeightPair S) :
    StateDirections S := by
  refine ⟨(η, (0, (0, 0))), ?_⟩
  change stateSector S (η, (0, (0, 0)))
  constructor
  · intro m θ φ
    simp only [map_zero, Pi.zero_apply]
  · intro m θ
    simp only [map_zero, Pi.zero_apply, neg_zero]

theorem coupledSectorHeightDirection_val (S : PhysicalSpacesData) (η : HeightPair S) :
    (coupledSectorHeightDirection S η).val = (η, (0, (0, 0))) := rfl

/-- An odd chart direction belongs to the same linear state sector. -/
def coupledSectorChartDirection (S : PhysicalSpacesData) (ψ : CircleSpace S)
    (hψ : IsOddCircle S ψ) : StateDirections S := by
  refine ⟨(0, (0, (0, ψ))), ?_⟩
  change stateSector S (0, (0, (0, ψ)))
  constructor
  · intro m θ φ
    simp only [map_zero, Pi.zero_apply]
  · exact hψ

theorem coupledSectorChartDirection_val (S : PhysicalSpacesData) (ψ : CircleSpace S)
    (hψ : IsOddCircle S ψ) :
    (coupledSectorChartDirection S ψ hψ).val = (0, (0, (0, ψ))) := rfl

/-- Along state directions the independent parameter is fixed. -/
theorem coupled_liftSectorParameter_add (z : StateDirections S × ℝ)
    (v : StateDirections S) (t : ℝ) :
    liftSectorParameter S C (z + (@SMul.smul ℝ (StateDirections S × ℝ) _ t (v, 0))) =
      ((liftSectorParameter S C z).1 + (@SMul.smul ℝ (AnnularState S) _ t v.val), z.2) := by
  simp only [liftSectorParameter, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, Submodule.coe_add, Submodule.coe_smul,
    smul_zero, add_zero, add_assoc]

theorem coupled_stateProfile_add_heightDirection
    (x : AnnularState S) (η : HeightPair S) (t : ℝ) :
    stateProfile D S C (x + (@SMul.smul ℝ (AnnularState S) _ t (η, (0, (0, 0))))) = stateProfile D S C x := by
  funext r
  simp only [stateProfile, stateKappa, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_zero, add_zero]

theorem coupled_stateU_add_heightDirection
    (x : AnnularState S) (η : HeightPair S) (t : ℝ) :
    stateU S (x + (@SMul.smul ℝ (AnnularState S) _ t (η, (0, (0, 0))))) =
      heightFamily (stateU S x) (heightPairField S η) t := by
  funext p
  simp only [stateU, heightPairField, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, map_add, map_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, heightFamily]
  ring

theorem coupled_scalarResidualField_add_heightDirection
    (x : AnnularState S) (η : HeightPair S) (q t : ℝ) :
    scalarResidualField D S C (x + (@SMul.smul ℝ (AnnularState S) _ t (η, (0, (0, 0)))), q) =
      normalizedResidual (stateProfile D S C x) (stateRadialHeight D S C x)
        (heightFamily (stateU S x) (heightPairField S η) t) q := by
  have hh : stateRadialHeight D S C (x + (@SMul.smul ℝ (AnnularState S) _ t (η, (0, (0, 0))))) =
      stateRadialHeight D S C x := by
    unfold stateRadialHeight
    rw [coupled_stateProfile_add_heightDirection]
  funext p
  change normalizedHeightResidual _ _ _ q p = normalizedHeightResidual _ _ _ q p
  simp only [coupled_stateProfile_add_heightDirection, hh, coupled_stateU_add_heightDirection]

/-- Chart changes leave the actual scalar field exactly unchanged. -/
theorem coupled_scalarResidualField_add_chartDirection
    (x : AnnularState S) (ψ : CircleSpace S) (q t : ℝ) :
    scalarResidualField D S C (x + (@SMul.smul ℝ (AnnularState S) _ t (0, (0, (0, ψ)))), q) =
      scalarResidualField D S C (x, q) := by
  simp only [scalarResidualField, stateRadialHeight, stateProfile, stateKappa,
    stateU, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_zero, add_zero]

/-- The corrected pointwise height derivative for the actual N01 geometry.
The formula includes the removable case where the independent parameter is zero. -/
theorem coupled_hasDerivAt_scalarResidualField_heightDirection
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {base loss : ℕ} {ε : ℝ} (h1 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (η : HeightPair S)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    HasDerivAt
      (fun t : ℝ => scalarResidualField D S C (z.1 + (@SMul.smul ℝ (AnnularState S) _ t (η, (0, (0, 0)))), z.2) p)
      (divergenceOperator (originalCoefficients D S C z) (heightPairField S η) p +
        z.2 * scalarCorrectionError (residualErrorCoefficient D S C z)
          (scalarResidualField D S C z) (heightPairField S η) p) 0 := by
  have hD : IsAccumulatingProfile D := h1.1.1
  have hw := contDiff_stateProfile_of_n01 hS hT h1 z.1
  have hh := stateRadialHeight_contDiff_of_contDiff hw
  have hu := neighborhood_stateU_contDiff hT hS z.1
  have hη : ContDiff ℝ ∞ (heightPairField S η) :=
    scalarCommonHeightDecode_contDiff hT hS η
  have hhw := stateRadialHeight_hasDerivAt_of_contDiff hw
  have hr : p.1 ≠ 0 := (hD.choose_spec.1.1.trans hp.1.1).ne'
  obtain ⟨_, _, _, _, _, _, _, _, _, hpositive, _⟩ := h1
  have hb := hpositive z hz hs p hp
  have hwp : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  have hdisc : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.2.2.2.2.1
  have hqratio : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) /
        stateProfile D S C z.1 p.1 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb.2.2.1
  have hQ : heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0 :=
    ((div_pos_iff_of_pos_right hwp).mp hqratio).ne'
  simp_rw [coupled_scalarResidualField_add_heightDirection]
  change HasDerivAt
    (fun t : ℝ => normalizedResidual (stateProfile D S C z.1) (stateRadialHeight D S C z.1)
      (heightFamily (stateU S z.1) (heightPairField S η) t) z.2 p)
    (heightCorrectedDivergence (stateProfile D S C z.1)
      (heightFamily (Radial.radialHeightField (stateRadialHeight D S C z.1)) (stateU S z.1) z.2)
      (heightPairField S η) p + z.2 *
      scalarCorrectionError (polarTypeB (stateProfile D S C z.1)
        (heightFamily (Radial.radialHeightField (stateRadialHeight D S C z.1)) (stateU S z.1) z.2))
        (normalizedResidual (stateProfile D S C z.1) (stateRadialHeight D S C z.1)
          (stateU S z.1) z.2) (heightPairField S η) p) 0
  exact hasDerivAt_normalizedResidual_corrected hw hh hu hη hhw z.2 hr hdisc hQ

/-- Interior decoding determines a source, since all decoded source heights
vanish outside the physical annulus. -/
theorem coupled_source_ext (hS : IsPhysicalSpaces D T S) {u v : S.Source}
    (heq : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode u.val p =
        (S.height (3 / 4 : ℝ)).decode v.val p) : u = v := by
  apply Subtype.ext
  apply (hS.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext p
  by_cases hp : p ∈ annularOpen D
  · exact heq p hp
  · rw [((hS.1 (3 / 4 : ℝ)).2.2.2.1 u.val).2.2.2.1 p hp,
      ((hS.1 (3 / 4 : ℝ)).2.2.2.1 v.val).2.2.2.1 p hp]

/-- A point evaluation observes the actual source-valued line derivative. -/
theorem coupled_source_decode_hasDerivAt
    (hS : IsPhysicalSpaces D T S)
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f : E → S.Source} {d : S.Source} {x v : E}
    (hf : HasProjectiveLineDerivAt f d x v) (p : PolarPoint) :
    HasDerivAt
      (fun t : ℝ => (S.height (3 / 4 : ℝ)).decode (f (x + t • v)).val p)
      ((S.height (3 / 4 : ℝ)).decode d.val p) 0 := by
  have hv := hf.clm_comp S.Q.toLinearMap.ker.subtypeL
  simpa only [Submodule.subtypeL_apply] using
    sobolev_decode_hasDerivAt_of_projectiveLineDerivAt
      ((hS.1 (3 / 4 : ℝ)).2.2.1) hv p

/-- The scalar projection of the existing first jet is a genuine derivative. -/
theorem coupled_sector_scalar_first_derivative
    {U : Set (StateDirections S × ℝ)}
    (J : SmoothDirections U (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ U) (v : StateDirections S × ℝ) :
    HasProjectiveLineDerivAt (fun y => (sectorJointResidual S C P y).1)
      (projectiveJetHeadLinear J.D 0 z Fin.elim0 v).1 z v := by
  exact (coupled_smoothDirections_first_derivative J hz v).clm_comp
    (ContinuousLinearMap.fst ℝ (S.Source) (EvenCircle S))

/-- The same line quotient is the ambient state derivative along its sector
direction; no ambient differentiability outside that line is required. -/
theorem coupled_scalar_first_derivative
    {U : Set (StateDirections S × ℝ)}
    (J : SmoothDirections U (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ U) (v : StateDirections S) :
    HasProjectiveLineDerivAt (fun x => P.scalar (x, z.2))
      (projectiveJetHeadLinear J.D 0 z Fin.elim0 (v, 0)).1
      (liftSectorParameter S C z).1 v.val := by
  have hd := coupled_sector_scalar_first_derivative J hz (v, 0)
  simpa only [HasProjectiveLineDerivAt, sectorJointResidual, jointResidual,
    liftSectorParameter, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Submodule.coe_add, Submodule.coe_smul, smul_zero,
    add_zero, add_assoc] using hd

private theorem coupled_sector_eventually_line_mem
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    {z : StateDirections S × ℝ} (hz : z ∈ U) (v : StateDirections S × ℝ) :
    ∀ᶠ t : ℝ in 𝓝 0, z + (@SMul.smul ℝ (StateDirections S × ℝ) _ t v) ∈ U := by
  have ht : ContinuousAt (fun t : ℝ => z + (@SMul.smul ℝ (StateDirections S × ℝ) _ t v)) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hline : Tendsto (fun t : ℝ => z + (@SMul.smul ℝ (StateDirections S × ℝ) _ t v)) (𝓝 0) (𝓝 z) := by
    simpa only [zero_smul, add_zero] using ht.tendsto
  exact hline.eventually (hU.mem_nhds hz)

/-- The scalar height entry of any genuine sector residual tower has the
prescribed original divergence plus the exact residual error. -/
theorem coupled_scalar_height_firstJet_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {base loss : ℕ} {ε : ℝ} (h1 : N01Properties D T S C base loss ε)
    (hscalar : ∀ x ∈ stateNeighborhood S C base ε, stateSector S x.1 →
      ∀ p ∈ annularOpen D,
        (S.height (3 / 4 : ℝ)).decode (P.scalar x).val p = scalarResidualField D S C x p)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (η : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode
        (projectiveJetHeadLinear J.D 0 z Fin.elim0
          (coupledSectorHeightDirection S η, 0)).1.val p =
      divergenceOperator (originalCoefficients D S C (liftSectorParameter S C z))
          (heightPairField S η) p +
        z.2 * scalarCorrectionError (residualErrorCoefficient D S C (liftSectorParameter S C z))
          (scalarResidualField D S C (liftSectorParameter S C z)) (heightPairField S η) p := by
  have hd := coupled_sector_scalar_first_derivative J hz
    (coupledSectorHeightDirection S η, 0)
  have hdecoded := coupled_source_decode_hasDerivAt hS hd p
  have hnear := coupled_sector_eventually_line_mem J.open_domain hz
    (coupledSectorHeightDirection S η, 0)
  have href : referenceStateConditions D S C := h1.2.2.1
  have hphysical := coupled_hasDerivAt_scalarResidualField_heightDirection hT hS h1
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (href.liftSectorParameter_sector z) η hp
  have hphysical' : HasDerivAt
      (fun t : ℝ => scalarResidualField D S C
        (liftSectorParameter S C (z + (@SMul.smul ℝ (StateDirections S × ℝ) _ t (coupledSectorHeightDirection S η, 0)))) p)
      (divergenceOperator (originalCoefficients D S C (liftSectorParameter S C z))
          (heightPairField S η) p +
        z.2 * scalarCorrectionError (residualErrorCoefficient D S C (liftSectorParameter S C z))
          (scalarResidualField D S C (liftSectorParameter S C z)) (heightPairField S η) p) 0 := by
    simpa only [coupled_liftSectorParameter_add, coupledSectorHeightDirection_val] using hphysical
  apply hdecoded.unique
  apply hphysical'.congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  exact hscalar _ (liftSectorParameter_mem_stateNeighborhood ht le_rfl)
    (href.liftSectorParameter_sector _) p hp

/-- The scalar chart entry of the actual first jet is zero in the source
space, by the actual scalar field and decoder injectivity. -/
theorem coupled_scalar_chart_firstJet_eq_zero
    (hS : IsPhysicalSpaces D T S) {base : ℕ} {ε : ℝ}
    (href : referenceStateConditions D S C)
    (hscalar : ∀ x ∈ stateNeighborhood S C base ε, stateSector S x.1 →
      ∀ p ∈ annularOpen D,
        (S.height (3 / 4 : ℝ)).decode (P.scalar x).val p = scalarResidualField D S C x p)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (ψ : CircleSpace S) (hψ : IsOddCircle S ψ) :
    (projectiveJetHeadLinear J.D 0 z Fin.elim0
      (coupledSectorChartDirection S ψ hψ, 0)).1 = 0 := by
  have hd := coupled_sector_scalar_first_derivative J hz
    (coupledSectorChartDirection S ψ hψ, 0)
  have hnear := coupled_sector_eventually_line_mem J.open_domain hz
    (coupledSectorChartDirection S ψ hψ, 0)
  apply coupled_source_ext hS
  intro p hp
  simp only [ZeroMemClass.coe_zero, map_zero, Pi.zero_apply]
  have hdecoded := coupled_source_decode_hasDerivAt hS hd p
  have hconstant := hasDerivAt_const (0 : ℝ)
    (scalarResidualField D S C (liftSectorParameter S C z) p)
  apply hdecoded.unique
  apply hconstant.congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  change (S.height (3 / 4 : ℝ)).decode
      (P.scalar (liftSectorParameter S C
        (z + (@SMul.smul ℝ (StateDirections S × ℝ) _ t (coupledSectorChartDirection S ψ hψ, 0))))).val p = _
  rw [hscalar _ (liftSectorParameter_mem_stateNeighborhood ht le_rfl)
    (href.liftSectorParameter_sector _) p hp]
  rw [coupled_liftSectorParameter_add, coupledSectorChartDirection_val,
    coupled_scalarResidualField_add_chartDirection]

private theorem coupled_scalar_lineDerivAt_replace
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {f : E → F} {df dg : F} {x v w : E}
    (h : HasProjectiveLineDerivAt f df x v) (hd : df = dg) (hv : v = w) :
    HasProjectiveLineDerivAt f dg x w := hd ▸ hv ▸ h

/-- The scalar map has zero genuine ambient state derivative in every odd
chart direction at a sector point. -/
theorem coupled_scalar_chart_hasLineDerivAt_zero
    (hS : IsPhysicalSpaces D T S) {base : ℕ} {ε : ℝ}
    (href : referenceStateConditions D S C)
    (hscalar : ∀ x ∈ stateNeighborhood S C base ε, stateSector S x.1 →
      ∀ p ∈ annularOpen D,
        (S.height (3 / 4 : ℝ)).decode (P.scalar x).val p = scalarResidualField D S C x p)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (ψ : CircleSpace S) (hψ : IsOddCircle S ψ) :
    HasProjectiveLineDerivAt (fun x => P.scalar (x, z.2)) 0
      (liftSectorParameter S C z).1 (0, (0, (0, ψ))) := by
  have hd := coupled_scalar_first_derivative J hz (coupledSectorChartDirection S ψ hψ)
  have hzero := coupled_scalar_chart_firstJet_eq_zero
    (D := D) (T := T) (S := S) (C := C) (P := P) hS href hscalar J hz ψ hψ
  exact coupled_scalar_lineDerivAt_replace hd hzero (coupledSectorChartDirection_val S ψ hψ)

end ContinuousFlexibility.Statements
