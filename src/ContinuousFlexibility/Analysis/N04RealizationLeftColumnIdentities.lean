module

public import ContinuousFlexibility.Analysis.CoupledScalarHeightDerivative
public import ContinuousFlexibility.Analysis.N06LeftColumnPhysical
public import ContinuousFlexibility.Analysis.N07aNuScalarState

/-!
# The actual left column in the reduced scalar geometry

The left height is the existing radial cutoff. Its angular error is zero.
On the compact support of its radial derivative, the actual optical
controls vanish as germs. Equality of the full residual parameter curves
therefore identifies the two genuine derivatives. Outside that support,
both divergence expressions are zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub

theorem n04Realization_leftHeight_decode (S : PhysicalSpacesData) :
    scalarCommonHeightDecode S (0, 1) = n06ReferenceLeftField S.chiLeft := by
  funext p
  simp only [scalarCommonHeightDecode, n06ReferenceLeftField,
    map_zero, Pi.zero_apply, one_mul, zero_add]

theorem n04Realization_leftHeight_error
    {S : PhysicalSpacesData} (hχ : ContDiff ℝ ∞ S.chiLeft)
    (B R : PolarPoint → ℝ) (p : PolarPoint) :
    scalarCorrectionError B R (scalarCommonHeightDecode S (0, 1)) p = 0 := by
  have ht : angularPartial (n06ReferenceLeftField S.chiLeft) = fun _ => (0 : ℝ) :=
    funext (fun q =>
      angularPartial_radialHeightField (hχ.differentiable (by simp) q.1))
  rw [n04Realization_leftHeight_decode]
  simp only [scalarCorrectionError, ht, mul_zero, angularPartial_const]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n04Realization_scalarLeft_zero
    (hχ : ContDiff ℝ ∞ S.chiLeft) {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ r, r ∉ J → deriv S.chiLeft r = 0)
    (x : ScalarWeightedState S) {p : PolarPoint} (hp : p.1 ∉ J) :
    scalarStateOperator D S x (0, 1) p = 0 := by
  rw [scalarStateOperator, n04Realization_leftHeight_decode]
  exact n06_divergence_radial_cutoff_zero
    { a := scalarStateA D S x
      b := scalarStateB D S x
      c := scalarStateCorrectedC D S x } hχ hJ hzero hp

theorem n04Realization_scalarLeft_hasDerivAt
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {x : ScalarWeightedState S}
    (hg : ScalarStateGeometry D S x) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    HasDerivAt
      (fun t : ℝ => scalarStateResidual D S (x + t • scalarHeightDirection S (0, 1)) p)
      (scalarStateOperator D S x (0, 1) p) 0 := by
  simpa only [n04Realization_leftHeight_error hS.2.2.1.1, mul_zero, add_zero] using
    hasDerivAt_scalarStateResidual_heightDirection hD hT hS hg (0, 1) hp

variable {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- Remove the vanishing angular error before specializing the complete
derivative curve and coefficients to the dependent physical state. -/
private theorem n04Realization_leftDerivative_of_error
    (hχ : ContDiff ℝ ∞ S.chiLeft) (f : ℝ → ℝ) (A : SymmetricCoefficients)
    (B R : PolarPoint → ℝ) (q : ℝ) (p : PolarPoint)
    (hd : HasDerivAt f
      (divergenceOperator A (heightPairField S (0, 1)) p +
        q * scalarCorrectionError B R (heightPairField S (0, 1)) p) 0) :
    HasDerivAt f (divergenceOperator A (n06ReferenceLeftField S.chiLeft) p) 0 := by
  have he : heightPairField S (0, 1) = scalarCommonHeightDecode S (0, 1) := rfl
  rw [he, n04Realization_leftHeight_error hχ, mul_zero, add_zero] at hd
  simpa only [n04Realization_leftHeight_decode] using hd

theorem n04Realization_originalLeft_hasDerivAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    HasDerivAt
      (fun t : ℝ => scalarResidualField D S C
        (z.1 + coupledScalarAction t ((0, 1), (0, (0, 0))), z.2) p)
      (divergenceOperator (originalCoefficients D S C z)
        (n06ReferenceLeftField S.chiLeft) p) 0 := by
  exact n04Realization_leftDerivative_of_error hS.2.2.1.1
    (fun t : ℝ => scalarResidualField D S C
      (z.1 + coupledScalarAction t ((0, 1), (0, (0, 0))), z.2) p)
    (originalCoefficients D S C z) (residualErrorCoefficient D S C z)
    (scalarResidualField D S C z) z.2 p
    (coupled_hasDerivAt_scalarResidualField_heightDirection hT hS h01 hz hs (0, 1) hp)

/-- The profile germ comparison holds along the entire left-height
parameter curve, before taking its derivative. -/
theorem n04Realization_leftResidual_curves_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ)
    {p : PolarPoint} (hpos : 0 < deriv D.w p.1) :
    (fun t : ℝ => scalarResidualField D S C
      (z.1 + coupledScalarAction t ((0, 1), (0, (0, 0))), z.2) p) =
    (fun t : ℝ => scalarStateResidual D S
      (n07aNuScalarState hT hS h01.1.2.2.2.1 z +
        t • scalarHeightDirection S (0, 1)) p) := by
  let y : ScalarWeightedState S := n07aNuScalarState hT hS h01.1.2.2.2.1 z
  have hw := contDiff_stateProfile_of_n01 hS hT h01 z.1
  have hyw := scalarStateProfile_contDiff h01.1.1 hT hS y
  have he : stateProfile D S C z.1 =ᶠ[𝓝 p.1] scalarStateProfile D S y := by
    rw [show scalarStateProfile D S y =
      fun r => D.w r * Real.exp (z.1.2.1 * D.chi r) from
        n07aNuScalarState_profile hT hS h01.1.2.2.2.1 z]
    exact n07a_stateProfile_eq_nuProfile_germ h01.1.1.choose_spec.1.2.2.1.1
      h01.2.2.2.1 z.1 hpos
  funext t
  rw [coupled_scalarResidualField_add_heightDirection,
    scalarStateResidual_add_heightDirection]
  change normalizedResidual (stateProfile D S C z.1) (stateRadialHeight D S C z.1)
      (heightFamily (stateU S z.1) (scalarCommonHeightDecode S (0, 1)) t) z.2 p =
    normalizedResidual (scalarStateProfile D S y) (scalarStatePrimitive D S y)
      (heightFamily (stateU S z.1) (scalarCommonHeightDecode S (0, 1)) t) z.2 p
  exact n07a_normalizedResidual_radialProfile_congr
    (stateRadialHeight_contDiff_of_contDiff hw)
    (scalarStatePrimitive_contDiff h01.1.1 hT hS y)
    (stateRadialHeight_hasDerivAt_of_contDiff hw)
    (scalarStatePrimitive_hasDerivAt h01.1.1 hT hS y)
    (hw.differentiable (by simp) p.1) (hyw.differentiable (by simp) p.1)
    (contDiff_heightFamily (neighborhood_stateU_contDiff hT hS z.1)
      (scalarCommonHeightDecode_contDiff hT hS (0, 1)) t)
    he.eq_of_nhds he.deriv_eq z.2

/-- The current physical column is the reduced scalar left derivative
on the same state. N03 is used only through its proved original-column
identity; no estimate on the correction operator is needed. -/
theorem n04Realization_actualLeft_eq_reduced
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hg : ScalarStateGeometry D S (n07aNuScalarState hT hS h01.1.2.2.2.1 z))
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    n06CurrentLeftColumn S L z p =
      scalarStateOperator D S (n07aNuScalarState hT hS h01.1.2.2.2.1 z) (0, 1) p := by
  rw [n06_currentLeftColumn_eq_original hS h03 hz hs p]
  obtain ⟨J, hJ, _, hpos, hzero⟩ := hS.2.2.1.2.2
  by_cases hpJ : p.1 ∈ J
  · have hactual := n04Realization_originalLeft_hasDerivAt hT hS h01 hz hs hp
    rw [n04Realization_leftResidual_curves_eq hT hS h01 z (hpos p.1 hpJ)] at hactual
    exact hactual.unique (n04Realization_scalarLeft_hasDerivAt h01.1.1 hT hS hg hp)
  · exact (n06_divergence_radial_cutoff_zero (originalCoefficients D S C z)
      hS.2.2.1.1 hJ.isClosed hzero hpJ).trans
        (n04Realization_scalarLeft_zero hS.2.2.1.1 hJ.isClosed hzero _ hpJ).symm

end ContinuousFlexibility.Analysis
