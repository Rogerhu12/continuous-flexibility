module

public import ContinuousFlexibility.Analysis.N07aAngularReferenceLowJets
public import ContinuousFlexibility.Analysis.N07aAngularReferenceSource
public import ContinuousFlexibility.Analysis.N07aReferenceTestOperator
public import ContinuousFlexibility.Analysis.N07aReferenceNuColumn

/-!
# The reference scalar columns are the actual differential columns

The zero reference return residual makes the correction vanish on every
decoded height pair. Applying it to the actual left cutoff identifies the
existing canonical scalar column with the radial differential expression.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

theorem n07a_referenceHeightPair_operator_eq_original
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (u : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (L.coefficients (C.referenceState, 0)) (heightPairField S u) p =
      divergenceOperator (originalCoefficients D S C (C.referenceState, 0))
        (heightPairField S u) p := by
  have hres := n07a_referenceReturnResidual_eq_zero hS hT h01 h02
  have h := h03.2.2.2.2.2.1 (C.referenceState, 0)
    (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector u p hp
  let E : CircleSpace S →ₗ[ℝ] (HeightPair S →ₗ[ℝ] S.Source) := L.error (C.referenceState, 0)
  have hE : E (R.residual (C.referenceState, 0)) = 0 :=
    (congrArg E hres).trans E.map_zero
  have hEu : E (R.residual (C.referenceState, 0)) u = (0 : S.Source) :=
    congrArg (fun A : HeightPair S →ₗ[ℝ] S.Source => A u) hE
  have hdecode := congrArg (fun v : S.Source => (S.height (3 / 4 : ℝ)).decode v.val p) hEu
  have hdz : (S.height (3 / 4 : ℝ)).decode (0 : (S.height (3 / 4 : ℝ)).Space) p = 0 :=
    congrFun (S.height (3 / 4 : ℝ)).decode.map_zero p
  exact (sub_eq_zero.mp (h.trans (hdecode.trans hdz))).symm

theorem n07a_referenceCutoff_column
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (L.coefficients (C.referenceState, 0))
        (fun q : PolarPoint => S.chiLeft q.1) p =
      n07aReferenceDifferential D (fun q : PolarPoint => S.chiLeft q.1) p := by
  have he : heightPairField S (0, 1) = (fun q : PolarPoint => S.chiLeft q.1) := by
    funext q
    simp only [heightPairField, map_zero, Pi.zero_apply, one_mul, zero_add]
  have h := n07a_referenceHeightPair_operator_eq_original hS hT h01 h02 h03 (0, 1) hp
  rw [he] at h
  have hχ := hS.2.2.1.1.comp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : PolarPoint → ℝ))
  exact h.trans ((n07a_originalReference_divergence hS hT h01 hχ hp).trans
    (n07a_referenceDifferential_eq_radialPDE
      (h01.1.1.choose_spec.1.2.2.1.1.differentiable (by simp) p.1) hχ.contDiffAt).symm)

theorem n07a_referenceDifferential_add_on
    {U : Set PolarPoint} (hU : IsOpen U) {f g : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {p : PolarPoint} (hp : p ∈ U) :
    n07aReferenceDifferential D (fun q => f q + g q) p =
      n07aReferenceDifferential D f p + n07aReferenceDifferential D g p := by
  have ha := n07a_referencePartials_eq_mixed hU (hf.add hg) hp
  have h₁ := n07a_referencePartials_eq_mixed hU hf hp
  have h₂ := n07a_referencePartials_eq_mixed hU hg hp
  simp only [n07aReferenceDifferential, ha.1, ha.2.1, ha.2.2,
    h₁.1, h₁.2.1, h₁.2.2, h₂.1, h₂.2.1, h₂.2.2,
    n07a_mixedDerivative_add_on hU hf hg _ _ hp]
  ring

theorem n07a_referenceDifferential_const_mul_on
    {U : Set PolarPoint} (hU : IsOpen U) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (a : ℝ) {p : PolarPoint} (hp : p ∈ U) :
    n07aReferenceDifferential D (fun q => a * f q) p =
      a * n07aReferenceDifferential D f p := by
  have haf : ContDiffOn ℝ ∞ (fun q : PolarPoint => a * f q) U :=
    contDiffOn_const.mul hf
  have ha := n07a_referencePartials_eq_mixed hU haf hp
  have h₁ := n07a_referencePartials_eq_mixed hU hf hp
  simp only [n07aReferenceDifferential, ha.1, ha.2.1, ha.2.2,
    h₁.1, h₁.2.1, h₁.2.2, spaces_mixedDerivative_const_mul]
  ring

end ContinuousFlexibility.Analysis
