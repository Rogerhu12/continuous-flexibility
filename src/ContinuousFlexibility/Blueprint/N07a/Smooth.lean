import ContinuousFlexibility.Analysis.N07aActualForward
import ContinuousFlexibility.Analysis.N07aInverseFromForward
import ContinuousFlexibility.Analysis.N07aStageRestriction

/-!
# N07a: the smooth tame family of the same physical inverse

Source: `paper/flexible-surface-readable/08-stable-inverse.tex` lines 790–815.
Task: `docs/tasks/N07a-Smooth.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

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

variable (A : RadialReference) (T : MaterialData) (S : PhysicalSpacesData)
  (C : NonlinearGeometryData S) (R : ReturnEquationData S)
  (L : ReturnCorrectionData S) (K : CanonicalData S) (V : VolumeModelData S K)
  (b : ℕ) (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)
  (base loss : ℕ) (ε : ℝ)

theorem N07aSmooth
    (hT : IsMaterialData A.val T) (hS : IsPhysicalSpaces A.val T S)
    (h06 : NonlinearPropertiesThrough06 A.val T S C R L K V b B P base loss ε)
    (G : ScalarInverseData S)
    (hLinear : ScalarLinearInverseProperties A.val S C L G base ε)
    (hTame : H01Statement ∧ H02Statement) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ScalarInverseProperties A.val S C L G base' ε' := by
  have h01 : N01Properties A.val T S C base loss ε := h06.1.1.1.1.1
  have h02 : N02Properties A.val T S C R base ε := h06.1.1.1.1.2
  have h03 : N03Properties A.val T S C R L base ε := h06.1.1.1.2
  let data := n07a_exists_actualNormalizedForward A.property hT hS h01 h02 h03
  let base' : ℕ := data.choose
  have hbase : base ≤ base' := data.choose_spec.1
  let ε' : ℝ := data.choose_spec.2.choose
  have he : 0 < ε' := data.choose_spec.2.choose_spec.1
  have hele : ε' ≤ ε := data.choose_spec.2.choose_spec.2.1
  let F : (StateDirections S × ℝ) → N07aNormalizedUnknown A.property hT hS →L[ℝ] S.Source :=
    data.choose_spec.2.choose_spec.2.2.choose
  have hF := data.choose_spec.2.choose_spec.2.2.choose_spec.1
  have hdecode := data.choose_spec.2.choose_spec.2.2.choose_spec.2
  exact ⟨base', hbase, ε', he, hele,
    n07a_scalarInverse_smooth_of_actualForward A.property hT hS h01.2.2.1
      (n07a_scalarLinearInverse_restrict hLinear hbase hele) F hF hdecode⟩

end ContinuousFlexibility.Blueprint
