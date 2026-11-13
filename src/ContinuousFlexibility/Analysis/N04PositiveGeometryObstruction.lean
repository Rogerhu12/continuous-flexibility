import ContinuousFlexibility.Analysis.N04PositiveGeometryBadBuffer
import ContinuousFlexibility.Analysis.N04PositiveGeometryCurrentCost
import ContinuousFlexibility.Analysis.N04RealizationLeadOptical

/-!
# The supplied-buffer quantifier obstructs positive geometry

The historical supplied-buffer draft allows every normalization buffer.
Its matching condition fixes the transport to the identity throughout the
buffer's middle interval. A legal choice can make the remaining right
transition arbitrarily narrow on infinitely many positive components.

The actual inverse-angle atom must still attain the independently variable
source label at the right endpoint. Its order-one spatial value estimate
therefore imposes the reciprocal-width cost proved in `CurrentCost`.
The buffer constructed in `BadBuffer` violates every such uniform cost,
including every fixed parameter loss and every material power.

All witnesses used here come from existing unconditional constructions.
No positive-geometry or realization blueprint theorem is imported.
That exact draft is retained as
`N04RealizationSuppliedBufferPositiveGeometryObligation`. The corrected
`N04RealizationPositiveGeometryObligation` instead chooses its buffer.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

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

/-- The universal supplied-buffer version of the positive geometry
obligation is false. The obstruction already follows from the first
spatial derivative of the genuine inverse-angle atom. -/
theorem n04Realization_not_positiveGeometryObligation :
    ¬ N04RealizationSuppliedBufferPositiveGeometryObligation := by
  intro hpositive
  have W : N04RealizationStart := n04RealizationStart_nonempty.some
  have X : N04RealizationChoice W :=
    (n04RealizationChoice_nonempty n04Realization_opticalObligation W).some
  have hborder : RadialTrueBorder W.D := W.radial.2.2.2.1
  have hf : Continuous (deriv W.D.w) :=
    (n04b_profileGeometry_of_through03 W.through03).2.2.1.1.continuous_deriv (by simp)
  have e : ℕ ≃ N04WholePieceIndex W.D :=
    (n04WholePiece_exists_enumeration (D := W.D) hf).some
  have B₀ : N04PositiveNormalizationBuffer
      W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi) :=
    (n04PositiveNormalizationBuffer_nonempty hf hborder.2.1 hborder.2.2.1).some
  have hfamily := n04Coordinates_exists_positive_reference_family
    W.hT W.hS W.through03 W.field X.e₀ X.src (n := 4) (by norm_num)
  let Y := hfamily.choose
  let H := hfamily.choose_spec.choose
  have hreference : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H :=
    hfamily.choose_spec.choose_spec
  have hbad := n04PositiveGeometry_exists_bad_buffer W X Y H hreference B₀
  let buffer := hbad.choose
  have hcurrent := hpositive W X Y H hreference e buffer
  let b := hcurrent.choose
  have hcurrent₁ := hcurrent.choose_spec
  let ε := hcurrent₁.choose
  have hcurrent₂ := hcurrent₁.choose_spec
  let lower := hcurrent₂.choose
  have hcurrent₃ := hcurrent₂.choose_spec
  let upper := hcurrent₃.choose
  have hcurrent₄ := hcurrent₃.choose_spec
  let τ := hcurrent₄.choose
  have hcurrent₅ := hcurrent₄.choose_spec
  let σ := hcurrent₅.choose
  have hcurrent₆ := hcurrent₅.choose_spec
  let Q := hcurrent₆.choose
  have hproperties := hcurrent₆.choose_spec
  let G : N04RealizationGauge :=
    N04RealizationGauge.mk W X e Y H τ σ Q buffer.region
  have hcost := G.n04PositiveGeometry_geometryData_forces_right_cost
    (0 : (W.S.height (3 / 4 : ℝ)).Space)
    hproperties.1 hproperties.2.1 hproperties.2.2.1 hreference
    (fun i => (hproperties.2.2.2.2.1 i).1)
    buffer lower upper hproperties.2.2.2.1 (hproperties.2.2.2.2.2 0)
  exact hbad.choose_spec.2.2
    ⟨hcost.choose, hcost.choose_spec.choose,
      hcost.choose_spec.choose_spec.1, fun i =>
        hcost.choose_spec.choose_spec.2 i (n04PositiveGeometry_rightSource W X i)
          (n04PositiveGeometry_rightSource_spec W X i)⟩

end ContinuousFlexibility.Analysis

open Lean in
run_cmd do
  let axioms ← collectAxioms
    ``ContinuousFlexibility.Analysis.n04Realization_not_positiveGeometryObligation
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in n04Realization_not_positiveGeometryObligation"

#print axioms ContinuousFlexibility.Analysis.n04RealizationStart_nonempty
#print axioms ContinuousFlexibility.Analysis.n04Realization_not_positiveGeometryObligation
