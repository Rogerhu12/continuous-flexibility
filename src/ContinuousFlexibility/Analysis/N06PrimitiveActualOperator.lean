import ContinuousFlexibility.Analysis.N06PrimitivePrincipalOperator
import ContinuousFlexibility.Analysis.N06PrimitiveLowerOrderSources
import ContinuousFlexibility.Analysis.N06ActualRelativeMap
import ContinuousFlexibility.Analysis.SolveStateSpaces

/-!
# The actual relative source on the retained N05 graph

The principal source, signed potential source, and all three scalar
columns act on the same source level and use the same reference inverse.
Their uniform orders are enlarged to one order. Their literal source
identities are retained for the subsequent physical Green argument.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis CanonicalGeometry

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
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

local instance n06PrimitiveActualOperatorLevelGroup :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedAddCommGroup _
local instance n06PrimitiveActualOperatorLevelSpace :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedSpace _
local instance n06PrimitiveActualOperatorGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06PrimitiveActualOperatorGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

theorem n06_primitiveActual_principal_sources
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖Mc‖ ≤ A * (stateGrading S N (z.1 - C.referenceState) + |z.2|) ∧
        (∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc F) m p * φ p
            ∂canonicalMeasure S K m) =
            ∫ p, (B.inverse F).val.1.1 m p * divergenceOperator
              (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
                (K.dividedDifference z m).a (K.dividedDifference z m).b
                (K.dividedDifference z m).c) φ p ∂canonicalMeasure S K m) ∧
        (∀ F m, K.positive m ≠ true → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0) := by
  have hrefstate : referenceStateConditions D S C := h.1.1.1.1.2.2.1
  obtain ⟨N, A, hA, hfamily⟩ :=
    n06_primitivePrincipal_operator hT hS h href hcur hprincipal hR hAux
  refine ⟨N, A, hA, fun z hz hs => ?_⟩
  obtain ⟨Mc, hMc, hweak, hnegative⟩ :=
    hfamily (n06PrimitiveParameterOfState hrefstate z hs)
      (n06PrimitiveParameterOfState_mem hrefstate hz hs)
  refine ⟨Mc, hMc.trans_eq (congrArg (fun r : ℝ => A * r)
    (n06PrimitiveParameterOfState_grading hrefstate z hs N)), ?_, ?_⟩
  · intro F m hm φ hφ
    simpa only [n06PrimitiveParameterOfState_lift] using hweak F m hm φ hφ
  · intro F m hm
    exact hnegative F m (Bool.eq_false_of_not_eq_true hm)

/-- This is a pointwise analytic source package. Its weak principal
pairing and full source identity are the inputs to the physical closure;
no perturbed physical relation is assumed in its construction. -/
theorem n06_primitiveActual_relative_source_package
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K) :
    ∃ order : ℕ, ∃ Q : ℝ, 0 ≤ Q ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
      ∃ M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        M = n06ActualRelativeMap B Mc Mp columns ∧
        ‖M‖ ≤ Q * (stateGrading S order (z.1 - C.referenceState) + |z.2|) ∧
        (∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc F) m p * φ p
            ∂canonicalMeasure S K m) =
            ∫ p, (B.inverse F).val.1.1 m p * divergenceOperator
              (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
                (K.dividedDifference z m).a (K.dividedDifference z m).b
                (K.dividedDifference z m).c) φ p ∂canonicalMeasure S K m) ∧
        (∀ F m, K.positive m ≠ true → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0) ∧
        (∀ F m,
          (V.forget (3 / 4 : ℝ) 0 b (F + M F) m : PolarPoint → ℝ)
            =ᵐ[canonicalMeasure S K m]
              n06CurrentRelativeSourceField D S C L K z (B.inverse F).val.1
                (V.forget (3 / 4 : ℝ) 0 b F)
                (V.forget (3 / 4 : ℝ) 0 b (Mc F)) m) := by
  obtain ⟨Nc, Qc, hQc, hc⟩ :=
    n06_primitiveActual_principal_sources hT hS h href hcur hprincipal hR hAux
  obtain ⟨Nl, Qp, Qcol, hQp, hQcol, hl⟩ :=
    n06_primitiveActual_lowerOrder_sources hT hS h href hcur
  let order : ℕ := max Nc Nl
  let Q : ℝ := Qc + Qp + 3 * Qcol * ‖n06InverseScalars B‖
  have hQ : 0 ≤ Q := add_nonneg (add_nonneg hQc hQp)
    (mul_nonneg (mul_nonneg (by norm_num) hQcol)
      (ContinuousLinearMap.opNorm_nonneg (n06InverseScalars B)))
  refine ⟨order, Q, hQ, fun z hz hs => ?_⟩
  obtain ⟨Mc, hMc, hweak, hnegative⟩ := hc z hz hs
  obtain ⟨Mp, columns, hMp, hcolumnnorm, hMpfield, hcolumns⟩ := hl z hz hs
  have hgradec : stateGrading S Nc (z.1 - C.referenceState) + |z.2| ≤
      stateGrading S order (z.1 - C.referenceState) + |z.2| :=
    add_le_add_right (solve_stateGrading_monotone S (le_max_left Nc Nl)
      (z.1 - C.referenceState)) _
  have hgradel : stateGrading S Nl (z.1 - C.referenceState) + |z.2| ≤
      stateGrading S order (z.1 - C.referenceState) + |z.2| :=
    add_le_add_right (solve_stateGrading_monotone S (le_max_right Nc Nl)
      (z.1 - C.referenceState)) _
  refine ⟨Mc, Mp, columns, n06ActualRelativeMap B Mc Mp columns, rfl, ?_,
    hweak, hnegative, ?_⟩
  · exact norm_n06ActualRelativeMap_le (B := B) Mc Mp columns
      (hMc.trans (mul_le_mul_of_nonneg_left hgradec hQc))
      (hMp.trans (mul_le_mul_of_nonneg_left hgradel hQp))
      (fun i => (hcolumnnorm i).trans (mul_le_mul_of_nonneg_left hgradel hQcol))
  · exact n06ActualRelativeMap_forget (B := B) Mc Mp columns hMpfield hcolumns

end ContinuousFlexibility.Statements
