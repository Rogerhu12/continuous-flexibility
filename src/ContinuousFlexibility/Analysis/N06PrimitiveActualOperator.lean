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

private theorem n06_actualOperator_map_budget
    {I X : Type*} (P Q : I → X → Prop)
    (h : ∃ i x, P i x) (hmap : ∀ i x, P i x → Q i x) :
    ∃ i x, Q i x :=
  h.elim (fun i hi => hi.elim (fun x hx => ⟨i, x, hmap i x hx⟩))

private theorem n06_actualOperator_bind_budgets
    {I X J Y Z : Type*} (P : I → X → Prop) (Q : J → Y → Z → Prop)
    (Goal : Prop) (hp : ∃ i x, P i x) (hq : ∃ j y z, Q j y z)
    (hcombine : ∀ i x, P i x → ∀ j y z, Q j y z → Goal) : Goal :=
  hp.elim (fun i hi => hi.elim (fun x hx =>
    hq.elim (fun j hj => hj.elim (fun y hy => hy.elim (fun z hz =>
      hcombine i x hx j y z hz)))))

private def N06ActualParameterPrincipalBudget (N : ℕ) (A : ℝ) : Prop :=
  0 ≤ A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖Mc‖ ≤ A * parameterGrading S N z ∧
        (∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc F) m p * φ p
            ∂canonicalMeasure S K m) =
            ∫ p, (B.inverse F).val.1.1 m p *
              divergenceOperator
                (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
                  (K.dividedDifference (liftSectorParameter S C z) m).a
                  (K.dividedDifference (liftSectorParameter S C z) m).b
                  (K.dividedDifference (liftSectorParameter S C z) m).c) φ p
                ∂canonicalMeasure S K m) ∧
        (∀ F m, K.positive m = false → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0)

private def N06ActualStatePrincipalBudget (N : ℕ) (A : ℝ) : Prop :=
  0 ≤ A ∧
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
        (∀ F m, K.positive m ≠ true → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0)

private def N06ActualLowerSourceBudget (order : ℕ) (Qp Qcol : ℝ) : Prop :=
  0 ≤ Qp ∧ 0 ≤ Qcol ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∃ Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
          ‖Mp‖ ≤ Qp * (stateGrading S order (z.1 - C.referenceState) + |z.2|) ∧
          (∀ i, ‖columns i‖ ≤
            Qcol * (stateGrading S order (z.1 - C.referenceState) + |z.2|)) ∧
          (∀ F m,
            (V.forget (3 / 4 : ℝ) 0 b (Mp F) m : PolarPoint → ℝ)
              =ᵐ[canonicalMeasure S K m] fun p =>
                (if K.positive m then (-1 : ℝ) else 1) *
                  (K.potential z m p - K.potential (C.referenceState, 0) m p) *
                    (B.inverse F).val.1.1 m p) ∧
          ∀ i m,
            (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ)
              =ᵐ[canonicalMeasure S K m]
                n06ActualCanonicalColumnDifference D S C L K z i m

private def N06ActualRelativeSourceBudget (order : ℕ) (Q : ℝ) : Prop :=
  0 ≤ Q ∧
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
                (V.forget (3 / 4 : ℝ) 0 b (Mc F)) m)

set_option diagnostics true in
private theorem n06_actualOperator_principal_state
    (hrefstate : referenceStateConditions D S C) (N : ℕ) (A : ℝ)
    (hp : N06ActualParameterPrincipalBudget (C := C) (B := B)
      (base := base) (ε := ε) N A) :
    N06ActualStatePrincipalBudget (C := C) (B := B)
      (base := base) (ε := ε) N A := by
  refine ⟨hp.1, fun z hz hs => ?_⟩
  obtain ⟨Mc, hMc, hweak, hnegative⟩ :=
    hp.2 (n06PrimitiveParameterOfState hrefstate z hs)
      (n06PrimitiveParameterOfState_mem hrefstate hz hs)
  refine ⟨Mc, hMc.trans_eq (congrArg (fun r : ℝ => A * r)
    (n06PrimitiveParameterOfState_grading hrefstate z hs N)), ?_, ?_⟩
  · intro F m hm φ hφ
    simpa only [n06PrimitiveParameterOfState_lift] using hweak F m hm φ hφ
  · intro F m hm
    exact hnegative F m (Bool.eq_false_of_not_eq_true hm)

set_option diagnostics true in
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
  exact n06_actualOperator_map_budget
    (N06ActualParameterPrincipalBudget (C := C) (B := B) (base := base) (ε := ε))
    (N06ActualStatePrincipalBudget (C := C) (B := B) (base := base) (ε := ε))
    (n06_primitivePrincipal_operator
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε) hT hS h href hcur hprincipal hR hAux)
    (fun N A hp => n06_actualOperator_principal_state
      (D := D) (S := S) (C := C) (B := B) (base := base) (ε := ε)
      h.1.1.1.1.2.2.1 N A hp)

set_option diagnostics true in
private theorem n06_actualOperator_assemble
    (Nc : ℕ) (Qc : ℝ)
    (hc : N06ActualStatePrincipalBudget (C := C) (B := B)
      (base := base) (ε := ε) Nc Qc)
    (Nl : ℕ) (Qp Qcol : ℝ)
    (hl : N06ActualLowerSourceBudget (D := D) (C := C) (L := L) (B := B)
      (base := base) (ε := ε) Nl Qp Qcol) :
    N06ActualRelativeSourceBudget (D := D) (C := C) (L := L) (B := B)
      (base := base) (ε := ε) (max Nc Nl)
      (Qc + Qp + 3 * Qcol * ‖n06InverseScalars B‖) := by
  have hQc : 0 ≤ Qc := hc.1
  have hQp : 0 ≤ Qp := hl.1
  have hQcol : 0 ≤ Qcol := hl.2.1
  let order : ℕ := max Nc Nl
  let Q : ℝ := Qc + Qp + 3 * Qcol * ‖n06InverseScalars B‖
  have hQ : 0 ≤ Q := add_nonneg (add_nonneg hQc hQp)
    (mul_nonneg (mul_nonneg (by norm_num) hQcol)
      (ContinuousLinearMap.opNorm_nonneg (n06InverseScalars B)))
  refine ⟨hQ, fun z hz hs => ?_⟩
  obtain ⟨Mc, hMc, hweak, hnegative⟩ := hc.2 z hz hs
  obtain ⟨Mp, columns, hMp, hcolumnnorm, hMpfield, hcolumns⟩ := hl.2.2 z hz hs
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

set_option diagnostics true in
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
  exact n06_actualOperator_bind_budgets
    (N06ActualStatePrincipalBudget (C := C) (B := B) (base := base) (ε := ε))
    (N06ActualLowerSourceBudget (D := D) (C := C) (L := L) (B := B)
      (base := base) (ε := ε))
    (∃ order : ℕ, ∃ Q : ℝ, N06ActualRelativeSourceBudget
      (D := D) (C := C) (L := L) (B := B) (base := base) (ε := ε) order Q)
    (n06_primitiveActual_principal_sources
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε) hT hS h href hcur hprincipal hR hAux)
    (n06_primitiveActual_lowerOrder_sources
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε) hT hS h href hcur)
    (fun Nc Qc hc Nl Qp Qcol hl =>
      ⟨max Nc Nl, Qc + Qp + 3 * Qcol * ‖n06InverseScalars B‖,
        n06_actualOperator_assemble (D := D) (S := S) (C := C) (L := L)
          (K := K) (V := V) (b := b) (B := B) (base := base) (ε := ε)
          Nc Qc hc Nl Qp Qcol hl⟩)

end ContinuousFlexibility.Statements
