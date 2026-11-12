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

private theorem n06_actualOperator_bind_state_fields
    {X Y Z W : Type*} (P : X → Prop) (Q : Y → Z → Prop)
    (R : X → Y → Z → W → Prop)
    (hp : ∃ x, P x) (hq : ∃ y z, Q y z)
    (hmap : ∀ x y z, P x → Q y z → ∃ w, R x y z w) :
    ∃ x y z w, R x y z w :=
  hp.elim (fun x hx => hq.elim (fun y hy => hy.elim (fun z hz =>
    ⟨x, y, z, hmap x y z hx hz⟩)))

private def N06ActualPrincipalStateFields (order : ℕ) (Qc : ℝ)
    (z : AnnularState S × ℝ)
    (Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b) : Prop :=
        ‖Mc‖ ≤ Qc * (stateGrading S order (z.1 - C.referenceState) + |z.2|) ∧
        (∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc F) m p * φ p
            ∂canonicalMeasure S K m) =
            ∫ p, (B.inverse F).val.1.1 m p * divergenceOperator
              (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
                (K.dividedDifference z m).a (K.dividedDifference z m).b
                (K.dividedDifference z m).c) φ p ∂canonicalMeasure S K m) ∧
        (∀ F m, K.positive m ≠ true → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0)

private def N06ActualLowerStateFields (order : ℕ) (Qp Qcol : ℝ)
    (z : AnnularState S × ℝ)
    (Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b) : Prop :=
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

private def N06ActualRelativeStateFields (order : ℕ) (Q : ℝ)
    (z : AnnularState S × ℝ)
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b) : Prop :=
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

private theorem n06_actualOperator_constant_nonneg {Qc Qp Qcol s : ℝ}
    (hc : 0 ≤ Qc) (hp : 0 ≤ Qp) (hcol : 0 ≤ Qcol) (hs : 0 ≤ s) :
    0 ≤ Qc + Qp + 3 * Qcol * s :=
  add_nonneg (add_nonneg hc hp)
    (mul_nonneg (mul_nonneg (by norm_num) hcol) hs)

private theorem n06_actualOperator_grading_max (Nc Nl : ℕ)
    (x : AnnularState S) (t : ℝ) :
    (stateGrading S Nc x + t ≤ stateGrading S (max Nc Nl) x + t) ∧
    (stateGrading S Nl x + t ≤ stateGrading S (max Nc Nl) x + t) :=
  ⟨add_le_add_right (solve_stateGrading_monotone S (le_max_left Nc Nl) x) t,
    add_le_add_right (solve_stateGrading_monotone S (le_max_right Nc Nl) x) t⟩

private theorem n06_actualOperator_map_norm
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    {Qc Qp Qcol ρc ρl ρ : ℝ}
    (hQc : 0 ≤ Qc) (hQp : 0 ≤ Qp) (hQcol : 0 ≤ Qcol)
    (hρc : ρc ≤ ρ) (hρl : ρl ≤ ρ)
    (hc : ‖Mc‖ ≤ Qc * ρc) (hp : ‖Mp‖ ≤ Qp * ρl)
    (hcolumns : ∀ i, ‖columns i‖ ≤ Qcol * ρl) :
    ‖n06ActualRelativeMap B Mc Mp columns‖ ≤
      (Qc + Qp + 3 * Qcol * ‖n06InverseScalars B‖) * ρ := by
  exact norm_n06ActualRelativeMap_le
    (S := S) (K := K) (V := V) (b := b) (B := B)
    (Qc := Qc) (Qp := Qp) (Qcol := Qcol) (δ := ρ) Mc Mp columns
    (hc.trans (mul_le_mul_of_nonneg_left hρc hQc))
    (hp.trans (mul_le_mul_of_nonneg_left hρl hQp))
    (fun i => (hcolumns i).trans (mul_le_mul_of_nonneg_left hρl hQcol))

private theorem n06_actualOperator_map_source
    (order : ℕ) (Qp Qcol : ℝ) (z : AnnularState S × ℝ)
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (hl : N06ActualLowerStateFields (D := D) (C := C) (L := L) (B := B)
      order Qp Qcol z Mp columns) :
    ∀ F m,
      (V.forget (3 / 4 : ℝ) 0 b (F + n06ActualRelativeMap B Mc Mp columns F) m :
        PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          n06CurrentRelativeSourceField D S C L K z (B.inverse F).val.1
            (V.forget (3 / 4 : ℝ) 0 b F) (V.forget (3 / 4 : ℝ) 0 b (Mc F)) m := by
  exact n06ActualRelativeMap_forget
    (D := D) (S := S) (C := C) (L := L) (K := K)
    (V := V) (b := b) (B := B) (z := z)
    Mc Mp columns hl.2.2.1 hl.2.2.2

private theorem n06_actualOperator_assemble_maps
    (Nc Nl : ℕ) (Qc Qp Qcol : ℝ)
    (hQc : 0 ≤ Qc) (hQp : 0 ≤ Qp) (hQcol : 0 ≤ Qcol)
    (z : AnnularState S × ℝ)
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (hc : N06ActualPrincipalStateFields (C := C) (B := B) Nc Qc z Mc)
    (hl : N06ActualLowerStateFields (D := D) (C := C) (L := L) (B := B)
      Nl Qp Qcol z Mp columns) :
    N06ActualRelativeStateFields (D := D) (C := C) (L := L) (B := B)
      (max Nc Nl) (Qc + Qp + 3 * Qcol * ‖n06InverseScalars B‖)
      z Mc Mp columns (n06ActualRelativeMap B Mc Mp columns) := by
  have hgrade := n06_actualOperator_grading_max
    (S := S) Nc Nl (z.1 - C.referenceState) |z.2|
  refine ⟨rfl, ?_, hc.2.1, hc.2.2, ?_⟩
  · exact n06_actualOperator_map_norm
      (S := S) (K := K) (V := V) (b := b) (B := B) Mc Mp columns
      (Qc := Qc) (Qp := Qp) (Qcol := Qcol)
      (ρc := stateGrading S Nc (z.1 - C.referenceState) + |z.2|)
      (ρl := stateGrading S Nl (z.1 - C.referenceState) + |z.2|)
      (ρ := stateGrading S (max Nc Nl) (z.1 - C.referenceState) + |z.2|)
      hQc hQp hQcol hgrade.1 hgrade.2 hc.1 hl.1 hl.2.1
  · exact n06_actualOperator_map_source
      (D := D) (S := S) (C := C) (L := L) (K := K)
      (V := V) (b := b) (B := B) Nl Qp Qcol z Mc Mp columns hl

private theorem n06_actualOperator_assemble_state
    (Nc Nl : ℕ) (Qc Qp Qcol : ℝ)
    (hQc : 0 ≤ Qc) (hQp : 0 ≤ Qp) (hQcol : 0 ≤ Qcol)
    (z : AnnularState S × ℝ)
    (hc : ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      N06ActualPrincipalStateFields (C := C) (B := B) Nc Qc z Mc)
    (hl : ∃ Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
        N06ActualLowerStateFields (D := D) (C := C) (L := L) (B := B)
          Nl Qp Qcol z Mp columns) :
    ∃ Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
    ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
    ∃ M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      N06ActualRelativeStateFields (D := D) (C := C) (L := L) (B := B)
        (max Nc Nl) (Qc + Qp + 3 * Qcol * ‖n06InverseScalars B‖) z Mc Mp columns M := by
  exact n06_actualOperator_bind_state_fields
    (N06ActualPrincipalStateFields (C := C) (B := B) Nc Qc z)
    (N06ActualLowerStateFields (D := D) (C := C) (L := L) (B := B) Nl Qp Qcol z)
    (N06ActualRelativeStateFields (D := D) (C := C) (L := L) (B := B)
      (max Nc Nl) (Qc + Qp + 3 * Qcol * ‖n06InverseScalars B‖) z)
    hc hl (fun Mc Mp columns hc hl =>
      ⟨n06ActualRelativeMap B Mc Mp columns,
        n06_actualOperator_assemble_maps
          (D := D) (S := S) (C := C) (L := L) (K := K) (V := V) (b := b) (B := B)
          Nc Nl Qc Qp Qcol hQc hQp hQcol z Mc Mp columns hc hl⟩)

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
  refine ⟨n06_actualOperator_constant_nonneg hc.1 hl.1 hl.2.1
    (ContinuousLinearMap.opNorm_nonneg (n06InverseScalars B)), ?_⟩
  intro z hz hs
  exact n06_actualOperator_assemble_state
    (D := D) (S := S) (C := C) (L := L) (K := K) (V := V) (b := b) (B := B)
    Nc Nl Qc Qp Qcol hc.1 hl.1 hl.2.1 z (hc.2 z hz hs) (hl.2.2 z hz hs)

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
