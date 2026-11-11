import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.SpacesTraceRestriction
import ContinuousFlexibility.Scalar.WeightedCoefficientAlgebra

/-!
# Material bounds for the actual coefficient families

The complete coefficient power in N01 and N04 is charged once. The original
coefficient and flow variations retain their actual height-weight gain and
one-high-factor bounds. The canonical jet bound retains exactly the gain
recorded in N04, without adding an unproved height factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

local instance n07aCoefficientMaterialInst1 (S : PhysicalSpacesData) : AddCommGroup (AnnularState S) := inferInstance

local instance n07aCoefficientMaterialInst2 (S : PhysicalSpacesData) : Module ℝ (AnnularState S) := inferInstance

local instance n07aCoefficientMaterialInst3 (S : PhysicalSpacesData) : TopologicalSpace (AnnularState S) := inferInstance

local instance n07aCoefficientMaterialInst4 (S : PhysicalSpacesData) : AddGroup (AnnularState S) :=
  (inferInstance : AddCommGroup (AnnularState S)).toAddGroup

local instance n07aCoefficientMaterialInst5 (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (inferInstance : Module ℝ (AnnularState S)).toSMul

local instance n07aCoefficientMaterialInst6 (S : PhysicalSpacesData) : Sub (AnnularState S) :=
  (inferInstance : AddCommGroup (AnnularState S)).toSub

private theorem n07a_oneHighVariationWeight_nonneg
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x : E)
    {k : ℕ} (v : Fin k → E) :
    0 ≤ oneHighVariationWeight p base high x v := by
  classical
  unfold oneHighVariationWeight
  exact add_nonneg
    (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
      (Finset.prod_nonneg fun _ _ => apply_nonneg _ _))
    (Finset.sum_nonneg fun _ _ => mul_nonneg (apply_nonneg _ _)
      (Finset.prod_nonneg fun _ _ => apply_nonneg _ _))

private theorem n07a_absorb_material_factor {A K H E M W f : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hE : E ≤ K * M) (hf : f ≤ A * H * E * W) :
    f ≤ (A * K) * H * M * W := by
  have hpower := mul_le_mul_of_nonneg_left hE (mul_nonneg hA hH)
  exact hf.trans ((mul_le_mul_of_nonneg_right hpower hW).trans_eq (by ring))

private def n07aCoefficientVariationBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (k s : ℕ) (A : ℝ) : Prop :=
  ∀ (m : ℕ) (i : Fin 3) (a b : ℕ) (p : PolarPoint),
    a + b ≤ s → p.1 ∈ D.cells m →
    ∃ J : SmoothDirections (E := AnnularState S × ℝ) (F := ℝ)
      (stateNeighborhood S C base ε) (coefficientFamily D S C i a b p),
      ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
        ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ A * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ A *
          oneHighVariationWeight (E := AnnularState S × ℝ)
            (pairGrading (E := AnnularState S) (F := ℝ) (stateGrading S) realGrading)
            base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v

private theorem n07a_n01_coefficient_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (h01 : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ A : ℝ, 0 < A ∧ n07aCoefficientVariationBound D T S C base loss ε k s A :=
  h01.2.2.2.2.2.2.2.2.2.2.2.1 k s

private def n07aFlowVariationBound (_D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (k s : ℕ) (A : ℝ) : Prop :=
  ∀ (m : ℕ) (a b : ℕ) (p : PolarPoint),
    a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
    ∃ J : SmoothDirections (E := AnnularState S × ℝ) (F := ℝ)
      (stateNeighborhood S C base ε) (ordinaryFlowFamily S C m a b p),
      ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
        ∀ v : Fin k → (AnnularState S × ℝ),
        min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
          A * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ A *
            oneHighVariationWeight (E := AnnularState S × ℝ)
              (pairGrading (E := AnnularState S) (F := ℝ) (stateGrading S) realGrading)
              base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v

private theorem n07a_n01_flow_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (h01 : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ A : ℝ, 0 < A ∧ n07aFlowVariationBound D T S C base loss ε k s A :=
  h01.2.2.2.2.2.2.2.2.2.2.2.2 k s

/-- The actual original-coefficient variations have arbitrarily small
material growth, with their original height decay left intact. -/
theorem n07a_coefficientFamily_subpower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε δ : ℝ}
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (hδ : 0 < δ) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (i : Fin 3) (a b : ℕ) (p : PolarPoint),
      a + b ≤ s → p.1 ∈ D.cells m →
      ∃ J : SmoothDirections (E := AnnularState S × ℝ) (F := ℝ) (stateNeighborhood S C base ε)
          (coefficientFamily D S C i a b p),
        ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
          ∀ v : Fin k → (AnnularState S × ℝ),
          |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            T.M (T.sample m) ^ δ *
            oneHighVariationWeight (E := AnnularState S × ℝ) (pairGrading (E := AnnularState S) (F := ℝ) (stateGrading S) realGrading)
              base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
  have hD := h01.1
  let bound := n07a_n01_coefficient_bound (D := D) (T := T) (S := S)
    (C := C) (base := base) (loss := loss) (ε := ε) h01 k s
  let A : ℝ := bound.choose
  have hA : 0 < A := bound.choose_spec.1
  have hAj : n07aCoefficientVariationBound D T S C base loss ε k s A := bound.choose_spec.2
  let material := materialE0_rpow_le_subpowerM hT A hδ
  let K0 : ℝ := material.choose
  have hK0 : 0 < K0 := material.choose_spec.1
  have hKb : ∀ r ∈ Ioo D.a D.b, T.E0 r ^ A ≤ K0 * T.M r ^ δ :=
    material.choose_spec.2
  refine ⟨A * K0, mul_pos hA hK0, ?_⟩
  intro m i a b p hab hp
  let J := (hAj m i a b p hab hp).choose
  have hJ := (hAj m i a b p hab hp).choose_spec
  refine ⟨J, ?_⟩
  intro z hz v
  have hm := spaces_trace_sample_mem hD.1 hT m
  have hH : 0 ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) :=
    (Real.rpow_pos_of_pos (hT.2.1 _ hm).2.1 _).le
  have hweight := n07a_oneHighVariationWeight_nonneg
    (E := AnnularState S × ℝ)
    (pairGrading (E := AnnularState S) (F := ℝ) (stateGrading S) realGrading)
    base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v
  exact n07a_absorb_material_factor hA.le hH hweight (hKb _ hm) (hJ z hz v)

/-- The actual characteristic-flow variations obey the same material
bound, including the radial endpoint factor already supplied by N01. -/
theorem n07a_ordinaryFlowFamily_subpower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε δ : ℝ}
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (hδ : 0 < δ) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (a b : ℕ) (p : PolarPoint),
      a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      ∃ J : SmoothDirections (E := AnnularState S × ℝ) (F := ℝ) (stateNeighborhood S C base ε)
          (ordinaryFlowFamily S C m a b p),
        ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
          ∀ v : Fin k → (AnnularState S × ℝ),
          min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
            B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              T.M (T.sample (C.cell m)) ^ δ *
              oneHighVariationWeight (E := AnnularState S × ℝ) (pairGrading (E := AnnularState S) (F := ℝ) (stateGrading S) realGrading)
                base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
  have hD := h01.1
  let bound := n07a_n01_flow_bound (D := D) (T := T) (S := S)
    (C := C) (base := base) (loss := loss) (ε := ε) h01 k s
  let A : ℝ := bound.choose
  have hA : 0 < A := bound.choose_spec.1
  have hAj : n07aFlowVariationBound D T S C base loss ε k s A := bound.choose_spec.2
  let material := materialE0_rpow_le_subpowerM hT A hδ
  let K0 : ℝ := material.choose
  have hK0 : 0 < K0 := material.choose_spec.1
  have hKb : ∀ r ∈ Ioo D.a D.b, T.E0 r ^ A ≤ K0 * T.M r ^ δ :=
    material.choose_spec.2
  refine ⟨A * K0, mul_pos hA hK0, ?_⟩
  intro m a b p hab hp
  let J := (hAj m a b p hab hp).choose
  have hJ := (hAj m a b p hab hp).choose_spec
  refine ⟨J, ?_⟩
  intro z hz v
  have hm := spaces_trace_sample_mem hD.1 hT (C.cell m)
  have hH : 0 ≤ T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) :=
    (Real.rpow_pos_of_pos (hT.2.1 _ hm).2.1 _).le
  have hweight := n07a_oneHighVariationWeight_nonneg
    (E := AnnularState S × ℝ)
    (pairGrading (E := AnnularState S) (F := ℝ) (stateGrading S) realGrading)
    base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v
  exact n07a_absorb_material_factor hA.le hH hweight (hKb _ hm) (hJ z hz v)

private def n07aCanonicalJetsBound (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) (s : ℕ) (A : ℝ) : Prop :=
    ∀ z : AnnularState S × ℝ,
      z ∈ stateNeighborhood S C base ε → ∀ (m : ℕ) (p : PolarPoint),
      p ∈ canonicalOpen S K m → ∀ a b : ℕ, a + b ≤ s →
      |mixedDerivative a b (K.potential z m) p| +
        |mixedDerivative a b (K.dividedDifference z m).a p| +
        |mixedDerivative a b (K.dividedDifference z m).b p| +
        |mixedDerivative a b (K.dividedDifference z m).c p| ≤
        A * T.E0 (T.sample (K.cell m)) ^ A *
          (1 + stateGrading S (s + loss) (z.1 - C.referenceState : AnnularState S) + |z.2|)

private theorem n07a_canonicalCoefficientJets_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε) (s : ℕ) :
    ∃ A : ℝ, 0 < A ∧ n07aCanonicalJetsBound T S C K base loss ε s A :=
  h04.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s

/-- The actual canonical potential and divided-difference jets cost one
arbitrarily prescribed positive material power after collecting the full
coefficient expression. -/
theorem n07a_canonicalCoefficientJets_subpower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε δ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hδ : 0 < δ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : AnnularState S × ℝ,
      z ∈ stateNeighborhood S C base ε → ∀ (m : ℕ) (p : PolarPoint),
      p ∈ canonicalOpen S K m → ∀ a b : ℕ, a + b ≤ s →
      |mixedDerivative a b (K.potential z m) p| +
        |mixedDerivative a b (K.dividedDifference z m).a p| +
        |mixedDerivative a b (K.dividedDifference z m).b p| +
        |mixedDerivative a b (K.dividedDifference z m).c p| ≤
        B * T.M (T.sample (K.cell m)) ^ δ *
          (1 + stateGrading S (s + loss) (z.1 - C.referenceState : AnnularState S) + |z.2|) := by
  let bound := n07a_canonicalCoefficientJets_bound (D := D) (T := T) (S := S)
    (C := C) (L := L) (K := K) (base := base) (loss := loss) (ε := ε) h04 s
  let A : ℝ := bound.choose
  have hA : 0 < A := bound.choose_spec.1
  have hAb : n07aCanonicalJetsBound T S C K base loss ε s A := bound.choose_spec.2
  let material := materialE0_rpow_le_subpowerM hT A hδ
  let K0 : ℝ := material.choose
  have hK0 : 0 < K0 := material.choose_spec.1
  have hKb : ∀ r ∈ Ioo D.a D.b, T.E0 r ^ A ≤ K0 * T.M r ^ δ :=
    material.choose_spec.2
  refine ⟨A * K0, mul_pos hA hK0, ?_⟩
  intro z hz m p hp a b hab
  have hm := spaces_trace_sample_mem hD hT (K.cell m)
  have hfactor : 0 ≤ 1 + stateGrading S (s + loss) (z.1 - C.referenceState : AnnularState S) + |z.2| :=
    add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _)
  have hactual := hAb z hz m p hp a b hab
  have hbound :
      |mixedDerivative a b (K.potential z m) p| +
        |mixedDerivative a b (K.dividedDifference z m).a p| +
        |mixedDerivative a b (K.dividedDifference z m).b p| +
        |mixedDerivative a b (K.dividedDifference z m).c p| ≤
      A * (1 : ℝ) * T.E0 (T.sample (K.cell m)) ^ A *
      (1 + stateGrading S (s + loss) (z.1 - C.referenceState : AnnularState S) + |z.2|) := by
    simpa only [mul_one] using hactual
  simpa only [mul_one] using
    n07a_absorb_material_factor hA.le zero_le_one hfactor (hKb _ hm) hbound

end ContinuousFlexibility.Analysis
