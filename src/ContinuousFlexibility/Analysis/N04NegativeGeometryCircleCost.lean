module

public import ContinuousFlexibility.Analysis.N01LeftChartJets
public import ContinuousFlexibility.Analysis.N01cStateSeminorms
public import ContinuousFlexibility.Analysis.MaterialSampleShift
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Circle bounds at the actual negative-component sample

Circle models use the control label as their sample index. The current
geometry cost uses the cell containing the negative component. The actual
N01 index comparison transfers the positive height weight between these
samples at a coefficient-envelope cost. Angular evaluation then costs one
grading order, uniformly in the component and evaluation angle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- A circle grading estimate gives the current pointwise cost at the
containing-cell sample, retaining the exact positive height power. -/
theorem n04NegativeGeometry_circleJet_component_cost
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {Q : CircleModelData} (hQ : IsCircleModel T (3 / 4 : ℝ) Q)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (C.cell m)))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ (u : Q.Space) (m j : ℕ) (θ w : ℝ), 0 ≤ w →
      Q.grading (j + 1) u ≤ K * w →
      |iteratedDeriv j (Q.decode u m) θ| ≤
        B * T.E0 (T.sample (C.cell m)) ^ B *
          T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * w := by
  let indexData := hN.2.2.2.2.1
  let heightData := materialSample_H_E0_rpow_of_index_sub_bound hT hN.1.1
    (3 / 4 : ℝ) (R := 0) le_rfl indexData.choose_spec.1.le
  let KH : ℝ := heightData.choose
  let A : ℝ := heightData.choose_spec.choose
  have hKH : 0 < KH := heightData.choose_spec.choose_spec.1
  let packed := coefficientEnvelope_pack (KH * anglePairEvaluationConstant * K) A
  let B : ℝ := packed.choose
  refine ⟨B, packed.choose_spec.1, ?_⟩
  intro u m j θ w hw hbound
  have hs : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT m)).2.1
  have ht : 0 < T.H (T.sample (C.cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT (C.cell m))).2.1
  have hshift : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤
      KH * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ A := by
    have hindex : |(D.cellIndex m : ℝ) - D.cellIndex (C.cell m)| ≤ indexData.choose := by
      simpa only [abs_sub_comm] using indexData.choose_spec.2 m
    have hraw : T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ (0 : ℝ) ≤
        KH * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ A :=
      heightData.choose_spec.choose_spec.2.2 m (C.cell m) hindex
    calc
      _ = T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ (0 : ℝ) := by
        rw [Real.rpow_zero, mul_one]
      _ ≤ _ := hraw
  have hpack : (KH * anglePairEvaluationConstant * K) *
      T.E0 (T.sample (C.cell m)) ^ A ≤ B * T.E0 (T.sample (C.cell m)) ^ B :=
    packed.choose_spec.2 _ (hfloor m)
  calc
    _ ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) * anglePairEvaluationConstant *
        Q.grading (j + 1) u := circleModel_iteratedDeriv_abs_le hQ u m hs j θ
    _ ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) * anglePairEvaluationConstant * (K * w) :=
      mul_le_mul_of_nonneg_left hbound
        (mul_nonneg (Real.rpow_nonneg hs.le _) anglePairEvaluationConstant_nonneg)
    _ = T.H (T.sample m) ^ (3 / 4 : ℝ) * (anglePairEvaluationConstant * K * w) := by ring
    _ ≤ (KH * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ A) * (anglePairEvaluationConstant * K * w) :=
      mul_le_mul_of_nonneg_right hshift
        (mul_nonneg (mul_nonneg anglePairEvaluationConstant_nonneg hK) hw)
    _ = ((KH * anglePairEvaluationConstant * K) * T.E0 (T.sample (C.cell m)) ^ A) *
        T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * w := by ring
    _ ≤ (B * T.E0 (T.sample (C.cell m)) ^ B) *
        T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * w :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpack (Real.rpow_nonneg ht.le _)) hw

/-- Apply angular evaluation to the supplied family of genuine circle
towers. The family and low base are unchanged; the loss increases by one. -/
theorem n04NegativeGeometry_circleTower_pointwise_bound
    {I X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    {Q : CircleModelData} (hQ : IsCircleModel T (3 / 4 : ℝ) Q)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (C.cell m)))
    {U : Set X} {f : I → X → Q.Space} (J : ∀ i, SmoothDirections U (f i))
    (p : ℕ → Seminorm ℝ X) (b L k : ℕ)
    (hbound : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ i z, z ∈ U → ∀ v : Fin k → X,
      Q.grading s ((J i).D k z v) ≤
        K * oneHighVariationWeight p b (s + L) z v) :
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i z, z ∈ U → ∀ v : Fin k → X,
      ∀ (m j : ℕ) (θ : ℝ), j ≤ s →
        |iteratedDeriv j (Q.decode ((J i).D k z v) m) θ| ≤
          B * T.E0 (T.sample (C.cell m)) ^ B *
            T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight p b (s + (L + 1)) z v := by
  intro s
  let orderData := hbound (s + 1)
  let costData := n04NegativeGeometry_circleJet_component_cost hN hT hQ hfloor
    orderData.choose_spec.1
  refine ⟨costData.choose, costData.choose_spec.1, ?_⟩
  intro i z hz v m j θ hjs
  have horder : (s + 1) + L = s + (L + 1) := by omega
  have hgrade : Q.grading (j + 1) ((J i).D k z v) ≤
      orderData.choose * oneHighVariationWeight p b (s + (L + 1)) z v := by
    have hm := gradedSeminorm_monotone (fun s => ↥(Q.level s)) Q.bond
      (Nat.add_le_add_right hjs 1) ((J i).D k z v)
    exact (hm.trans (orderData.choose_spec.2 i z hz v)).trans_eq
      (congrArg (fun n : ℕ => orderData.choose * oneHighVariationWeight p b n z v) horder)
  exact costData.choose_spec.2 ((J i).D k z v) m j θ _
    (oneHighVariationWeight_nonneg p b _ z v) hgrade

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_circleTower_pointwise_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_circleTower_pointwise_bound
