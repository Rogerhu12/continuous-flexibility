module

public import ContinuousFlexibility.Analysis.SpacesTraceCircleBounds
public import ContinuousFlexibility.Analysis.MaterialSampleBounds
public import ContinuousFlexibility.Analysis.StateNeighborhood

/-!
# Actual angular jets of the left return coordinate

The existing weighted circle evaluation estimate applies to every exact
circle model through its prescribed norm identity. The actual left
coordinate is the angle plus the decoded last state component, which is
zero at the reference state. Thus its displacement has the fixed loss one,
with a constant chosen before the state, angle, order, and component.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The existing weighted row evaluation and the actual Hilbert norm
give a pointwise estimate for any member of the circle class. -/
theorem circleMember_iteratedDeriv_abs_le
    {T : MaterialData} {γ : ℝ} {f : ℕ → ℝ → ℝ}
    (hf : CircleMember T γ f) (m : ℕ)
    (hH : 0 < T.H (T.sample m)) (n : ℕ) (θ : ℝ) :
    |iteratedDeriv n (f m) θ| ≤
      T.H (T.sample m) ^ γ * anglePairEvaluationConstant * circleNorm T γ (n + 1) f := by
  have hb := spaces_circle_weighted_pointwise hf (n + 1) m n 0 (by omega) θ
  have hrow := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (circleJetEncodeHilbert hf (n + 1)) m
  have hw : T.H (T.sample m) ^ (-γ) * |iteratedDeriv n (f m) θ| ≤
      anglePairEvaluationConstant * circleNorm T γ (n + 1) f := by
    calc
      _ ≤ anglePairEvaluationConstant * ‖circleJetEncodeHilbert hf (n + 1) m‖ := by
        simpa only [pow_zero, one_mul, abs_mul,
          abs_of_pos (Real.rpow_pos_of_pos hH (-γ))] using hb
      _ ≤ anglePairEvaluationConstant * ‖circleJetEncodeHilbert hf (n + 1)‖ :=
        mul_le_mul_of_nonneg_left hrow anglePairEvaluationConstant_nonneg
      _ = _ := congrArg (anglePairEvaluationConstant * ·)
        (circleJetEncodeHilbert_norm hf (n + 1))
  have hcancel : T.H (T.sample m) ^ γ * T.H (T.sample m) ^ (-γ) = 1 := by
    rw [← Real.rpow_add hH, add_neg_cancel, Real.rpow_zero]
  calc
    |iteratedDeriv n (f m) θ| =
        T.H (T.sample m) ^ γ *
          (T.H (T.sample m) ^ (-γ) * |iteratedDeriv n (f m) θ|) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ T.H (T.sample m) ^ γ *
        (anglePairEvaluationConstant * circleNorm T γ (n + 1) f) :=
      mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg hH.le γ)
    _ = _ := (mul_assoc _ _ _).symm

/-- The estimate uses the specified decoder and grading of an arbitrary
actual circle model, rather than replacing it by the canonical model. -/
theorem circleModel_iteratedDeriv_abs_le
    {T : MaterialData} {γ : ℝ} {Q : CircleModelData}
    (hQ : IsCircleModel T γ Q) (u : Q.Space) (m : ℕ)
    (hH : 0 < T.H (T.sample m)) (n : ℕ) (θ : ℝ) :
    |iteratedDeriv n (Q.decode u m) θ| ≤
      T.H (T.sample m) ^ γ * anglePairEvaluationConstant * Q.grading (n + 1) u := by
  have hn : circleNorm T γ (n + 1) (Q.decode u) ≤ Q.grading (n + 1) u := by
    rw [← hQ.2.2.2.2.2.2.2 u (n + 1)]
    exact norm_coordinate_le_graded (fun k => Q.level k) Q.bond le_rfl u
  exact (circleMember_iteratedDeriv_abs_le (hQ.2.2.2.1 u) m hH n θ).trans
    (mul_le_mul_of_nonneg_left hn
      (mul_nonneg (Real.rpow_nonneg hH.le γ) anglePairEvaluationConstant_nonneg))

private theorem snd_le_pairGrading_for_leftChart
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (n : ℕ) (x : E × F) :
    q n x.2 ≤ pairGrading p q n x := by
  simp only [pairGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]
  exact le_add_of_nonneg_left (apply_nonneg _ _)

private theorem leftCircleGrading_le_stateGrading
    (S : PhysicalSpacesData) (n : ℕ) (x : AnnularState S) :
    (S.circle (3 / 4 : ℝ)).grading n x.2.2.2 ≤ stateGrading S n x := by
  exact (snd_le_pairGrading_for_leftChart
    (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading n x.2.2).trans
    ((snd_le_pairGrading_for_leftChart realGrading
      (pairGrading (S.circle (3 / 4 : ℝ)).grading
        (S.circle (3 / 4 : ℝ)).grading) n x.2).trans
      (snd_le_pairGrading_for_leftChart (heightPairGrading S)
        (pairGrading realGrading (pairGrading (S.circle (3 / 4 : ℝ)).grading
          (S.circle (3 / 4 : ℝ)).grading)) n x))

theorem contDiff_stateLeftChart
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (x : AnnularState S) (m : ℕ) :
    ContDiff ℝ ∞ (stateLeftChart S x m) := by
  change ContDiff ℝ ∞ (fun θ : ℝ => θ + (S.circle (3 / 4 : ℝ)).decode x.2.2.2 m θ)
  exact contDiff_id.add (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 x.2.2.2).1 m).1

theorem stateLeftChart_period_add
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (x : AnnularState S) (m : ℕ) (θ : ℝ) :
    stateLeftChart S x m (θ + Real.pi) = stateLeftChart S x m θ + Real.pi := by
  have hp := (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 x.2.2.2).1 m).2 θ
  change θ + Real.pi + (S.circle (3 / 4 : ℝ)).decode x.2.2.2 m (θ + Real.pi) =
    (θ + (S.circle (3 / 4 : ℝ)).decode x.2.2.2 m θ) + Real.pi
  rw [hp]
  ring

private theorem lastCoordinate_sub_reference
    {E₁ E₂ E₃ E₄ : Type*}
    [AddCommGroup E₁] [AddCommGroup E₂] [AddCommGroup E₃] [AddCommGroup E₄]
    (x x₀ : E₁ × E₂ × E₃ × E₄) (hzero : x₀.2.2.2 = 0) :
    (x - x₀).2.2.2 = x.2.2.2 := by
  simp only [Prod.snd_sub, hzero, sub_zero]

private theorem decodedLift_jet_bound_of_coordinate_eq
    {E : Type*} (decode : E → ℕ → ℝ → ℝ) {u v : E}
    (huv : v = u) {m n : ℕ} {θ A q r : ℝ}
    (hb : |iteratedDeriv n (decode v m) θ| ≤ A * q)
    (hqr : q ≤ r) (hA : 0 ≤ A) :
    |iteratedDeriv n (fun η => η + decode u m η - η) θ| ≤ A * r := by
  have he : (fun η => η + decode u m η - η) = decode v m := by
    rw [huv]
    funext η
    ring
  rw [he]
  exact hb.trans (mul_le_mul_of_nonneg_left hqr hA)

/-- The actual displacement retains the sampled material height factor.
The derivative loss is exactly one at every angular order. -/
theorem stateLeftChart_displacement_iteratedDeriv_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hC : referenceStateConditions D S C)
    (x : AnnularState S) (m n : ℕ) (θ : ℝ) :
    |iteratedDeriv n (fun η => stateLeftChart S x m η - η) θ| ≤
      T.H (T.sample m) ^ (3 / 4 : ℝ) * anglePairEvaluationConstant *
        stateGrading S (n + 1) (x - C.referenceState) := by
  have hH : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT m)).2.1
  have hzero : C.referenceState.2.2.2 = 0 := hC.2.2.2.2.1
  have hc : (x - C.referenceState).2.2.2 = x.2.2.2 :=
    lastCoordinate_sub_reference x C.referenceState hzero
  change |iteratedDeriv n
      (fun η => η + (S.circle (3 / 4 : ℝ)).decode x.2.2.2 m η - η) θ| ≤ _
  exact decodedLift_jet_bound_of_coordinate_eq
    (S.circle (3 / 4 : ℝ)).decode hc
    (circleModel_iteratedDeriv_abs_le (hS.2.1 (3 / 4 : ℝ))
      (x - C.referenceState).2.2.2 m hH n θ)
    (leftCircleGrading_le_stateGrading S (n + 1) (x - C.referenceState))
    (mul_nonneg (Real.rpow_nonneg hH.le _) anglePairEvaluationConstant_nonneg)

private def ScalarFamilyDisplacementJetBound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (x₀ : E) (f : E → ℕ → ℝ → ℝ) (B : ℝ) : Prop :=
  ∀ (n m : ℕ) (x : E) (θ : ℝ),
    |iteratedDeriv n (f x m) θ| ≤ B * p (n + 1) (x - x₀)

private theorem scalarFamily_bound_of_sample_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (x₀ : E) (f : E → ℕ → ℝ → ℝ)
    (H : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hH : ∃ M : ℝ, 0 < M ∧ ∀ m, H m ≤ M)
    (hf : ∀ (n m : ℕ) (x : E) (θ : ℝ),
      |iteratedDeriv n (f x m) θ| ≤ H m * c * p (n + 1) (x - x₀)) :
    ∃ B : ℝ, 0 < B ∧ ScalarFamilyDisplacementJetBound p x₀ f B := by
  obtain ⟨M, hM, hbound⟩ := hH
  refine ⟨1 + M * c, add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hM.le hc), ?_⟩
  intro n m x θ
  exact (hf n m x θ).trans (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (hbound m) hc).trans
      (le_add_of_nonneg_left zero_le_one)) (apply_nonneg _ _))

private theorem exists_circleSampleHeight_bound
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ M : ℝ, 0 < M ∧ ∀ m, T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ M := by
  obtain ⟨M, hM, hbound⟩ := material_sample_height_coefficient_power_bounded
    hD hT id 0 (by norm_num : (0 : ℝ) < 3 / 4)
  refine ⟨M, hM, ?_⟩
  intro m
  simpa only [id_eq, Real.rpow_zero, mul_one] using hbound m

/-- The full uniform displacement conclusion, with the loss-one order
unchanged, is named to keep the physical state adapter small. -/
def N01LeftChartDisplacementJetBound (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (B : ℝ) : Prop :=
  ∀ (n m : ℕ) (x : AnnularState S) (θ : ℝ),
    |iteratedDeriv n (fun η => stateLeftChart S x m η - η) θ| ≤
      B * stateGrading S (n + 1) (x - C.referenceState)

/-- Material absorption supplies one constant before every state,
component, and order. No neighborhood shrink or additional high-jet
hypothesis is needed for this linear left-coordinate displacement. -/
theorem n01_stateLeftChart_displacement_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ B : ℝ, 0 < B ∧ N01LeftChartDisplacementJetBound S C B := by
  exact scalarFamily_bound_of_sample_bound
    (stateGrading S) C.referenceState
    (fun x m η => stateLeftChart S x m η - η)
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    anglePairEvaluationConstant_nonneg
    (exists_circleSampleHeight_bound hN.1.1 hT)
    (fun n m x θ => stateLeftChart_displacement_iteratedDeriv_le
      hN.1.1 hT hS hN.2.2.1 x m n θ)

/-- The actual left lift in the paired state grading used by the flow
calculus. This named conclusion keeps the concrete state-space adapter
separate from the finite-dimensional normalization proofs. -/
def N01LeftChartPairJetBound (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (B : ℝ) : Prop :=
  ∀ (n m : ℕ) (z : AnnularState S × ℝ) (θ : ℝ),
    ‖iteratedFDeriv ℝ n (fun η => stateLeftChart S z.1 m η - η) θ‖ ≤
      B * (1 + pairGrading (stateGrading S) realGrading (n + 1)
        (z - (C.referenceState, 0)))

private theorem scalarJet_le_pairGrading
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    {B : ℝ} (hB : 0 ≤ B) {f : ℝ → ℝ} {n k : ℕ} {θ : ℝ} (x : E × F)
    (hb : |iteratedDeriv n f θ| ≤ B * p k x.1) :
    ‖iteratedFDeriv ℝ n f θ‖ ≤ B * (1 + pairGrading p q k x) := by
  have hf : p k x.1 ≤ pairGrading p q k x := by
    simp only [pairGrading, add_apply, Seminorm.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply]
    exact le_add_of_nonneg_right (apply_nonneg _ _)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact hb.trans (mul_le_mul_of_nonneg_left
    (hf.trans (le_add_of_nonneg_left zero_le_one)) hB)

theorem n01_stateLeftChart_pairJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ B : ℝ, 0 < B ∧ N01LeftChartPairJetBound S C B := by
  obtain ⟨B, hB, hbound⟩ := n01_stateLeftChart_displacement_fixed_loss hS hT hN
  refine ⟨B, hB, ?_⟩
  intro n m z θ
  exact scalarJet_le_pairGrading (stateGrading S) realGrading hB.le
    (z - (C.referenceState, 0)) (hbound n m z.1 θ)

end ContinuousFlexibility.Analysis
