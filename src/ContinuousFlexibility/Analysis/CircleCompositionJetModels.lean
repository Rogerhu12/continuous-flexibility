module

public import ContinuousFlexibility.Analysis.CircleCompositionMixedJets
public import ContinuousFlexibility.Analysis.CircleDifferentialOperators
public import ContinuousFlexibility.Analysis.CircleProductSmoothTame

/-!
# Actual model values of all chart-composition parameter jets

Every displayed scalar jet is the decoder of a vector in the supplied
circle space. Finite products start with an actual circle vector, so
the construction never requires the constant sequence of circle fields
to have finite weighted energy.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

private theorem grading_map_shift_le
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (N : ℕ → F → ℝ) (decode : E → F) (A : E → E)
    (hgrade : ∀ s u C, 0 ≤ C → (p s u ≤ C ↔ ∀ i ≤ s, N i (decode u) ≤ C))
    (hbound : ∀ i u, N i (decode (A u)) ≤ N (i + 1) (decode u))
    (s : ℕ) (u : E) : p s (A u) ≤ p (s + 1) u := by
  apply (hgrade s (A u) (p (s + 1) u) (apply_nonneg _ _)).mpr
  intro i hi
  exact (hbound i u).trans
    (((hgrade (s + 1) u (p (s + 1) u) (apply_nonneg _ _)).mp le_rfl)
      (i + 1) (Nat.add_le_add_right hi 1))

private theorem circleAngularDerivative_grading_le (hS : IsCircleModel T γ S)
    (s : ℕ) (u : S.Space) :
    S.grading s (circleDerivativeContinuousLinear hS u) ≤ S.grading (s + 1) u := by
  have hb (i : ℕ) (v : S.Space) :
      circleNorm T γ i (S.decode (circleDerivativeContinuousLinear hS v)) ≤
        circleNorm T γ (i + 1) (S.decode v) :=
    (congrArg (circleNorm T γ i) (circleDerivativeContinuousLinear_decode hS v)).trans_le
      (circleNorm_angularDerivative_le (hS.2.2.2.1 v) i)
  exact grading_map_shift_le S.grading (circleNorm T γ) (fun v => S.decode v)
    (fun v => circleDerivativeContinuousLinear hS v)
    (fun k v C hC => circleGrading_le_iff_circleNorm hS k v hC) hb s u

private theorem circleField_finiteProduct_insert
    {ι : Type*} [DecidableEq ι] (u : ℕ → ℝ → ℝ) (v : ι → ℕ → ℝ → ℝ)
    (I : Finset ι) (i : ι) (hi : i ∉ I) :
    (fun m θ => u m θ * ∏ j ∈ insert i I, v j m θ) =
      (fun m θ => v i m θ * (u m θ * ∏ j ∈ I, v j m θ)) := by
  funext m θ
  rw [Finset.prod_insert hi]
  ring

private theorem circleMember_field_finiteProductWith
    {ι : Type*} [DecidableEq ι] {u : ℕ → ℝ → ℝ} {v : ι → ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u)
    (hv : ∀ i m, ContDiff ℝ ∞ (v i m) ∧ Function.Periodic (v i m) Real.pi)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hjets : ∀ i s, ∃ B : ℝ, 0 ≤ B ∧
      ∀ m k θ, k ≤ s → |iteratedDeriv k (v i m) θ| ≤ B)
    (I : Finset ι) : CircleMember T γ (fun m θ => u m θ * ∏ i ∈ I, v i m θ) := by
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, mul_one] using hu
  | @insert i I hi ih =>
      exact (circleField_finiteProduct_insert u v I i hi).symm ▸
        circleMember_mul_of_uniform_jets ih (hv i) hM hH (hjets i)

def circleAngularDerivativeIterate (hS : IsCircleModel T γ S) :
    ℕ → S.Space →L[ℝ] S.Space
  | 0 => ContinuousLinearMap.id ℝ S.Space
  | n + 1 => (circleDerivativeContinuousLinear hS).comp (circleAngularDerivativeIterate hS n)

theorem circleAngularDerivativeIterate_decode (hS : IsCircleModel T γ S)
    (n : ℕ) (u : S.Space) :
    S.decode (circleAngularDerivativeIterate hS n u) =
      fun m => iteratedDeriv n (S.decode u m) := by
  induction n with
  | zero => simp only [circleAngularDerivativeIterate, ContinuousLinearMap.id_apply,
      iteratedDeriv_zero]
  | succ n ih =>
      simp only [circleAngularDerivativeIterate, ContinuousLinearMap.comp_apply,
        circleDerivativeContinuousLinear_decode, ih, iteratedDeriv_succ]

theorem circleAngularDerivativeIterate_grading (hS : IsCircleModel T γ S)
    (n s : ℕ) (u : S.Space) :
    S.grading s (circleAngularDerivativeIterate hS n u) ≤ S.grading (s + n) u := by
  induction n generalizing s with
  | zero => simp only [circleAngularDerivativeIterate, ContinuousLinearMap.id_apply,
      Nat.add_zero, le_refl]
  | succ n ih =>
      have hd := circleAngularDerivative_grading_le hS s (circleAngularDerivativeIterate hS n u)
      simpa only [circleAngularDerivativeIterate, ContinuousLinearMap.comp_apply,
        Nat.add_assoc, Nat.add_comm 1 n] using hd.trans (ih (s + 1))

theorem circleShiftedChartComposeLinear_isTame
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) :
    IsTameLinear S.grading S.grading
      (circleShiftedChartComposeLinear hS hT hD hγ travel e) 1 0 :=
  circleComposeModelLinear_isTame hS (material_circle_sample_weights_pos hT hD).1
    (material_circle_sample_weights_pos hT hD).2
    (circleAffineLift travel (S.decode e) 1)
    (circleAffineLift_contDiff (fun m => ((hS.2.2.2.1 e).1 m).1) travel 1)
    (circleAffineLift_periodic (fun m => ((hS.2.2.2.1 e).1 m).2) travel 1)
    (circleShiftedChart_uniform_jets hS hT hD hγ travel e)

def circleShiftedChartComposeContinuousLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) : S.Space →L[ℝ] S.Space :=
  (circleShiftedChartComposeLinear_isTame hS hT hD hγ travel e).toContinuousLinearMap
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)

theorem circleShiftedChartComposeContinuousLinear_apply
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e u : S.Space) :
    circleShiftedChartComposeContinuousLinear hS hT hD hγ travel e u =
      circleShiftedChartComposeLinear hS hT hD hγ travel e u :=
  IsTameLinear.toContinuousLinearMap_apply
    (circleShiftedChartComposeLinear_isTame hS hT hD hγ travel e)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond) u

def circleOuterJetComposeContinuousLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (n : ℕ) (e : S.Space) : S.Space →L[ℝ] S.Space :=
  (circleShiftedChartComposeContinuousLinear hS hT hD hγ travel e).comp
    (circleAngularDerivativeIterate hS n)

theorem circleOuterJetComposeContinuousLinear_decode
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (n : ℕ) (e u : S.Space) :
    S.decode (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e u) =
      fun m θ => iteratedDeriv n (S.decode u m)
        (circleCompositionPhase travel (e, u) m θ) := by
  funext m θ
  simp only [circleOuterJetComposeContinuousLinear, ContinuousLinearMap.comp_apply,
    circleShiftedChartComposeContinuousLinear_apply, circleShiftedChartComposeLinear_decode,
    circleAngularDerivativeIterate_decode, circleCompositionPhase]

theorem circleMember_finiteProductWith
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (u : S.Space) (v : ι → S.Space) (I : Finset ι) :
    CircleMember T γ (fun m θ => S.decode u m θ * ∏ i ∈ I, S.decode (v i) m θ) :=
  circleMember_field_finiteProductWith (hS.2.2.2.1 u)
    (fun i => (hS.2.2.2.1 (v i)).1)
    (fun m => ((material_circle_sample_weights_pos hT hD).1 m).le)
    (fun m => ((material_circle_sample_weights_pos hT hD).2 m).le)
    (fun i => circleModel_uniform_jets_of_material hS hT hD hγ (v i)) I

def circleFiniteProductWith
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (u : S.Space) (v : ι → S.Space) (I : Finset ι) : S.Space :=
  circleRealize hS (fun m θ => S.decode u m θ * ∏ i ∈ I, S.decode (v i) m θ)
    (circleMember_finiteProductWith hS hT hD hγ u v I)

theorem circleFiniteProductWith_decode
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (u : S.Space) (v : ι → S.Space) (I : Finset ι) :
    S.decode (circleFiniteProductWith hS hT hD hγ u v I) =
      fun m θ => S.decode u m θ * ∏ i ∈ I, S.decode (v i) m θ :=
  circleRealize_decode hS _ (circleMember_finiteProductWith hS hT hD hγ u v I)

theorem circleFiniteProductWith_empty
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (u : S.Space) (v : ι → S.Space) :
    circleFiniteProductWith hS hT hD hγ u v ∅ = u := by
  apply hS.2.2.2.2.2.1
  simp only [circleFiniteProductWith_decode, Finset.prod_empty, mul_one]

theorem circleFiniteProductWith_insert
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (u : S.Space) (v : ι → S.Space) (I : Finset ι) (i : ι) (hi : i ∉ I) :
    circleFiniteProductWith hS hT hD hγ u v (insert i I) =
      circleProductBilinear hS hT hD hγ (v i) (circleFiniteProductWith hS hT hD hγ u v I) := by
  have hleft := circleFiniteProductWith_decode hS hT hD hγ u v (insert i I)
  have hright := circleProductBilinear_decode hS hT hD hγ (v i)
    (circleFiniteProductWith hS hT hD hγ u v I)
  have hinner := congrArg (fun f : ℕ → ℝ → ℝ =>
    fun m θ => S.decode (v i) m θ * f m θ) (circleFiniteProductWith_decode hS hT hD hγ u v I)
  exact hS.2.2.2.2.2.1 (hleft.trans
    ((circleField_finiteProduct_insert (S.decode u) (fun j => S.decode (v j)) I i hi).trans
      (hinner.symm.trans hright.symm)))

def circleChartCompositionJetValue
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (n : ℕ) (x : S.Space × S.Space)
    (v : Fin n → S.Space × S.Space) : S.Space :=
  circleFiniteProductWith hS hT hD hγ
    (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n x.1 x.2)
      (fun i => (v i).1) Finset.univ +
    ∑ i : Fin n, circleFiniteProductWith hS hT hD hγ
      (circleOuterJetComposeContinuousLinear hS hT hD hγ travel (n - 1) x.1 (v i).2)
        (fun j => (v j).1) (Finset.univ.erase i)

theorem circleChartCompositionJetValue_decode
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (n : ℕ) (x : S.Space × S.Space)
    (v : Fin n → S.Space × S.Space) :
    S.decode (circleChartCompositionJetValue hS hT hD hγ travel n x v) =
      circleChartCompositionJets hS travel n x v := by
  classical
  simp only [circleChartCompositionJetValue, map_add, map_sum,
    circleFiniteProductWith_decode, circleOuterJetComposeContinuousLinear_decode]
  funext m θ
  simp only [Pi.add_apply, Finset.sum_apply, circleChartCompositionJets_apply,
    circleCompositionPhase]

theorem circleChartCompositionJets_member
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (n : ℕ) (x : S.Space × S.Space)
    (v : Fin n → S.Space × S.Space) :
    CircleMember T γ (circleChartCompositionJets hS travel n x v) := by
  rw [← circleChartCompositionJetValue_decode hS hT hD hγ travel n x v]
  exact hS.2.2.2.1 _

end ContinuousFlexibility.Statements
