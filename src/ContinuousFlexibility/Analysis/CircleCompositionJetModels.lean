import ContinuousFlexibility.Analysis.CircleCompositionMixedJets
import ContinuousFlexibility.Analysis.CircleDifferentialOperators
import ContinuousFlexibility.Analysis.CircleProductSmoothTame

/-!
# Actual model values of all chart-composition parameter jets

Every displayed scalar jet is the decoder of a vector in the supplied
circle space. Finite products start with an actual circle vector, so
the construction never requires the constant sequence of circle fields
to have finite weighted energy.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

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
      have hd : S.grading s (circleDerivativeContinuousLinear hS
          (circleAngularDerivativeIterate hS n u)) ≤
          S.grading (s + 1) (circleAngularDerivativeIterate hS n u) := by
        apply (circleGrading_le_iff_circleNorm hS s _ (apply_nonneg _ _)).mpr
        intro i hi
        rw [circleDerivativeContinuousLinear_decode]
        exact (circleNorm_angularDerivative_le
          (hS.2.2.2.1 (circleAngularDerivativeIterate hS n u)) i).trans
          (((circleGrading_le_iff_circleNorm hS (s + 1)
            (circleAngularDerivativeIterate hS n u) (apply_nonneg _ _)).mp
              (le_refl _)) (i + 1) (by omega))
      exact hd.trans ((ih (s + 1)).trans_eq (by congr 1; omega))

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
    CircleMember T γ (fun m θ => S.decode u m θ * ∏ i ∈ I, S.decode (v i) m θ) := by
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, mul_one] using hS.2.2.2.1 u
  | @insert i I hi ih =>
      have hm := circleMember_mul_of_uniform_jets ih (hS.2.2.2.1 (v i)).1
        (fun m => ((material_circle_sample_weights_pos hT hD).1 m).le)
        (fun m => ((material_circle_sample_weights_pos hT hD).2 m).le)
        (circleModel_uniform_jets_of_material hS hT hD hγ (v i))
      have heq :
          (fun m θ => S.decode u m θ * ∏ j ∈ insert i I, S.decode (v j) m θ) =
          (fun m θ => S.decode (v i) m θ *
            (S.decode u m θ * ∏ j ∈ I, S.decode (v j) m θ)) := by
        funext m θ
        rw [Finset.prod_insert hi]
        ring
      rw [heq]
      exact hm

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
  apply hS.2.2.2.2.2.1
  rw [circleFiniteProductWith_decode, circleProductBilinear_decode,
    circleFiniteProductWith_decode]
  funext m θ
  rw [Finset.prod_insert hi]
  ring

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
