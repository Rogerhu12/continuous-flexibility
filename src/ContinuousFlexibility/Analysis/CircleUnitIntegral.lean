import ContinuousFlexibility.Analysis.ProjectiveUnitIntegral
import ContinuousFlexibility.Analysis.CircleAngleEvaluation
import ContinuousFlexibility.Analysis.CircleModelRealization

/-!
# Parameter integration and the actual circle decoder

The supplied model's weak derivative graph represents point evaluation
by the value and first angular derivative in level one. This finite-level
formula proves that the existing decoder commutes with projective
parameter integration, without replacing the circle model.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleModelValueLevel (T : MaterialData) (γ : ℝ) (S : CircleModelData)
    (m : ℕ) (θ : ℝ) : S.level 1 →L[ℝ] ℝ :=
  T.H (T.sample m) ^ γ • (anglePairEvaluation (toIocMod Real.pi_pos 0 θ)).comp
    (((circleJetCoordinate 1 m (zeroCircleJetIndex 1)).comp (S.level 1).subtypeL).prod
      ((circleJetCoordinate 1 m (circleJetPureAngularIndex 1)).comp (S.level 1).subtypeL))

theorem circleModelValueLevel_apply
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 < T.M (T.sample m)) (hH : ∀ m, 0 < T.H (T.sample m))
    (m : ℕ) (θ : ℝ) (u : S.Space) :
    circleModelValueLevel T γ S m θ (u.val 1) = S.decode u m θ := by
  have hg : (u.val 1).val ∈ circleJetGraph T 1 := by
    rw [← hS.1 1]
    exact (u.val 1).property
  have hw := (mem_circleJetGraph_iff_normalized hM (u.val 1).val).mp hg
    m (circleJetPureAngularIndex 1)
  have hw' : HasWeakAngularDerivative
      ((u.val 1).val m (zeroCircleJetIndex 1))
      ((u.val 1).val m (circleJetPureAngularIndex 1)) 1 := by
    simpa only [circleJetNormalizedDerivative_apply, circleJetWeight,
      circleJetPureAngularIndex_order, circleJetPureAngularIndex_weight,
      pow_zero, inv_one, one_smul] using hw
  have hc : Continuous (fun x => T.H (T.sample m) ^ (-γ) * S.decode u m x) :=
    continuous_const.mul (((hS.2.2.2.1 u).1 m).1.continuous)
  have hp : Function.Periodic
      (fun x => T.H (T.sample m) ^ (-γ) * S.decode u m x) Real.pi := by
    intro x
    rw [((hS.2.2.2.1 u).1 m).2 x]
  have he := anglePairEvaluation_of_weakDerivative hw' hc hp
    (hS.2.2.2.2.2.2.1 u 1 m) θ
  change T.H (T.sample m) ^ γ *
    anglePairEvaluation (toIocMod Real.pi_pos 0 θ)
      ((u.val 1).val m (zeroCircleJetIndex 1),
        (u.val 1).val m (circleJetPureAngularIndex 1)) = _
  rw [he, ← mul_assoc, ← Real.rpow_add (hH m), add_neg_cancel, Real.rpow_zero, one_mul]

def circleUnitIntegral (hS : IsCircleModel T γ S)
    (f : ℝ → S.Space) (hf : Continuous f) : S.Space := by
  letI : ∀ n, CompleteSpace (S.level n) :=
    fun n => (hS.2.1 n).isComplete.completeSpace_coe
  exact projectiveUnitIntegral f hf

theorem circleUnitIntegral_decode
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 < T.M (T.sample m)) (hH : ∀ m, 0 < T.H (T.sample m))
    (f : ℝ → S.Space) (hf : Continuous f) (m : ℕ) (θ : ℝ) :
    S.decode (circleUnitIntegral hS f hf) m θ =
      ∫ a in (0 : ℝ)..1, S.decode (f a) m θ := by
  letI : ∀ n, CompleteSpace (S.level n) :=
    fun n => (hS.2.1 n).isComplete.completeSpace_coe
  change S.decode (projectiveUnitIntegral f hf) m θ = _
  rw [← circleModelValueLevel_apply hS hM hH m θ (projectiveUnitIntegral f hf),
    projectiveUnitIntegral_coordinate_map]
  apply intervalIntegral.integral_congr
  intro a ha
  exact circleModelValueLevel_apply hS hM hH m θ (f a)

end ContinuousFlexibility.Statements
