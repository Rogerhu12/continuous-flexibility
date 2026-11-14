module

public import ContinuousFlexibility.Analysis.ProjectiveUnitIntegral
public import ContinuousFlexibility.Analysis.CircleJetEvaluation
public import ContinuousFlexibility.Analysis.CircleModelRealization

/-!
# Parameter integration and the actual circle decoder

The supplied model's weak derivative graph represents point evaluation
by the value and first angular derivative in level one. This finite-level
formula proves that the existing decoder commutes with projective
parameter integration, without replacing the circle model.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

private theorem circleUnitIntegral_mul_cancel
    (a b c : ℝ) (h : a * b = 1) : a * (b * c) = c :=
  (mul_assoc a b c).symm.trans
    ((congrArg (fun t : ℝ => t * c) h).trans (one_mul c))

def circleModelValueLevel (T : MaterialData) (γ : ℝ) (S : CircleModelData)
    (m : ℕ) (θ : ℝ) : S.level 1 →L[ℝ] ℝ :=
  T.H (T.sample m) ^ γ • (anglePairEvaluation (toIocMod Real.pi_pos 0 θ)).comp
    (((circleJetCoordinate 1 m (zeroCircleJetIndex 1)).comp (S.level 1).subtypeL).prod
      ((circleJetCoordinate 1 m (circleJetPureAngularIndex 1)).comp (S.level 1).subtypeL))

private theorem circleModelValueLevel_coordinates
    (m : ℕ) (θ : ℝ) (v : S.level 1) :
    circleModelValueLevel T γ S m θ v = T.H (T.sample m) ^ γ *
      anglePairEvaluation (toIocMod Real.pi_pos 0 θ)
        (v.val m (zeroCircleJetIndex 1), v.val m (circleJetPureAngularIndex 1)) := by
  simp only [circleModelValueLevel, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    Submodule.subtypeL_apply, circleJetCoordinate_apply, smul_eq_mul]

private theorem circleModelValueLevel_weakDerivative
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 < T.M (T.sample m)) (m : ℕ) (u : S.Space) :
    HasWeakAngularDerivative
      ((u.val 1).val m (zeroCircleJetIndex 1))
      ((u.val 1).val m (circleJetPureAngularIndex 1)) 1 := by
  have hg : (u.val 1).val ∈ circleJetGraph T 1 := by
    rw [← hS.1 1]
    exact (u.val 1).property
  have hw := (mem_circleJetGraph_iff_normalized hM (u.val 1).val).mp hg
    m (circleJetPureAngularIndex 1)
  simpa only [circleJetNormalizedDerivative_apply, circleJetWeight,
    circleJetPureAngularIndex_order, circleJetPureAngularIndex_weight,
    pow_zero, inv_one, one_smul] using hw

theorem circleModelValueLevel_apply
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 < T.M (T.sample m)) (hH : ∀ m, 0 < T.H (T.sample m))
    (m : ℕ) (θ : ℝ) (u : S.Space) :
    circleModelValueLevel T γ S m θ (u.val 1) = S.decode u m θ := by
  have hc : Continuous (fun x => T.H (T.sample m) ^ (-γ) * S.decode u m x) :=
    continuous_const.mul (((hS.2.2.2.1 u).1 m).1.continuous)
  have hp : Function.Periodic
      (fun x => T.H (T.sample m) ^ (-γ) * S.decode u m x) Real.pi := by
    intro x
    exact congrArg (fun y : ℝ => T.H (T.sample m) ^ (-γ) * y)
      (((hS.2.2.2.1 u).1 m).2 x)
  have he := anglePairEvaluation_of_weakDerivative
    (circleModelValueLevel_weakDerivative hS hM m u) hc hp
    (hS.2.2.2.2.2.2.1 u 1 m) θ
  have hw : T.H (T.sample m) ^ γ * T.H (T.sample m) ^ (-γ) = 1 := by
    rw [← Real.rpow_add (hH m), add_neg_cancel, Real.rpow_zero]
  calc
    circleModelValueLevel T γ S m θ (u.val 1) =
        T.H (T.sample m) ^ γ *
          anglePairEvaluation (toIocMod Real.pi_pos 0 θ)
            ((u.val 1).val m (zeroCircleJetIndex 1),
              (u.val 1).val m (circleJetPureAngularIndex 1)) :=
      circleModelValueLevel_coordinates (T := T) (γ := γ) (S := S) m θ (u.val 1)
    _ = T.H (T.sample m) ^ γ *
        (T.H (T.sample m) ^ (-γ) * S.decode u m θ) :=
      congrArg (fun y : ℝ => T.H (T.sample m) ^ γ * y) he
    _ = S.decode u m θ := circleUnitIntegral_mul_cancel _ _ _ hw

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
  calc
    S.decode (projectiveUnitIntegral f hf) m θ =
        circleModelValueLevel T γ S m θ ((projectiveUnitIntegral f hf).val 1) :=
      (circleModelValueLevel_apply hS hM hH m θ (projectiveUnitIntegral f hf)).symm
    _ = ∫ a in (0 : ℝ)..1, circleModelValueLevel T γ S m θ ((f a).val 1) :=
      projectiveUnitIntegral_coordinate_map (F := fun n => S.level n) (bond := S.bond)
        hf 1 (circleModelValueLevel T γ S m θ)
    _ = ∫ a in (0 : ℝ)..1, S.decode (f a) m θ :=
      intervalIntegral.integral_congr fun a _ => circleModelValueLevel_apply hS hM hH m θ (f a)

end ContinuousFlexibility.Statements
