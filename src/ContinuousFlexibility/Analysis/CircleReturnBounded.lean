import ContinuousFlexibility.Analysis.CircleReturnSmoothInverse
import ContinuousFlexibility.Analysis.CircleJetClosedGraph
import ContinuousFlexibility.Analysis.CircleWeightedEstimate

/-!
# The leading return operator on the actual weighted circle space

Translations and reflection preserve the unnormalized L² norm on one
period. The even projection therefore contracts that norm. Applying this
to each angular derivative gives a bound at every existing circle level,
with no derivative or sample-weight loss.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory Statements
open scoped ContDiff RealInnerProductSpace BigOperators ENNReal

theorem circle_angleL2_sq_eq_integral {f : ℝ → ℝ} (hf : Continuous f) :
    (eLpNorm f 2 angleMeasure).toReal ^ 2 =
      ∫ θ in (0 : ℝ)..Real.pi, f θ ^ 2 := by
  have hlp := memLp_angleMeasure_of_continuous hf
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  change _ = ∫ θ, f θ ^ 2 ∂angleMeasure
  rw [← Lp.norm_toLp f hlp, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hlp] with θ hθ
  simp only [hθ, RCLike.inner_apply, conj_trivial, sq]

theorem circle_angleL2_shift {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f Real.pi) (t : ℝ) :
    eLpNorm (fun θ => f (θ + t)) 2 angleMeasure = eLpNorm f 2 angleMeasure := by
  have hs : Continuous (fun θ : ℝ => f (θ + t)) := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq] using
      hf.comp (show Continuous (fun θ : ℝ => θ + t) from continuous_id.add continuous_const)
  apply (ENNReal.toReal_eq_toReal_iff'
    (memLp_angleMeasure_of_continuous hs).eLpNorm_ne_top
    (memLp_angleMeasure_of_continuous hf).eLpNorm_ne_top).mp
  have hp2 : Function.Periodic (fun θ => f θ ^ 2) Real.pi :=
    fun θ => congrArg (fun x : ℝ => x ^ 2) (hp θ)
  have heq : (eLpNorm (fun θ => f (θ + t)) 2 angleMeasure).toReal ^ 2 =
      (eLpNorm f 2 angleMeasure).toReal ^ 2 := by
    rw [circle_angleL2_sq_eq_integral hs, circle_angleL2_sq_eq_integral hf]
    exact circle_periodic_shift_integral hp2 t
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f 2 angleMeasure),
    ENNReal.toReal_nonneg (a := eLpNorm (fun θ => f (θ + t)) 2 angleMeasure)]

theorem circle_angleL2_reflect {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f Real.pi) :
    eLpNorm (fun θ => f (-θ)) 2 angleMeasure = eLpNorm f 2 angleMeasure := by
  have hs : Continuous (fun θ : ℝ => f (-θ)) := by
    simpa only [Function.comp_def] using hf.comp continuous_neg
  apply (ENNReal.toReal_eq_toReal_iff'
    (memLp_angleMeasure_of_continuous hs).eLpNorm_ne_top
    (memLp_angleMeasure_of_continuous hf).eLpNorm_ne_top).mp
  have hp2 : Function.Periodic (fun θ => f θ ^ 2) Real.pi :=
    fun θ => congrArg (fun x : ℝ => x ^ 2) (hp θ)
  have heq : (eLpNorm (fun θ => f (-θ)) 2 angleMeasure).toReal ^ 2 =
      (eLpNorm f 2 angleMeasure).toReal ^ 2 := by
    rw [circle_angleL2_sq_eq_integral hs, circle_angleL2_sq_eq_integral hf,
      intervalIntegral.integral_comp_neg (f := fun θ : ℝ => f θ ^ 2)]
    simpa only [neg_zero, neg_add_cancel, zero_add] using hp2.intervalIntegral_add_eq (-Real.pi) 0
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f 2 angleMeasure),
    ENNReal.toReal_nonneg (a := eLpNorm (fun θ => f (-θ)) 2 angleMeasure)]

/-- The affine reflected shift has exactly the same norm on one period. -/
theorem circle_angleL2_reflected_shift {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f Real.pi) (t : ℝ) :
    eLpNorm (fun θ => f (t - θ)) 2 angleMeasure = eLpNorm f 2 angleMeasure := by
  have hs : Continuous (fun θ : ℝ => f (θ + t)) := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq] using
      hf.comp (show Continuous (fun θ : ℝ => θ + t) from continuous_id.add continuous_const)
  have hps : Function.Periodic (fun θ => f (θ + t)) Real.pi := by
    intro θ
    have h := hp (θ + t)
    simpa only [add_assoc, add_comm Real.pi t] using h
  have h := circle_angleL2_reflect hs hps
  have heq : (fun θ => f (-θ + t)) = (fun θ => f (t - θ)) := by
    funext θ
    congr 1
    ring
  simpa only [heq, circle_angleL2_shift hf hp t] using h

/-- Every derivative of the leading operator is the corresponding
translated/reflected average, with the reflection sign retained. -/
theorem iteratedDeriv_circleReturnShift {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) (s : ℕ) (θ : ℝ) :
    iteratedDeriv s (circleReturnShift t f) θ =
      (iteratedDeriv s f (θ + t) +
        (-1 : ℝ) ^ s * iteratedDeriv s f (t - θ)) / 2 := by
  have heq : circleReturnShift t f =
      (fun θ => (f (θ + t) + f (t - θ)) / 2) := by
    funext θ
    unfold circleReturnShift circleReturnEven
    congr 2
    congr 1
    ring
  rw [heq, iteratedDeriv_div_const]
  have hplus : ContDiff ℝ ∞ (fun x : ℝ => f (x + t)) := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq] using
      hf.comp (show ContDiff ℝ ∞ (fun x : ℝ => x + t) from contDiff_id.add contDiff_const)
  have hminus : ContDiff ℝ ∞ (fun x : ℝ => f (t - x)) := by
    simpa only [Function.comp_def, Pi.sub_apply, id_eq] using
      hf.comp (show ContDiff ℝ ∞ (fun x : ℝ => t - x) from contDiff_const.sub contDiff_id)
  rw [iteratedDeriv_fun_add
    (hplus.contDiffAt.of_le (by simp)) (hminus.contDiffAt.of_le (by simp))]
  rw [iteratedDeriv_comp_add_const, iteratedDeriv_comp_const_sub]
  simp only [smul_eq_mul]

theorem circle_angleL2_return_deriv_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (t : ℝ) (s : ℕ) :
    eLpNorm (iteratedDeriv s (circleReturnShift t f)) 2 angleMeasure ≤
      eLpNorm (iteratedDeriv s f) 2 angleMeasure := by
  have hd := hf.continuous_iteratedDeriv s (by simp)
  have hpd : Function.Periodic (iteratedDeriv s f) Real.pi := by
    have heq : (fun x : ℝ => f (x + Real.pi)) = f := funext hp
    intro x
    have h := congrArg (fun g : ℝ → ℝ => iteratedDeriv s g x) heq
    simpa only [iteratedDeriv_comp_add_const] using h
  have heq : iteratedDeriv s (circleReturnShift t f) =
      (2 : ℝ)⁻¹ • ((fun θ => iteratedDeriv s f (θ + t)) +
        (-1 : ℝ) ^ s • (fun θ => iteratedDeriv s f (t - θ))) := by
    funext θ
    rw [iteratedDeriv_circleReturnShift hf]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  have hsign : ‖(-1 : ℝ) ^ s‖ₑ = 1 := by
    rw [Real.enorm_eq_ofReal_abs, abs_pow]
    norm_num
  have hhalf : ENNReal.ofReal |(2 : ℝ)⁻¹| * (2 : ℝ≥0∞) = 1 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) from by norm_num,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    norm_num
  calc
    _ ≤ ENNReal.ofReal |(2 : ℝ)⁻¹| *
        (eLpNorm (fun θ => iteratedDeriv s f (θ + t)) 2 angleMeasure +
          eLpNorm ((-1 : ℝ) ^ s • (fun θ => iteratedDeriv s f (t - θ))) 2 angleMeasure) :=
      mul_le_mul_of_nonneg_left (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)) zero_le
    _ = _ := by
      rw [eLpNorm_const_smul, hsign, one_mul,
        circle_angleL2_shift hd hpd t, circle_angleL2_reflected_shift hd hpd t,
        ← two_mul, ← mul_assoc, hhalf, one_mul]

theorem periodic_circleReturnShift_of_periodic {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (t : ℝ) :
    Function.Periodic (circleReturnShift t f) Real.pi := by
  intro θ
  unfold circleReturnShift circleReturnEven
  have hpos : f (θ + Real.pi + t) = f (θ + t) := by
    convert hp (θ + t) using 1 <;> congr 1 <;> ring
  have hneg : f (-(θ + Real.pi) + t) = f (-θ + t) := by
    convert hp.neg (-θ + t) using 1 <;> congr 1 <;> ring
  dsimp only
  rw [hpos, hneg]

theorem circleMember_circleReturnShift
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (travel : ℕ → ℝ) :
    CircleMember T γ (fun m => circleReturnShift (travel m) (u m)) := by
  apply circleMember_of_jet_bound hu 0 0
  · intro m
    exact ⟨contDiff_circleReturnShift (hu.1 m).1 (travel m),
      periodic_circleReturnShift_of_periodic (hu.1 m).2 (travel m)⟩
  · intro m b
    exact memLp_angleMeasure_iteratedDeriv_of_contDiff
      (contDiff_circleReturnShift (hu.1 m).1 (travel m)) b
  · intro s
    refine ⟨1, by norm_num, ?_⟩
    intro m j
    simpa only [Nat.add_zero, one_mul] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left'
        (circle_angleL2_return_deriv_le (hu.1 m).1 (hu.1 m).2 (travel m) (j.val 0).val) 2)
        (show 0 ≤ ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
          T.H (T.sample m) ^ (-γ)) ^ 2) from zero_le)

theorem circleNorm_circleReturnShift_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (travel : ℕ → ℝ) (s : ℕ) :
    circleNorm T γ s (fun m => circleReturnShift (travel m) (u m)) ≤
      circleNorm T γ s u := by
  have h := circleNorm_le_of_jet_bound
    (v := fun m => circleReturnShift (travel m) (u m)) hu s 0 0 (C := 1) zero_le_one
  simp only [Nat.add_zero, one_mul] at h
  apply h
  intro m j
  simpa only [one_pow, ENNReal.ofReal_one, one_mul] using
    mul_le_mul_of_nonneg_left (pow_le_pow_left'
      (circle_angleL2_return_deriv_le (hu.1 m).1 (hu.1 m).2 (travel m) (j.val 0).val) 2)
      (show 0 ≤ ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) from zero_le)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

/-- The scalar leading operator, applied to the actual decoded fields. -/
def circleReturnFieldLinear (S : CircleModelData) (travel : ℕ → ℝ) :
    S.Space →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun u m θ := circleReturnShift (travel m) (S.decode u m) θ
  map_add' u v := by
    funext m θ
    simp only [map_add, Pi.add_apply, circleReturnShift, circleReturnEven]
    ring
  map_smul' c u := by
    funext m θ
    simp only [map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, circleReturnShift, circleReturnEven]
    ring

theorem circleReturnFieldLinear_apply (S : CircleModelData) (travel : ℕ → ℝ)
    (u : S.Space) (m : ℕ) (θ : ℝ) :
    circleReturnFieldLinear S travel u m θ =
      circleReturnShift (travel m) (S.decode u m) θ := rfl

def circleReturnLinear {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ) : S.Space →ₗ[ℝ] S.Space :=
  liftCircleLinear hS (circleReturnFieldLinear S travel)
    (fun u => circleMember_circleReturnShift (hS.2.2.2.1 u) travel)

theorem circleReturnLinear_decode {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ) (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleReturnLinear hS travel u) m θ =
      circleReturnShift (travel m) (S.decode u m) θ := by
  have h : S.decode (liftCircleLinear hS (circleReturnFieldLinear S travel)
      (fun v => circleMember_circleReturnShift (hS.2.2.2.1 v) travel) u) =
      circleReturnFieldLinear S travel u :=
    liftCircleLinear_decode hS (circleReturnFieldLinear S travel)
      (fun v => circleMember_circleReturnShift (hS.2.2.2.1 v) travel) u
  exact congrFun (congrFun h m) θ

theorem circleReturnLinear_tame {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ) :
    IsTameLinear S.grading S.grading (circleReturnLinear hS travel) 0 0 := by
  apply liftCircleLinear_isTame hS _ _ S.grading
    (gradedSeminorm_monotone (fun i => S.level i) S.bond) 0
  intro n
  refine ⟨1, ?_⟩
  intro u
  simp only [NNReal.coe_one, one_mul, Nat.add_zero]
  have h := circleNorm_circleReturnShift_le (hS.2.2.2.1 u) travel n
  have hn := hS.2.2.2.2.2.2.2 u n
  rw [← hn] at h
  exact h.trans (norm_coordinate_le_graded (fun i => S.level i) S.bond le_rfl u)

/-- The actual continuous linear leading term required in N02. -/
def circleReturnContinuousLinear {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ) : S.Space →L[ℝ] S.Space :=
  (circleReturnLinear_tame hS travel).toContinuousLinearMap
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)

theorem circleReturnContinuousLinear_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ) (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleReturnContinuousLinear hS travel u) m θ =
      circleReturnShift (travel m) (S.decode u m) θ := by
  have heq : circleReturnContinuousLinear hS travel u = circleReturnLinear hS travel u :=
    IsTameLinear.toContinuousLinearMap_apply (circleReturnLinear_tame hS travel)
      (withSeminorms_graded (fun i => S.level i) S.bond)
      (withSeminorms_graded (fun i => S.level i) S.bond)
      (gradedSeminorm_monotone (fun i => S.level i) S.bond) u
  rw [heq]
  exact circleReturnLinear_decode hS travel u m θ

end ContinuousFlexibility.Statements
