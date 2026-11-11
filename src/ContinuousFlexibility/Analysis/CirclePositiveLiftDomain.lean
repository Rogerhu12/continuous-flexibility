import ContinuousFlexibility.Analysis.CircleInverseModel
import ContinuousFlexibility.Analysis.CircleJetPointwiseEnergy
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The open domain of positive circle lifts

The actual weighted component energies are summable. Hence every fixed
angular derivative of a decoded circle field tends uniformly to zero
along the components. A positive degree-one lift consequently has one
positive lower derivative bound on all components, and that bound persists
on a neighborhood measured by the original second circle grading.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance circlePositiveLiftDomainRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circlePositiveLiftDomain (S : CircleModelData) : Set S.Space :=
  {e | ∀ m θ, 0 < 1 + deriv (S.decode e m) θ}

theorem circleAffineLift_deriv
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ)
    (e : S.Space) (m : ℕ) (θ : ℝ) :
    deriv (circleAffineLift travel (S.decode e) 1 m) θ =
      1 + deriv (S.decode e m) θ := by
  have he : HasDerivAt (S.decode e m) (deriv (S.decode e m) θ) θ :=
    (((hS.2.2.2.1 e).1 m).1.differentiable (by simp)).differentiableAt.hasDerivAt
  simpa only [circleAffineLift, one_mul, Pi.add_apply] using
    (((hasDerivAt_id θ).add_const (travel m)).add he).deriv

theorem circlePositiveLiftDomain_iff
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ) (e : S.Space) :
    e ∈ circlePositiveLiftDomain S ↔
      ∀ m θ, 0 < deriv (circleAffineLift travel (S.decode e) 1 m) θ := by
  simp only [circlePositiveLiftDomain, mem_setOf_eq, circleAffineLift_deriv hS]

/-- The componentwise Sobolev envelope tends to zero because its squared
energies form part of the actual finite circle norm. -/
theorem circleModel_angular_jet_tail
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (e : S.Space) (b : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ θ,
      |iteratedDeriv b (S.decode e m) θ| < δ := by
  have he : CircleMember T γ (S.decode e) := hS.2.2.2.1 e
  have hw := material_circle_sample_weights_pos hT hD
  obtain ⟨A, hA, hHA⟩ := material_circle_power_upper hT hD hγ
  let E : ℕ → ℝ≥0∞ := circleComponentEnergy T γ (b + 1) (S.decode e)
  have hsum : (∑' m, E m) < ⊤ := he.2.2 (b + 1)
  have hreal : Summable (fun m => (E m).toReal) := ENNReal.summable_toReal hsum.ne
  have hlim : Tendsto (fun m => (2 * circleSobolevConstant * A) * Real.sqrt (E m).toReal)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero, mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp hreal.tendsto_atTop_zero).const_mul
        (2 * circleSobolevConstant * A)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro m hm θ
  have hb := circleWeighted_abs_le_componentEnergy he (hw.1 m).le (hw.2 m).le
    (a := b) (b := 0) (s := b + 1) (by omega) θ
  simp only [pow_zero, one_mul] at hb
  have hcancel : T.H (T.sample m) ^ γ * T.H (T.sample m) ^ (-γ) = 1 := by
    rw [← Real.rpow_add (hw.2 m)]
    simp only [add_neg_cancel, Real.rpow_zero]
  have hbound : |iteratedDeriv b (S.decode e m) θ| ≤
      (2 * circleSobolevConstant * A) * Real.sqrt (E m).toReal := by
    calc
      _ = T.H (T.sample m) ^ γ *
          (T.H (T.sample m) ^ (-γ) * |iteratedDeriv b (S.decode e m) θ|) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ T.H (T.sample m) ^ γ *
          (2 * circleSobolevConstant * Real.sqrt (E m).toReal) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (hw.2 m).le _)
      _ ≤ A * (2 * circleSobolevConstant * Real.sqrt (E m).toReal) :=
        mul_le_mul_of_nonneg_right (hHA m)
          (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
            (Real.sqrt_nonneg _))
      _ = _ := by ring
  exact hbound.trans_lt (hN m hm)

private theorem periodic_positive_has_uniform_lower
    {g : ℝ → ℝ} (hg : Continuous g) (hp : Function.Periodic g Real.pi)
    (hpos : ∀ θ, 0 < g θ) : ∃ a : ℝ, 0 < a ∧ ∀ θ, a ≤ g θ := by
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr Real.pi_pos.le) hg.continuousOn
  refine ⟨g x, hpos x, ?_⟩
  intro θ
  let y := toIocMod Real.pi_pos 0 θ
  let n := toIocDiv Real.pi_pos 0 θ
  have hy : y ∈ Icc (0 : ℝ) Real.pi := by
    have h : y ∈ Ioc (0 : ℝ) Real.pi := by
      simpa only [y, zero_add] using toIocMod_mem_Ioc Real.pi_pos 0 θ
    exact ⟨h.1.le, h.2⟩
  have hθ : y + n • Real.pi = θ := toIocMod_add_toIocDiv_zsmul Real.pi_pos 0 θ
  have heq : g θ = g y := (congrArg g hθ.symm).trans (hp.zsmul n y)
  exact (hmin hy).trans_eq heq.symm

theorem circlePositiveLiftDomain_uniform_lower
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    {e : S.Space} (he : e ∈ circlePositiveLiftDomain S) :
    ∃ a : ℝ, 0 < a ∧ ∀ m θ, a ≤ 1 + deriv (S.decode e m) θ := by
  classical
  have hcomponent (m : ℕ) : ∃ a : ℝ, 0 < a ∧
      ∀ θ, a ≤ 1 + deriv (S.decode e m) θ := by
    apply periodic_positive_has_uniform_lower
      (continuous_const.add (((hS.2.2.2.1 e).1 m).1.continuous_deriv (by simp)))
      _ (he m)
    intro θ
    have hp := circlePeriodic_iteratedDeriv_real ((hS.2.2.2.1 e).1 m).2 1 θ
    simpa only [iteratedDeriv_one] using congrArg (fun x : ℝ => 1 + x) hp
  have hfinite (F : Finset ℕ) : ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧
      ∀ m ∈ F, ∀ θ, a ≤ 1 + deriv (S.decode e m) θ := by
    induction F using Finset.induction_on with
    | empty => exact ⟨1 / 2, by norm_num, le_rfl, by simp⟩
    | @insert m F hm ih =>
      obtain ⟨a, ha, hhalf, hbound⟩ := ih
      obtain ⟨c, hc, hcBound⟩ := hcomponent m
      refine ⟨min a c, lt_min ha hc, (min_le_left _ _).trans hhalf, ?_⟩
      intro j hj θ
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans (hcBound θ)
      · exact (min_le_left _ _).trans (hbound j hj θ)
  obtain ⟨N, hN⟩ := circleModel_angular_jet_tail hS hT hD hγ e 1
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨a, ha, hhalf, hfiniteBound⟩ := hfinite (Finset.range N)
  refine ⟨a, ha, ?_⟩
  intro m θ
  by_cases hm : m < N
  · exact hfiniteBound m (Finset.mem_range.mpr hm) θ
  · have hb : |deriv (S.decode e m) θ| < 1 / 2 := by
      simpa only [iteratedDeriv_one] using hN m (Nat.le_of_not_gt hm) θ
    have hlow := (abs_lt.mp hb).1
    linarith only [hhalf, hlow]

private theorem circleDecode_deriv_sub
    (hS : IsCircleModel T γ S) (e f : S.Space) (m : ℕ) (θ : ℝ) :
    deriv (S.decode (e - f) m) θ = deriv (S.decode e m) θ - deriv (S.decode f m) θ := by
  have he : HasDerivAt (S.decode e m) (deriv (S.decode e m) θ) θ :=
    (((hS.2.2.2.1 e).1 m).1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hf : HasDerivAt (S.decode f m) (deriv (S.decode f m) θ) θ :=
    (((hS.2.2.2.1 f).1 m).1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hfield : S.decode (e - f) m = fun t => S.decode e m t - S.decode f m t := by
    funext t
    exact congrFun (congrFun (S.decode.map_sub e f) m) t
  rw [hfield]
  simpa only [Pi.sub_apply] using (he.sub hf).deriv

/-- A fixed second-order seminorm neighborhood preserves one common
lower derivative bound on all circles. -/
theorem circlePositiveLiftDomain_local_lower
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    {e₀ : S.Space} (he₀ : e₀ ∈ circlePositiveLiftDomain S) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧ ∀ e : S.Space,
      S.grading 2 (e - e₀) < δ → ∀ m θ, a ≤ 1 + deriv (S.decode e m) θ := by
  obtain ⟨a, ha, hlower⟩ := circlePositiveLiftDomain_uniform_lower hS hT hD hγ he₀
  obtain ⟨A, hA, hHA⟩ := material_circle_power_upper hT hD hγ
  let L : ℝ := 1 + 2 * circleSobolevConstant * A
  have hL : 0 < L := add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hA)
  refine ⟨a / 2, (a / 2) / L, by positivity, div_pos (by positivity) hL, ?_⟩
  intro e he m θ
  have hb := circleModel_jet_abs_le_material_upper hS
    (material_circle_sample_weights_pos hT hD).2 hA hHA (e - e₀) m 1 θ
  simp only [iteratedDeriv_one, circleDecode_deriv_sub hS] at hb
  have hbound : |deriv (S.decode e m) θ - deriv (S.decode e₀ m) θ| ≤
      L * S.grading 2 (e - e₀) := by
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (by dsimp only [L]; linarith)
      (apply_nonneg _ _)
  have hsmall : L * S.grading 2 (e - e₀) < a / 2 := by
    simpa only [mul_comm L] using (lt_div_iff₀ hL).mp he
  have hdiff := (abs_lt.mp (hbound.trans_lt hsmall)).1
  have hbase := hlower m θ
  linarith only [hdiff, hbase]

theorem circlePositiveLiftDomain_isOpen
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) :
    IsOpen (circlePositiveLiftDomain S) := by
  apply isOpen_iff_mem_nhds.mpr
  intro e₀ he₀
  obtain ⟨a, δ, ha, hδ, hbound⟩ := circlePositiveLiftDomain_local_lower hS hT hD hγ he₀
  have hc : Continuous (fun e : S.Space => S.grading 2 (e - e₀)) :=
    ((withSeminorms_graded (fun j => S.level j) S.bond).continuous_seminorm 2).comp
      (continuous_id.sub continuous_const)
  have hball : {e : S.Space | S.grading 2 (e - e₀) < δ} ∈ 𝓝 e₀ :=
    (isOpen_lt hc continuous_const).mem_nhds
      (by simpa only [mem_setOf_eq, sub_self, (S.grading 2).map_zero'] using hδ)
  apply mem_of_superset hball
  intro e he m θ
  exact ha.trans_le (hbound e he m θ)

end ContinuousFlexibility.Statements
