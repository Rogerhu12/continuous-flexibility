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
  have hlift : circleAffineLift travel (S.decode e) 1 m =
      fun t : ℝ => t + travel m + S.decode e m t := by
    funext t
    change t + travel m + (1 : ℝ) * S.decode e m t =
      t + travel m + S.decode e m t
    rw [one_mul]
  have hd : deriv (fun t : ℝ => t + travel m + S.decode e m t) θ =
      1 + deriv (S.decode e m) θ :=
    (((hasDerivAt_id θ).add_const (travel m)).fun_add he).deriv
  exact (congrArg (fun F : ℝ → ℝ => deriv F θ) hlift).trans hd

theorem circlePositiveLiftDomain_iff
    (hS : IsCircleModel T γ S) (travel : ℕ → ℝ) (e : S.Space) :
    e ∈ circlePositiveLiftDomain S ↔
      ∀ m θ, 0 < deriv (circleAffineLift travel (S.decode e) 1 m) θ := by
  simp only [circlePositiveLiftDomain, mem_setOf_eq, circleAffineLift_deriv hS]

private theorem circle_weighted_value_bound
    {w winv A c x e : ℝ} (hw : 0 ≤ w) (hcancel : w * winv = 1)
    (hA : w ≤ A) (hc : 0 ≤ c) (he : 0 ≤ e) (hb : winv * x ≤ c * e) :
    x ≤ c * A * e := by
  calc
    x = w * (winv * x) := by rw [← mul_assoc, hcancel, one_mul]
    _ ≤ w * (c * e) := mul_le_mul_of_nonneg_left hb hw
    _ ≤ A * (c * e) := mul_le_mul_of_nonneg_right hA (mul_nonneg hc he)
    _ = c * A * e := by ring

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
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp hreal.tendsto_atTop_zero).const_mul
        (2 * circleSobolevConstant * A)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro m hm θ
  have hb : T.H (T.sample m) ^ (-γ) * |iteratedDeriv b (S.decode e m) θ| ≤
      (2 * circleSobolevConstant) * Real.sqrt (E m).toReal := by
    simpa only [E, pow_zero, one_mul] using
      circleWeighted_abs_le_componentEnergy he (hw.1 m).le (hw.2 m).le
        (m := m) (a := b) (b := 0) (s := b + 1) (by omega) θ
  have hcancel : T.H (T.sample m) ^ γ * T.H (T.sample m) ^ (-γ) = 1 := by
    rw [← Real.rpow_add (hw.2 m)]
    simp only [add_neg_cancel, Real.rpow_zero]
  have hbound : |iteratedDeriv b (S.decode e m) θ| ≤
      (2 * circleSobolevConstant * A) * Real.sqrt (E m).toReal :=
    circle_weighted_value_bound (Real.rpow_nonneg (hw.2 m).le _) hcancel
      (hHA m) (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
      (Real.sqrt_nonneg _) hb
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

private theorem component_lower_with_positive_tail
    (f : ℕ → ℝ → ℝ)
    (hcomponent : ∀ m, ∃ a : ℝ, 0 < a ∧ ∀ θ, a ≤ f m θ)
    (htail : ∃ N : ℕ, ∀ m, N ≤ m → ∀ θ, (1 / 2 : ℝ) ≤ f m θ) :
    ∃ a : ℝ, 0 < a ∧ ∀ m θ, a ≤ f m θ := by
  classical
  have hfinite (F : Finset ℕ) : ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧
      ∀ m ∈ F, ∀ θ, a ≤ f m θ := by
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
  obtain ⟨N, hN⟩ := htail
  obtain ⟨a, ha, hhalf, hfiniteBound⟩ := hfinite (Finset.range N)
  refine ⟨a, ha, ?_⟩
  intro m θ
  by_cases hm : m < N
  · exact hfiniteBound m (Finset.mem_range.mpr hm) θ
  · exact hhalf.trans (hN m (Nat.le_of_not_gt hm) θ)

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
    simpa only [iteratedDeriv_one, Pi.add_apply] using congrArg (fun x : ℝ => 1 + x) hp
  apply component_lower_with_positive_tail
    (fun m θ => 1 + deriv (S.decode e m) θ) hcomponent
  let tail := circleModel_angular_jet_tail hS hT hD hγ e 1
    (by norm_num : (0 : ℝ) < 1 / 2)
  let N : ℕ := tail.choose
  have hN : ∀ m, N ≤ m → ∀ θ, |deriv (S.decode e m) θ| < 1 / 2 := by
    intro m hm θ
    simpa only [iteratedDeriv_one] using (tail.choose_spec m hm θ)
  refine ⟨N, ?_⟩
  intro m hm θ
  have hlow : -(1 / 2 : ℝ) < deriv (S.decode e m) θ := (abs_lt.mp (hN m hm θ)).1
  linarith only [hlow]

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
  exact (he.fun_sub hf).deriv

private theorem seminorm_positive_family_local
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (f : E → ℕ → ℝ → ℝ) (e₀ : E)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A)
    (hlower : ∀ m θ, a ≤ 1 + f e₀ m θ)
    (hbound : ∀ e m θ, |f e m θ - f e₀ m θ| ≤ A * p (e - e₀)) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧ ∀ e : E,
      p (e - e₀) < δ → ∀ m θ, a ≤ 1 + f e m θ := by
  have hL : 0 < 1 + A := add_pos_of_pos_of_nonneg zero_lt_one hA
  refine ⟨a / 2, (a / 2) / (1 + A), div_pos ha (by norm_num),
    div_pos (div_pos ha (by norm_num)) hL, ?_⟩
  intro e he m θ
  have hsmall : (1 + A) * p (e - e₀) < a / 2 := by
    simpa only [mul_comm (1 + A)] using (lt_div_iff₀ hL).mp he
  have hdiff : -(a / 2) < f e m θ - f e₀ m θ :=
    (abs_lt.mp ((hbound e m θ).trans_lt
      ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
        (apply_nonneg _ _)).trans_lt hsmall))).1
  have hbase := hlower m θ
  linarith only [hdiff, hbase]

/-- A fixed second-order seminorm neighborhood preserves one common
lower derivative bound on all circles. -/
theorem circlePositiveLiftDomain_local_lower
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    {e₀ : S.Space} (he₀ : e₀ ∈ circlePositiveLiftDomain S) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧ ∀ e : S.Space,
      S.grading 2 (e - e₀) < δ → ∀ m θ, a ≤ 1 + deriv (S.decode e m) θ := by
  let lower := circlePositiveLiftDomain_uniform_lower hS hT hD hγ he₀
  let a : ℝ := lower.choose
  have ha : 0 < a := lower.choose_spec.1
  have hlower : ∀ m θ, a ≤ 1 + deriv (S.decode e₀ m) θ := lower.choose_spec.2
  let upper := material_circle_power_upper hT hD hγ
  let A : ℝ := upper.choose
  have hA : 0 ≤ A := upper.choose_spec.1
  have hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A := upper.choose_spec.2
  apply seminorm_positive_family_local (a := a)
    (A := 2 * circleSobolevConstant * A) (S.grading 2)
    (fun e m θ => deriv (S.decode e m) θ) e₀ ha
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      circleSobolevConstant_nonneg) hA) hlower
  intro e m θ
  have hb := circleModel_jet_abs_le_material_upper hS
    (material_circle_sample_weights_pos hT hD).2 hA hHA (e - e₀) m 1 θ
  simpa only [iteratedDeriv_one, circleDecode_deriv_sub hS] using hb

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
  have hcenter : S.grading 2 (e₀ - e₀) = (0 : ℝ) := by
    rw [sub_self]
    exact (map_zero (S.grading 2) : S.grading 2 (0 : S.Space) = (0 : ℝ))
  have hball : {e : S.Space | S.grading 2 (e - e₀) < δ} ∈ 𝓝 e₀ :=
    (isOpen_lt hc continuous_const).mem_nhds (hcenter.trans_lt hδ)
  apply mem_of_superset hball
  intro e he m θ
  exact ha.trans_le (hbound e he m θ)

end ContinuousFlexibility.Statements
