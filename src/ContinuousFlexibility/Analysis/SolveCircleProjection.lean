import ContinuousFlexibility.Analysis.StateKappaBounds

/-!
# The angular-constant projection on the physical circle space

Taking the normalized angular mean contracts the actual angular `L²` norm.
It therefore contracts every weighted circle norm and the corresponding
projective grading.  Exact realization and injectivity of the circle model
then give a continuous linear projection with zero tame loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal BigOperators NNReal

private theorem solve_angleMeasure_univ :
    angleMeasure univ = ENNReal.ofReal Real.pi := by
  rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

private instance solve_angleMeasure_finite : IsFiniteMeasure angleMeasure :=
  ⟨by rw [solve_angleMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- The constant angular mean is an `L²` contraction on the actual circle. -/
theorem eLpNorm_angularMean_const_le {u : ℝ → ℝ}
    (hu : MemLp u 2 angleMeasure) :
    eLpNorm (fun _ : ℝ => angularMean u) 2 angleMeasure ≤ eLpNorm u 2 angleMeasure := by
  have hc : MemLp (fun _ : ℝ => angularMean u) 2 angleMeasure := memLp_const _
  apply (ENNReal.toReal_le_toReal hc.eLpNorm_lt_top.ne hu.eLpNorm_lt_top.ne).mp
  rw [eLpNorm_const' _ (by norm_num) (by simp), ENNReal.toReal_mul,
    toReal_enorm, Real.norm_eq_abs, solve_angleMeasure_univ, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal Real.pi_pos.le]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← Real.sqrt_eq_rpow]
  calc
    |angularMean u| * Real.sqrt Real.pi ≤
        (((1 / Real.pi) * Real.sqrt Real.pi) *
          (eLpNorm u 2 angleMeasure).toReal) * Real.sqrt Real.pi :=
      mul_le_mul_of_nonneg_right (abs_angularMean_le_angleL2 hu) (Real.sqrt_nonneg _)
    _ = ((1 / Real.pi) * (Real.sqrt Real.pi * Real.sqrt Real.pi)) *
        (eLpNorm u 2 angleMeasure).toReal := by ring
    _ = (eLpNorm u 2 angleMeasure).toReal := by
      rw [Real.mul_self_sqrt Real.pi_pos.le, one_div,
        inv_mul_cancel₀ Real.pi_ne_zero, one_mul]

/-- The field obtained by taking the angular mean on every component. -/
def circleAngularMeanField (u : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun m _ => angularMean (u m)

theorem circleAngularMeanField_component (u : ℕ → ℝ → ℝ) (m : ℕ) :
    circleAngularMeanField u m = fun _ : ℝ => angularMean (u m) := rfl

private theorem iteratedDeriv_circleAngularMeanField_succ
    (u : ℕ → ℝ → ℝ) (m b : ℕ) :
    iteratedDeriv (b + 1) (circleAngularMeanField u m) = 0 := by
  rw [circleAngularMeanField_component]
  funext θ
  have hb : b + 1 ≠ 0 := Nat.succ_ne_zero b
  simp only [iteratedDeriv_const, hb, ↓reduceIte, Pi.zero_apply]

theorem eLpNorm_iteratedDeriv_circleAngularMeanField_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (m b : ℕ) :
    eLpNorm (iteratedDeriv b (circleAngularMeanField u m)) 2 angleMeasure ≤
      eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure := by
  cases b with
  | zero =>
    simpa only [iteratedDeriv_zero, circleAngularMeanField_component] using
      eLpNorm_angularMean_const_le (hu.2.1 m 0)
  | succ b =>
    rw [iteratedDeriv_circleAngularMeanField_succ, eLpNorm_zero]
    exact zero_le

private theorem circleAngularMean_energy_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (s : ℕ) :
    (∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (circleAngularMeanField u m))
          2 angleMeasure ^ 2) ≤
    ∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (u m)) 2 angleMeasure ^ 2 := by
  apply ENNReal.tsum_le_tsum
  intro m
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_right
    (pow_le_pow_left₀ zero_le (eLpNorm_iteratedDeriv_circleAngularMeanField_le hu m _) 2) _

/-- Angular averaging preserves all weighted circle membership conditions. -/
theorem CircleMember.angularMeanField
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ} (hu : CircleMember T γ u) :
    CircleMember T γ (circleAngularMeanField u) := by
  refine ⟨fun _ => ⟨contDiff_const, fun _ => rfl⟩, ?_, ?_⟩
  · intro m b
    cases b with
    | zero =>
      simpa only [iteratedDeriv_zero, circleAngularMeanField_component] using
        (memLp_const (angularMean (u m)) : MemLp (fun _ : ℝ => angularMean (u m)) 2 angleMeasure)
    | succ b =>
      rw [iteratedDeriv_circleAngularMeanField_succ]
      exact MemLp.zero
  · intro s
    exact (circleAngularMean_energy_le hu s).trans_lt (hu.2.2 s)

/-- The angular-constant projection contracts every actual circle norm. -/
theorem circleNorm_angularMeanField_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (s : ℕ) :
    circleNorm T γ s (circleAngularMeanField u) ≤ circleNorm T γ s u := by
  apply Real.sqrt_le_sqrt
  exact ENNReal.toReal_mono (hu.2.2 s).ne (circleAngularMean_energy_le hu s)

private def circleAngularMeanValue
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) : S.Space :=
  (hS.2.2.2.2.1 (circleAngularMeanField (S.decode u))
    (hS.2.2.2.1 u).angularMeanField).choose

private theorem circleAngularMeanValue_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) :
    S.decode (circleAngularMeanValue hS u) = circleAngularMeanField (S.decode u) :=
  (hS.2.2.2.2.1 (circleAngularMeanField (S.decode u))
    (hS.2.2.2.1 u).angularMeanField).choose_spec

private theorem solve_angularMean_add {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) :
    angularMean (u + v) = angularMean u + angularMean v := by
  unfold angularMean
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add
    (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _)]
  exact mul_add _ _ _

private theorem solve_angularMean_smul (a : ℝ) (u : ℝ → ℝ) :
    angularMean (a • u) = a * angularMean u := by
  unfold angularMean
  simp only [Pi.smul_apply]
  rw [intervalIntegral.integral_smul, smul_eq_mul]
  ring

private theorem solve_angularMean_const (a : ℝ) :
    angularMean (fun _ : ℝ => a) = a := by
  rw [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_div]
  exact inv_mul_cancel_left₀ Real.pi_ne_zero a

/-- The linear operator underlying the actual angular-constant projection. -/
def circleAngularMeanLinear
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) : S.Space →ₗ[ℝ] S.Space where
  toFun := circleAngularMeanValue hS
  map_add' := by
    intro u v
    apply hS.2.2.2.2.2.1
    simp only [circleAngularMeanValue_decode, map_add]
    funext m θ
    exact solve_angularMean_add ((hS.2.2.2.1 u).1 m).1.continuous
      ((hS.2.2.2.1 v).1 m).1.continuous
  map_smul' := by
    intro a u
    apply hS.2.2.2.2.2.1
    simp only [circleAngularMeanValue_decode, map_smul]
    funext m θ
    exact solve_angularMean_smul a (S.decode u m)

theorem circleAngularMeanLinear_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleAngularMeanLinear hS u) m θ = angularMean (S.decode u m) := by
  exact congrFun (congrFun (circleAngularMeanValue_decode hS u) m) θ

theorem circleAngularMeanLinear_grading_le
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (n : ℕ) (u : S.Space) :
    S.grading n (circleAngularMeanLinear hS u) ≤ S.grading n u := by
  apply (ContinuousFlexibility.Analysis.gradedSeminorm_le_iff
    (fun s => S.level s) S.bond n _ (apply_nonneg _ _)).mpr
  intro i hi
  calc
    ‖(circleAngularMeanLinear hS u).val i‖ =
        circleNorm T γ i (S.decode (circleAngularMeanLinear hS u)) := hS.2.2.2.2.2.2.2 _ _
    _ = circleNorm T γ i (circleAngularMeanField (S.decode u)) := by
      rw [show S.decode (circleAngularMeanLinear hS u) =
        circleAngularMeanField (S.decode u) from circleAngularMeanValue_decode hS u]
    _ ≤ circleNorm T γ i (S.decode u) := circleNorm_angularMeanField_le (hS.2.2.2.1 u) i
    _ = ‖u.val i‖ := (hS.2.2.2.2.2.2.2 u i).symm
    _ ≤ S.grading n u :=
      ContinuousFlexibility.Analysis.norm_coordinate_le_graded _ _ hi u

theorem circleAngularMeanLinear_isTame
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) :
    ContinuousFlexibility.Analysis.IsTameLinear S.grading S.grading
      (circleAngularMeanLinear hS) 0 0 := by
  intro n _
  refine ⟨1, fun u => ?_⟩
  simpa only [Nat.add_zero, NNReal.coe_one, one_mul] using
    circleAngularMeanLinear_grading_le hS n u

/-- Continuous angular averaging in the actual projective topology. -/
def circleAngularMeanProjection
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) : S.Space →L[ℝ] S.Space where
  toLinearMap := circleAngularMeanLinear hS
  cont := ContinuousFlexibility.Analysis.continuous_projectiveLimit_of_tame
    (fun s => S.level s) S.bond (fun s => S.level s) S.bond
    (circleAngularMeanLinear hS) (circleAngularMeanLinear_isTame hS)

theorem circleAngularMeanProjection_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleAngularMeanProjection hS u) m θ = angularMean (S.decode u m) :=
  circleAngularMeanLinear_decode hS u m θ

theorem circleAngularMeanProjection_isTame
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) :
    ContinuousFlexibility.Analysis.IsTameLinear S.grading S.grading
      (circleAngularMeanProjection hS).toLinearMap 0 0 :=
  circleAngularMeanLinear_isTame hS

theorem circleAngularMeanProjection_constant
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) (m : ℕ) (θ φ : ℝ) :
    S.decode (circleAngularMeanProjection hS u) m θ =
      S.decode (circleAngularMeanProjection hS u) m φ := by
  exact (circleAngularMeanProjection_decode hS u m θ).trans
    (circleAngularMeanProjection_decode hS u m φ).symm

/-- Angular averaging fixes exactly the angular-constant component. -/
theorem circleAngularMeanProjection_eq_self
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space)
    (hu : ∀ m θ φ, S.decode u m θ = S.decode u m φ) :
    circleAngularMeanProjection hS u = u := by
  apply hS.2.2.2.2.2.1
  funext m θ
  calc
    S.decode (circleAngularMeanProjection hS u) m θ = angularMean (S.decode u m) :=
      circleAngularMeanProjection_decode hS u m θ
    _ = angularMean (fun _ : ℝ => S.decode u m θ) :=
      congrArg angularMean (funext (fun φ => hu m φ θ))
    _ = S.decode u m θ := solve_angularMean_const _

theorem circleAngularMeanProjection_idempotent
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) :
    circleAngularMeanProjection hS (circleAngularMeanProjection hS u) =
      circleAngularMeanProjection hS u :=
  circleAngularMeanProjection_eq_self hS _ (circleAngularMeanProjection_constant hS u)

end ContinuousFlexibility.Statements
