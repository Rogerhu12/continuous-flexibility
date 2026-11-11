import ContinuousFlexibility.Analysis.SolveCircleProjection
import ContinuousFlexibility.Analysis.CircleJetEncoding

/-!
# Bounded component multipliers in the physical circle space

The diagonal inverse in the control equation acts on the weighted circle
space as well as on its base Banach space.  This file realizes that action
in any of the actual circle models, with the same bound at every order.
The angular-constant recovery therefore does not assume that an arbitrary
base-space control already has all weighted orders.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff NNReal

/-- A scalar multiplier that is constant along each circle component. -/
def coupledCircleMultiplierField (a : ℕ → ℝ) (u : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun m θ => a m * u m θ

theorem coupledCircleMultiplierField_component (a : ℕ → ℝ)
    (u : ℕ → ℝ → ℝ) (m : ℕ) :
    coupledCircleMultiplierField a u m = a m • u m := rfl

theorem coupledCircleMultiplierField_iteratedDeriv (a : ℕ → ℝ)
    (u : ℕ → ℝ → ℝ) (m b : ℕ) :
    iteratedDeriv b (coupledCircleMultiplierField a u m) =
      a m • iteratedDeriv b (u m) := by
  funext θ
  simp only [coupledCircleMultiplierField, iteratedDeriv_const_mul_field,
    Pi.smul_apply, smul_eq_mul]

private theorem coupledCircleMultiplierField_eLpNorm_le
    (a : ℕ → ℝ) (u : ℕ → ℝ → ℝ) (c : ℝ)
    (ha : ∀ m, |a m| ≤ |c|) (m b : ℕ) :
    eLpNorm (iteratedDeriv b (coupledCircleMultiplierField a u m)) 2 angleMeasure ≤
      eLpNorm (iteratedDeriv b (coupledCircleMultiplierField (fun _ => c) u m))
        2 angleMeasure := by
  rw [coupledCircleMultiplierField_iteratedDeriv,
    coupledCircleMultiplierField_iteratedDeriv, eLpNorm_const_smul, eLpNorm_const_smul,
    Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (ha m)) le_rfl

private theorem coupledCircleMultiplierField_energy_le
    (T : MaterialData) (γ : ℝ) (a : ℕ → ℝ) (u : ℕ → ℝ → ℝ) (c : ℝ)
    (ha : ∀ m, |a m| ≤ |c|) (s : ℕ) :
    (∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (coupledCircleMultiplierField a u m))
          2 angleMeasure ^ 2) ≤
    ∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val
          (coupledCircleMultiplierField (fun _ => c) u m)) 2 angleMeasure ^ 2 := by
  apply ENNReal.tsum_le_tsum
  intro m
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul' le_rfl
    (pow_le_pow_left₀ zero_le
      (coupledCircleMultiplierField_eLpNorm_le a u c ha m _) 2)

private theorem coupledCircleMultiplierField_const_decode
    (S : CircleModelData) (u : S.Space) (c : ℝ) :
    coupledCircleMultiplierField (fun _ => c) (S.decode u) = S.decode (c • u) := by
  rw [map_smul]
  rfl

/-- Every bounded component multiplier preserves all angular and weight
orders of the actual circle model. -/
theorem coupledCircleMultiplierField_mem
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (a : ℕ → ℝ) (C : ℝ≥0)
    (ha : ∀ m, |a m| ≤ C) (u : S.Space) :
    CircleMember T γ (coupledCircleMultiplierField a (S.decode u)) := by
  have hu : CircleMember T γ (S.decode u) := hS.2.2.2.1 u
  have hCu : CircleMember T γ (S.decode ((C : ℝ) • u)) :=
    hS.2.2.2.1 ((C : ℝ) • u)
  have hbound : ∀ m, |a m| ≤ |(C : ℝ)| := by
    simpa only [abs_of_nonneg C.coe_nonneg] using ha
  refine ⟨?_, ?_, ?_⟩
  · intro m
    refine ⟨contDiff_const.mul (hu.1 m).1, ?_⟩
    intro θ
    exact congrArg (a m * ·) ((hu.1 m).2 θ)
  · intro m b
    rw [coupledCircleMultiplierField_iteratedDeriv]
    exact (hu.2.1 m b).const_smul (a m)
  · intro s
    have henergy := coupledCircleMultiplierField_energy_le T γ a (S.decode u)
      C hbound s
    rw [coupledCircleMultiplierField_const_decode] at henergy
    exact henergy.trans_lt (hCu.2.2 s)

private def coupledCircleMultiplierValue
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (a : ℕ → ℝ) (C : ℝ≥0)
    (ha : ∀ m, |a m| ≤ C) (u : S.Space) : S.Space :=
  (hS.2.2.2.2.1 (coupledCircleMultiplierField a (S.decode u))
    (coupledCircleMultiplierField_mem hS a C ha u)).choose

private theorem coupledCircleMultiplierValue_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (a : ℕ → ℝ) (C : ℝ≥0)
    (ha : ∀ m, |a m| ≤ C) (u : S.Space) :
    S.decode (coupledCircleMultiplierValue hS a C ha u) =
      coupledCircleMultiplierField a (S.decode u) :=
  (hS.2.2.2.2.1 (coupledCircleMultiplierField a (S.decode u))
    (coupledCircleMultiplierField_mem hS a C ha u)).choose_spec

/-- The actual circle multiplier, as a linear map. -/
def coupledCircleMultiplierLinear
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (a : ℕ → ℝ) (C : ℝ≥0)
    (ha : ∀ m, |a m| ≤ C) : S.Space →ₗ[ℝ] S.Space where
  toFun := coupledCircleMultiplierValue hS a C ha
  map_add' := by
    intro u v
    apply hS.2.2.2.2.2.1
    simp only [coupledCircleMultiplierValue_decode, map_add]
    funext m θ
    exact mul_add (a m) (S.decode u m θ) (S.decode v m θ)
  map_smul' := by
    intro c u
    apply hS.2.2.2.2.2.1
    simp only [coupledCircleMultiplierValue_decode, map_smul]
    funext m θ
    change a m * (c * S.decode u m θ) = c * (a m * S.decode u m θ)
    ring

theorem coupledCircleMultiplierLinear_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (a : ℕ → ℝ) (C : ℝ≥0)
    (ha : ∀ m, |a m| ≤ C) (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (coupledCircleMultiplierLinear hS a C ha u) m θ = a m * S.decode u m θ :=
  congrFun (congrFun (coupledCircleMultiplierValue_decode hS a C ha u) m) θ

/-- One bound works simultaneously for every projective seminorm. -/
theorem coupledCircleMultiplierLinear_grading_le
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (a : ℕ → ℝ) (C : ℝ≥0)
    (ha : ∀ m, |a m| ≤ C) (n : ℕ) (u : S.Space) :
    S.grading n (coupledCircleMultiplierLinear hS a C ha u) ≤ C * S.grading n u := by
  apply (ContinuousFlexibility.Analysis.gradedSeminorm_le_iff
    (fun s => S.level s) S.bond n _ (mul_nonneg C.coe_nonneg (apply_nonneg _ _))).mpr
  intro i hi
  have henergy := coupledCircleMultiplierField_energy_le T γ a (S.decode u) C
    (by simpa only [abs_of_nonneg C.coe_nonneg] using ha) i
  rw [coupledCircleMultiplierField_const_decode] at henergy
  have hfinite := (hS.2.2.2.1 ((C : ℝ) • u)).2.2 i
  calc
    ‖(coupledCircleMultiplierLinear hS a C ha u).val i‖ =
        circleNorm T γ i (S.decode (coupledCircleMultiplierLinear hS a C ha u)) :=
      hS.2.2.2.2.2.2.2 _ _
    _ = circleNorm T γ i (coupledCircleMultiplierField a (S.decode u)) := by
      rw [show S.decode (coupledCircleMultiplierLinear hS a C ha u) =
        coupledCircleMultiplierField a (S.decode u) from
          coupledCircleMultiplierValue_decode hS a C ha u]
    _ ≤ circleNorm T γ i (S.decode ((C : ℝ) • u)) :=
      Real.sqrt_le_sqrt (ENNReal.toReal_mono hfinite.ne henergy)
    _ = ‖((C : ℝ) • u).val i‖ := (hS.2.2.2.2.2.2.2 _ _).symm
    _ ≤ S.grading n ((C : ℝ) • u) :=
      ContinuousFlexibility.Analysis.norm_coordinate_le_graded _ _ hi _
    _ = C * S.grading n u := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg C.coe_nonneg]

theorem coupledCircleMultiplierLinear_isTame
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (a : ℕ → ℝ) (C : ℝ≥0)
    (ha : ∀ m, |a m| ≤ C) :
    ContinuousFlexibility.Analysis.IsTameLinear S.grading S.grading
      (coupledCircleMultiplierLinear hS a C ha) 0 0 := by
  intro n _
  exact ⟨C, fun u => by simpa only [Nat.add_zero] using
    coupledCircleMultiplierLinear_grading_le hS a C ha n u⟩

/-- The multiplier in the original projective topology. -/
def coupledCircleMultiplier
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (a : ℕ → ℝ) (C : ℝ≥0)
    (ha : ∀ m, |a m| ≤ C) : S.Space →L[ℝ] S.Space where
  toLinearMap := coupledCircleMultiplierLinear hS a C ha
  cont := ContinuousFlexibility.Analysis.continuous_projectiveLimit_of_tame
    (fun s => S.level s) S.bond (fun s => S.level s) S.bond
    (coupledCircleMultiplierLinear hS a C ha)
    (coupledCircleMultiplierLinear_isTame hS a C ha)

theorem coupledCircleMultiplier_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (a : ℕ → ℝ) (C : ℝ≥0)
    (ha : ∀ m, |a m| ≤ C) (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (coupledCircleMultiplier hS a C ha u) m θ = a m * S.decode u m θ :=
  coupledCircleMultiplierLinear_decode hS a C ha u m θ

end ContinuousFlexibility.Statements
