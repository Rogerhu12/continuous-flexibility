import ContinuousFlexibility.Analysis.N04PulledFieldsTransportPowerGrowth

/-!
# Common bases and budgets for transport powers

The low grading, high loss and parameter charge can be increased
independently. This combines finitely many primitive choices while
retaining the order of their quantifiers. A bounded height can also be
absorbed for the unweighted copy of the same transported field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

private theorem n04PulledFields_parameterPower_scale_mono
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {loss loss' shift shift' : ℕ} (hl : loss ≤ loss') (hs : shift ≤ shift')
    (N k d : ℕ) (x w : E) :
    (1 + p (N + loss) x + p (N + loss) w) ^
        (((d + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) ≤
      (1 + p (N + loss') x + p (N + loss') w) ^
        (((d + shift' * k : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
  have hindex : N + loss ≤ N + loss' := Nat.add_le_add_left hl N
  have hQ : 1 ≤ 1 + p (N + loss') x + p (N + loss') w := by
    linarith only [apply_nonneg (p (N + loss')) x, apply_nonneg (p (N + loss')) w]
  calc
    _ ≤ (1 + p (N + loss') x + p (N + loss') w) ^
        (((d + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) :=
      Real.rpow_le_rpow (by positivity)
        (add_le_add (add_le_add le_rfl (hp hindex x)) (hp hindex w)) (by positivity)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ
      (div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_right k hs) d) (by positivity))

theorem N04PulledFieldsMixedPowerGrowth.mono
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    (hp : Monotone p) (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ} {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K B loss shift B' loss' shift' : ℕ}
    (h : N04PulledFieldsMixedPowerGrowth p W F J K B loss shift)
    (hB : B ≤ B') (hl : loss ≤ loss') (hs : shift ≤ shift') :
    N04PulledFieldsMixedPowerGrowth p W F J K B' loss' shift' := by
  intro R hR N k hk a b hab
  obtain ⟨C, P, hC, hP, hb⟩ := h R hR N k hk a b hab
  refine ⟨C, P, hC, hP, fun i x hx hxB w hw y hy => ?_⟩
  exact (hb i x hx ((hp hB x).trans hxB) w ((hp hB w).trans hw) y hy).trans
    (mul_le_mul_of_nonneg_left (n04PulledFields_parameterPower_scale_mono hp hl hs N k (a + b) x w)
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)) (hF i)))

theorem N04PulledFieldsAngularPowerGrowth.mono
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    (hp : Monotone p) (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ} {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K B loss shift B' loss' shift' : ℕ}
    (h : N04PulledFieldsAngularPowerGrowth p W F J K B loss shift)
    (hB : B ≤ B') (hl : loss ≤ loss') (hs : shift ≤ shift') :
    N04PulledFieldsAngularPowerGrowth p W F J K B' loss' shift' := by
  intro R hR N k hk b hbN
  obtain ⟨C, P, hC, hP, hb⟩ := h R hR N k hk b hbN
  refine ⟨C, P, hC, hP, fun i x hx hxB w hw y hy => ?_⟩
  exact (hb i x hx ((hp hB x).trans hxB) w ((hp hB w).trans hw) y hy).trans
    (mul_le_mul_of_nonneg_left (n04PulledFields_parameterPower_scale_mono hp hl hs N k b x w)
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)) (hF i)))

theorem N04PulledFieldsAngularPowerGrowth.unweight
    {p : ℕ → Seminorm ℝ E} {W H : I → ℝ}
    (hW : ∀ i, 1 ≤ W i) {L : ℝ} (hL : 0 ≤ L) (hHL : ∀ i, H i ≤ L)
    {f : I → E × PolarPoint → ℝ} {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K B loss shift : ℕ}
    (h : N04PulledFieldsAngularPowerGrowth p W H J K B loss shift) :
    N04PulledFieldsAngularPowerGrowth p W (fun _ => 1) J K B loss shift := by
  intro R hR N k hk b hbN
  obtain ⟨C, P, hC, hP, hb⟩ := h R hR N k hk b hbN
  refine ⟨C * L, P, mul_nonneg hC hL, hP, fun i x hx hxB w hw y hy => ?_⟩
  have hcoef : C * W i ^ P * H i ≤ (C * L) * W i ^ P * 1 := by
    calc
      _ ≤ C * W i ^ P * L := mul_le_mul_of_nonneg_left (hHL i)
        (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans (hW i)) _))
      _ = _ := by ring
  exact (hb i x hx hxB w hw y hy).trans
    (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) _))

end ContinuousFlexibility.Analysis
