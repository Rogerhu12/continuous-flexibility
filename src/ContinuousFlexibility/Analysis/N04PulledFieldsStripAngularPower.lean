import ContinuousFlexibility.Analysis.N04PulledFieldsCircleAngularPower
import ContinuousFlexibility.Analysis.N04PulledFieldsTransportPowerGrowth
import ContinuousFlexibility.Analysis.JointMixedCircleEvaluation

/-!
# Actual strip angular prefixes from fixed-base circle families

The circle estimates are uniform in a family of radius selectors.
Covering each physical strip identifies those estimates with the genuine
joint tower. The common low order precedes every parameter prefix.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {p : ℕ → Seminorm ℝ E}

/-- The actual angular parameter jets retain the sample-height factor.
No envelope power is needed, so the given envelope may be arbitrary. -/
theorem N04PulledFieldsFixedBaseFamily.realized_strip_angular_power
    {g : I → E → H.Space} (hg : N04PulledFieldsFixedBaseFamily p H.grading U g)
    (hp : Monotone p) (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m))
    (l h : ℕ → ℝ) (rsel : I → ℕ → ℝ)
    (hcover : ∀ m r, r ∈ Ioo (l m) (h m) → ∃ i, rsel i m = r)
    {f : ℕ → E × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (f m))
    (heq : ∀ i m, rsel i m ∈ Ioo (l m) (h m) → ∀ x ∈ U, ∀ θ,
      f m (x, (rsel i m, θ)) = H.decode (g i x) m θ)
    (W : ℕ → ℝ) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsAngularPowerGrowth p W (fun m => T.H (T.sample m) ^ γ)
        J K B highLoss shift := by
  let K₀ : ∀ i, SmoothDirections U (g i) := hg.choose
  obtain ⟨B, hB⟩ := hg.circle_diagonal_angular_power hp hIp hH hpos
  refine ⟨B, fun K => ?_⟩
  obtain ⟨highLoss, shift, hprefix⟩ := hB K
  refine ⟨highLoss, shift, fun R hR N k hk b hb => ?_⟩
  obtain ⟨C, hC, hc⟩ := hprefix R hR N k hk b hb
  refine ⟨C, 0, hC, le_rfl, fun m x hx hxlow w hwlow y hy => ?_⟩
  obtain ⟨i, hi⟩ := hcover m y.1 hy.1
  have hr : rsel i m ∈ Ioo (l m) (h m) := hi.symm ▸ hy.1
  have hid := jointMixedDiagonal_eq_circleAngularJet (J m) hH (K₀ i) m hr
    (heq i m hr) k b x w hx y.2
  have hyeta : (rsel i m, y.2) = y := Prod.ext hi rfl
  have hid' := (congrArg
    (fun q : PolarPoint => jointMixedDiagonal (J m) k 0 b x w q) hyeta).symm.trans hid
  have hpoint := hc i (K₀ i) x hx w hxlow hwlow m y.2
  simpa only [Real.rpow_zero, mul_one] using (congrArg abs hid').trans_le hpoint

/-- A fixed scalar offset contributes only to the zeroth jet. A uniform
bound on the sample height absorbs that term and the circle weight into
the numerical coefficient, leaving the same low order and power budget. -/
theorem N04PulledFieldsFixedBaseFamily.realized_strip_angular_power_add_const
    {g : I → E → H.Space} (hg : N04PulledFieldsFixedBaseFamily p H.grading U g)
    (hp : Monotone p) (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m)) (KH : ℝ) (hKH : 0 ≤ KH)
    (hheight : ∀ m, T.H (T.sample m) ^ γ ≤ KH)
    (l h : ℕ → ℝ) (rsel : I → ℕ → ℝ)
    (hcover : ∀ m r, r ∈ Ioo (l m) (h m) → ∃ i, rsel i m = r)
    {f : ℕ → E × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (f m))
    (c : ℝ)
    (heq : ∀ i m, rsel i m ∈ Ioo (l m) (h m) → ∀ x ∈ U, ∀ θ,
      f m (x, (rsel i m, θ)) = c + H.decode (g i x) m θ)
    (W : ℕ → ℝ) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsAngularPowerGrowth p W (fun _ => 1) J K B highLoss shift := by
  let K₀ : ∀ i, SmoothDirections U (g i) := hg.choose
  obtain ⟨B, hB⟩ := hg.circle_diagonal_angular_power hp hIp hH hpos
  refine ⟨B, fun K => ?_⟩
  obtain ⟨highLoss, shift, hprefix⟩ := hB K
  refine ⟨highLoss, shift, fun R hR N k hk b hb => ?_⟩
  obtain ⟨C, hC, hc⟩ := hprefix R hR N k hk b hb
  refine ⟨|c| + C * KH, 0, add_nonneg (abs_nonneg _) (mul_nonneg hC hKH),
    le_rfl, fun m x hx hxlow w hwlow y hy => ?_⟩
  obtain ⟨i, hi⟩ := hcover m y.1 hy.1
  have hr : rsel i m ∈ Ioo (l m) (h m) := hi.symm ▸ hy.1
  have hid := jointMixedDiagonal_eq_circleAngularJet_add_const (J m) hH (K₀ i) m hr c
    (heq i m hr) k b x w hx y.2
  have hyeta : (rsel i m, y.2) = y := Prod.ext hi rfl
  have hid' := (congrArg
    (fun q : PolarPoint => jointMixedDiagonal (J m) k 0 b x w q) hyeta).symm.trans hid
  let Q : ℝ := (1 + p (N + highLoss) x + p (N + highLoss) w) ^
    (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1))
  have hQ : 1 ≤ Q := by
    apply Real.one_le_rpow
    · linarith only [apply_nonneg (p (N + highLoss)) x,
        apply_nonneg (p (N + highLoss)) w]
    · positivity
  have hc0 : |(if k = 0 ∧ b = 0 then c else 0)| ≤ |c| := by
    split_ifs <;> simp only [abs_zero, abs_nonneg, le_refl]
  have hpoint := hc i (K₀ i) x hx w hxlow hwlow m y.2
  have hbound : |jointMixedDiagonal (J m) k 0 b x w y| ≤ (|c| + C * KH) * Q := by
    calc
      _ ≤ |(if k = 0 ∧ b = 0 then c else 0)| +
          |iteratedDeriv b (H.decode ((K₀ i).D k x (fun _ => w)) m) y.2| :=
        (congrArg abs hid').trans_le (abs_add_le _ _)
      _ ≤ |c| * Q + (C * KH) * Q := add_le_add
        (hc0.trans (by nlinarith only [hQ, abs_nonneg c]))
        (hpoint.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hheight m) hC) (zero_le_one.trans hQ)))
      _ = _ := by ring
  simpa only [Real.rpow_zero, mul_one, Q] using hbound

end ContinuousFlexibility.Analysis
