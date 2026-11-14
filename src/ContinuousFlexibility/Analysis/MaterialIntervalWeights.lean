module

public import ContinuousFlexibility.Analysis.MaterialInterval
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Actual material weights on the whole open unit interval

The same fixed smooth transition as the material scale interpolates the
logarithms of the two actual endpoint weights. The resulting positive
weights are smooth on `(0,1)` and agree exactly with the endpoint models
on the two collars. Logarithmic convexity preserves the proved uniform
envelopes, and the physical endpoint limits are actual one-sided limits.

These are explicit reference weights. Their comparison with the
manuscript's discrete profile and all higher-order coordinate estimates
remain separate obligations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def materialIntervalLogBlend (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 - materialIntervalTransition t) * f (materialIntervalXL t) +
    materialIntervalTransition t * f (materialIntervalXR t)

def materialIntervalLogH (t : ℝ) : ℝ := materialIntervalLogBlend (fun x => Real.log (materialH x)) t

def materialIntervalLogE0 (t : ℝ) : ℝ := materialIntervalLogBlend (fun x => Real.log (materialE0 x)) t

def materialIntervalLogM (t : ℝ) : ℝ := materialIntervalLogBlend (fun x => Real.log (materialM x)) t

def materialIntervalH (t : ℝ) : ℝ := Real.exp (materialIntervalLogH t)

def materialIntervalE0 (t : ℝ) : ℝ := Real.exp (materialIntervalLogE0 t)

def materialIntervalM (t : ℝ) : ℝ := Real.exp (materialIntervalLogM t)

theorem materialIntervalH_pos (t : ℝ) : 0 < materialIntervalH t := Real.exp_pos _

theorem materialIntervalE0_pos (t : ℝ) : 0 < materialIntervalE0 t := Real.exp_pos _

theorem materialIntervalM_pos (t : ℝ) : 0 < materialIntervalM t := Real.exp_pos _

theorem materialIntervalLogBlend_eq_left (f : ℝ → ℝ) {t : ℝ} (ht : t ≤ 1 / 3) :
    materialIntervalLogBlend f t = f (materialIntervalXL t) := by
  simp [materialIntervalLogBlend, materialIntervalTransition_eq_zero ht]

theorem materialIntervalLogBlend_eq_right (f : ℝ → ℝ) {t : ℝ} (ht : 2 / 3 ≤ t) :
    materialIntervalLogBlend f t = f (materialIntervalXR t) := by
  simp [materialIntervalLogBlend, materialIntervalTransition_eq_one ht]

theorem materialIntervalH_eq_left {t : ℝ} (ht : t ≤ 1 / 3) :
    materialIntervalH t = materialH (materialIntervalXL t) := by
  rw [materialIntervalH, materialIntervalLogH, materialIntervalLogBlend_eq_left _ ht,
    Real.exp_log (materialH_pos _)]

theorem materialIntervalH_eq_right {t : ℝ} (ht : 2 / 3 ≤ t) :
    materialIntervalH t = materialH (materialIntervalXR t) := by
  rw [materialIntervalH, materialIntervalLogH, materialIntervalLogBlend_eq_right _ ht,
    Real.exp_log (materialH_pos _)]

theorem materialIntervalE0_eq_left {t : ℝ} (ht : t ≤ 1 / 3) :
    materialIntervalE0 t = materialE0 (materialIntervalXL t) := by
  rw [materialIntervalE0, materialIntervalLogE0, materialIntervalLogBlend_eq_left _ ht,
    Real.exp_log (materialE0_pos _)]

theorem materialIntervalE0_eq_right {t : ℝ} (ht : 2 / 3 ≤ t) :
    materialIntervalE0 t = materialE0 (materialIntervalXR t) := by
  rw [materialIntervalE0, materialIntervalLogE0, materialIntervalLogBlend_eq_right _ ht,
    Real.exp_log (materialE0_pos _)]

theorem materialIntervalM_eq_left {t : ℝ} (ht : t ≤ 1 / 3) :
    materialIntervalM t = materialM (materialIntervalXL t) := by
  rw [materialIntervalM, materialIntervalLogM, materialIntervalLogBlend_eq_left _ ht,
    Real.exp_log (materialM_pos _)]

theorem materialIntervalM_eq_right {t : ℝ} (ht : 2 / 3 ≤ t) :
    materialIntervalM t = materialM (materialIntervalXR t) := by
  rw [materialIntervalM, materialIntervalLogM, materialIntervalLogBlend_eq_right _ ht,
    Real.exp_log (materialM_pos _)]

theorem contDiffAt_materialIntervalLogBlend {f : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hL : ContDiffAt ℝ ∞ f (materialIntervalXL t))
    (hR : ContDiffAt ℝ ∞ f (materialIntervalXR t)) :
    ContDiffAt ℝ ∞ (materialIntervalLogBlend f) t :=
  ((contDiffAt_const.sub contDiff_materialIntervalTransition.contDiffAt).mul
    (hL.comp t (contDiffAt_materialIntervalXL ht))).add
      (contDiff_materialIntervalTransition.contDiffAt.mul
        (hR.comp t (contDiffAt_materialIntervalXR ht)))

theorem contDiff_log_materialH : ContDiff ℝ ∞ (fun x => Real.log (materialH x)) := by
  have heq : (fun x => Real.log (materialH x)) = (fun x : ℝ => -2 * x ^ 3 / 3) := by
    funext x
    simp [materialH]
  rw [heq]
  exact (contDiff_const.mul (contDiff_id.pow 3)).div_const 3

theorem contDiffAt_log_materialE0 {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (fun y => Real.log (materialE0 y)) x := by
  have heq : (fun y => Real.log (materialE0 y)) = materialE0Exponent := by
    funext y
    exact Real.log_exp _
  rw [heq]
  exact contDiffAt_const.add
    ((contDiffAt_id.rpow_const_of_ne hx.ne').mul
      ((contDiffAt_const.add contDiffAt_id).log (add_pos (Real.exp_pos 1) hx).ne'))

theorem contDiffAt_log_materialM {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (fun y => Real.log (materialM y)) x := by
  have heq : (fun y => Real.log (materialM y)) = materialMExponent := by
    funext y
    exact Real.log_exp _
  rw [heq]
  exact contDiffAt_const.add
    ((contDiffAt_id.rpow_const_of_ne hx.ne').mul
      (((contDiffAt_const.add contDiffAt_id).log (add_pos (Real.exp_pos 1) hx).ne').pow 2))

theorem contDiffAt_materialIntervalH {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ materialIntervalH t :=
  (contDiffAt_materialIntervalLogBlend ht contDiff_log_materialH.contDiffAt
    contDiff_log_materialH.contDiffAt).exp

theorem contDiffAt_materialIntervalE0 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ materialIntervalE0 t :=
  (contDiffAt_materialIntervalLogBlend ht (contDiffAt_log_materialE0 (materialIntervalXL_pos ht))
    (contDiffAt_log_materialE0 (materialIntervalXR_pos ht))).exp

theorem contDiffAt_materialIntervalM {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ materialIntervalM t :=
  (contDiffAt_materialIntervalLogBlend ht (contDiffAt_log_materialM (materialIntervalXL_pos ht))
    (contDiffAt_log_materialM (materialIntervalXR_pos ht))).exp

theorem contDiffOn_materialIntervalH : ContDiffOn ℝ ∞ materialIntervalH (Ioo (0 : ℝ) 1) :=
  fun _ ht => (contDiffAt_materialIntervalH ht).contDiffWithinAt

theorem contDiffOn_materialIntervalE0 : ContDiffOn ℝ ∞ materialIntervalE0 (Ioo (0 : ℝ) 1) :=
  fun _ ht => (contDiffAt_materialIntervalE0 ht).contDiffWithinAt

theorem contDiffOn_materialIntervalM : ContDiffOn ℝ ∞ materialIntervalM (Ioo (0 : ℝ) 1) :=
  fun _ ht => (contDiffAt_materialIntervalM ht).contDiffWithinAt

/-- Both endpoint variables are nonnegative even for the totalized real
functions, so the logarithmic envelope holds for every real `t`. -/
theorem materialIntervalLogBlend_le {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x : ℝ, 0 ≤ x → f x ≤ C) (t : ℝ) : materialIntervalLogBlend f t ≤ C := by
  have hL := hf (materialIntervalXL t) (Real.sqrt_nonneg _)
  have hR := hf (materialIntervalXR t) (Real.sqrt_nonneg _)
  have hη := materialIntervalTransition_nonneg t
  have hη' := sub_nonneg.mpr (materialIntervalTransition_le_one t)
  calc
    materialIntervalLogBlend f t ≤ (1 - materialIntervalTransition t) * C +
        materialIntervalTransition t * C := add_le_add
      (mul_le_mul_of_nonneg_left hL hη') (mul_le_mul_of_nonneg_left hR hη)
    _ = C := by ring

theorem materialIntervalE0_rpow_le_M (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, materialIntervalE0 t ^ A ≤ C * materialIntervalM t := by
  obtain ⟨C, hC, hbound⟩ := materialE0_rpow_le_materialM A
  have hb : ∀ x : ℝ, 0 ≤ x → A * Real.log (materialE0 x) - Real.log (materialM x) ≤ Real.log C := by
    intro x hx
    have h := Real.log_le_log (Real.rpow_pos_of_pos (materialE0_pos x) A) (hbound x hx)
    rw [Real.log_rpow (materialE0_pos x), Real.log_mul hC.ne' (materialM_pos x).ne'] at h
    linarith
  refine ⟨C, hC, fun t => ?_⟩
  have h := materialIntervalLogBlend_le hb t
  have hl : A * materialIntervalLogE0 t - materialIntervalLogM t ≤ Real.log C := by
    convert h using 1
    unfold materialIntervalLogE0 materialIntervalLogM materialIntervalLogBlend
    ring
  calc
    materialIntervalE0 t ^ A = Real.exp (A * materialIntervalLogE0 t) := by
      rw [materialIntervalE0, ← Real.exp_mul]
      congr 1
      ring
    _ ≤ Real.exp (Real.log C + materialIntervalLogM t) := Real.exp_le_exp.mpr (by linarith)
    _ = C * materialIntervalM t := by rw [Real.exp_add, Real.exp_log hC]; rfl

private theorem interval_envelope_of_endpoint {A ε : ℝ} {C : ℝ} (hC : 0 < C)
    (hb : ∀ x : ℝ, 0 ≤ x → materialH x ^ ε * materialM x ^ A ≤ C) (t : ℝ) :
    materialIntervalH t ^ ε * materialIntervalM t ^ A ≤ C := by
  have hlog : ∀ x : ℝ, 0 ≤ x →
      ε * Real.log (materialH x) + A * Real.log (materialM x) ≤ Real.log C := by
    intro x hx
    have h := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos (materialH_pos x) ε)
      (Real.rpow_pos_of_pos (materialM_pos x) A)) (hb x hx)
    rw [Real.log_mul (Real.rpow_pos_of_pos (materialH_pos x) ε).ne'
      (Real.rpow_pos_of_pos (materialM_pos x) A).ne', Real.log_rpow (materialH_pos x),
      Real.log_rpow (materialM_pos x)] at h
    exact h
  have h := materialIntervalLogBlend_le hlog t
  have hl : ε * materialIntervalLogH t + A * materialIntervalLogM t ≤ Real.log C := by
    convert h using 1
    unfold materialIntervalLogH materialIntervalLogM materialIntervalLogBlend
    ring
  calc
    materialIntervalH t ^ ε * materialIntervalM t ^ A =
        Real.exp (ε * materialIntervalLogH t + A * materialIntervalLogM t) := by
      rw [materialIntervalH, materialIntervalM, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log C) := Real.exp_le_exp.mpr hl
    _ = C := Real.exp_log hC

theorem materialIntervalH_rpow_mul_M_rpow_le (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, materialIntervalH t ^ ε * materialIntervalM t ^ A ≤ C := by
  obtain ⟨C, hC, hb⟩ := materialH_rpow_mul_materialM_rpow_le A hε
  exact ⟨C, hC, interval_envelope_of_endpoint hC hb⟩

theorem materialIntervalH_rpow_mul_E0_rpow_le (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, materialIntervalH t ^ ε * materialIntervalE0 t ^ A ≤ C := by
  obtain ⟨C, hC, hb⟩ := materialH_rpow_mul_materialE0_rpow_le A hε
  have hlog : ∀ x : ℝ, 0 ≤ x →
      ε * Real.log (materialH x) + A * Real.log (materialE0 x) ≤ Real.log C := by
    intro x hx
    have h := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos (materialH_pos x) ε)
      (Real.rpow_pos_of_pos (materialE0_pos x) A)) (hb x hx)
    rw [Real.log_mul (Real.rpow_pos_of_pos (materialH_pos x) ε).ne'
      (Real.rpow_pos_of_pos (materialE0_pos x) A).ne', Real.log_rpow (materialH_pos x),
      Real.log_rpow (materialE0_pos x)] at h
    exact h
  refine ⟨C, hC, fun t => ?_⟩
  have h := materialIntervalLogBlend_le hlog t
  have hl : ε * materialIntervalLogH t + A * materialIntervalLogE0 t ≤ Real.log C := by
    convert h using 1
    unfold materialIntervalLogH materialIntervalLogE0 materialIntervalLogBlend
    ring
  calc
    materialIntervalH t ^ ε * materialIntervalE0 t ^ A =
        Real.exp (ε * materialIntervalLogH t + A * materialIntervalLogE0 t) := by
      rw [materialIntervalH, materialIntervalE0, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log C) := Real.exp_le_exp.mpr hl
    _ = C := Real.exp_log hC

private theorem eventually_materialInterval_left : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ≤ 1 / 3 :=
  (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 3)).filter_mono nhdsWithin_le_nhds

private theorem eventually_materialInterval_right : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), 2 / 3 ≤ t :=
  (eventually_ge_nhds (by norm_num : (2 / 3 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds

theorem tendsto_materialIntervalH_rpow_mul_M_left (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t : ℝ => materialIntervalH t ^ ε * materialIntervalM t ^ A)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (tendsto_endpoint_H_rpow_M_rpow_zero (by norm_num : (0 : ℝ) < 1) A hε).congr'
  filter_upwards [eventually_materialInterval_left] with t ht
  rw [materialIntervalH_eq_left ht, materialIntervalM_eq_left ht]
  rfl

theorem tendsto_materialIntervalH_rpow_mul_M_right (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t : ℝ => materialIntervalH t ^ ε * materialIntervalM t ^ A)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  apply ((tendsto_endpoint_H_rpow_M_rpow_zero (by norm_num : (0 : ℝ) < 1) A hε).comp
    tendsto_reflectedDistance_zero).congr'
  filter_upwards [eventually_materialInterval_right] with t ht
  rw [materialIntervalH_eq_right ht, materialIntervalM_eq_right ht]
  rfl

theorem tendsto_materialIntervalH_rpow_mul_E0_left (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t : ℝ => materialIntervalH t ^ ε * materialIntervalE0 t ^ A)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (tendsto_endpoint_H_rpow_E0_rpow_zero (by norm_num : (0 : ℝ) < 1) A hε).congr'
  filter_upwards [eventually_materialInterval_left] with t ht
  rw [materialIntervalH_eq_left ht, materialIntervalE0_eq_left ht]
  rfl

theorem tendsto_materialIntervalH_rpow_mul_E0_right (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t : ℝ => materialIntervalH t ^ ε * materialIntervalE0 t ^ A)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  apply ((tendsto_endpoint_H_rpow_E0_rpow_zero (by norm_num : (0 : ℝ) < 1) A hε).comp
    tendsto_reflectedDistance_zero).congr'
  filter_upwards [eventually_materialInterval_right] with t ht
  rw [materialIntervalH_eq_right ht, materialIntervalE0_eq_right ht]
  rfl

theorem tendsto_materialIntervalH_left : Tendsto materialIntervalH (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa using tendsto_materialIntervalH_rpow_mul_M_left 0 (by norm_num : (0 : ℝ) < 1)

theorem tendsto_materialIntervalH_right : Tendsto materialIntervalH (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  simpa using tendsto_materialIntervalH_rpow_mul_M_right 0 (by norm_num : (0 : ℝ) < 1)

end ContinuousFlexibility.Analysis
