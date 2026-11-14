module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.Compact

/-!
# The actual material weights and their envelopes

These are the functions of the nonnegative material endpoint variable in
§7, `eq:readable-physical-weights`. The exponents `5/2` and the powers of
positive weights below are real powers. Logarithmic asymptotics prove
eventual bounds; continuity on a compact initial interval makes the bounds
global for `x ≥ 0`.

No discrete profile comparison, weighted Sobolev estimate, or endpoint
coordinate identification is assumed or proved here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

def materialLogFactor (x : ℝ) : ℝ := Real.log (Real.exp 1 + x)

def materialE0Exponent (x : ℝ) : ℝ := 1 + x ^ ((5 : ℝ) / 2) * materialLogFactor x

def materialMExponent (x : ℝ) : ℝ := 1 + x ^ ((5 : ℝ) / 2) * materialLogFactor x ^ 2

def materialH (x : ℝ) : ℝ := Real.exp (-2 * x ^ 3 / 3)

def materialE0 (x : ℝ) : ℝ := Real.exp (materialE0Exponent x)

def materialM (x : ℝ) : ℝ := Real.exp (materialMExponent x)

theorem materialH_pos (x : ℝ) : 0 < materialH x := Real.exp_pos _

theorem materialE0_pos (x : ℝ) : 0 < materialE0 x := Real.exp_pos _

theorem materialM_pos (x : ℝ) : 0 < materialM x := Real.exp_pos _

theorem continuous_materialH : Continuous materialH := by
  have hc : Continuous (fun x : ℝ => -2 * x ^ 3 / 3) :=
    (continuous_const.mul (continuous_id.pow 3)).div_const 3
  exact hc.rexp

theorem continuousOn_materialLogFactor : ContinuousOn materialLogFactor (Ici 0) := by
  exact (continuous_const.add continuous_id).continuousOn.log
    (fun x hx => (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hx).ne')

theorem continuousOn_materialE0Exponent : ContinuousOn materialE0Exponent (Ici 0) := by
  exact continuousOn_const.add
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 2)).continuousOn.mul
      continuousOn_materialLogFactor)

theorem continuousOn_materialMExponent : ContinuousOn materialMExponent (Ici 0) := by
  exact continuousOn_const.add
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 2)).continuousOn.mul
      (continuousOn_materialLogFactor.pow 2))

theorem continuousOn_materialE0 : ContinuousOn materialE0 (Ici 0) :=
  continuousOn_materialE0Exponent.rexp

theorem continuousOn_materialM : ContinuousOn materialM (Ici 0) :=
  continuousOn_materialMExponent.rexp

private theorem tendsto_exp_one_add_atTop :
    Tendsto (fun x : ℝ => Real.exp 1 + x) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (B - Real.exp 1)] with x hx
  linarith

theorem tendsto_materialLogFactor_atTop : Tendsto materialLogFactor atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_exp_one_add_atTop

private theorem tendsto_shift_ratio :
    Tendsto (fun x : ℝ => (Real.exp 1 + x) / x) atTop (𝓝 1) := by
  have ht : Tendsto (fun x : ℝ => 1 + Real.exp 1 / x) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  have ht' : Tendsto (fun x : ℝ => 1 + Real.exp 1 / x) atTop (𝓝 1) := by simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp [hx.ne']
  ring

/-- The actual shifted logarithmic square grows more slowly than the
square root. This is the analytic reason the material exponent fits below
the cubic exponent of `H`. -/
theorem tendsto_materialLogFactor_sq_div_rpow :
    Tendsto (fun x : ℝ => materialLogFactor x ^ 2 / x ^ ((1 : ℝ) / 2))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun y : ℝ => Real.log y ^ 2 / y ^ ((1 : ℝ) / 2))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := (1 : ℝ) / 2)
        (by norm_num)).tendsto_div_nhds_zero
  have hshift := hlog.comp tendsto_exp_one_add_atTop
  have hratio := tendsto_shift_ratio.rpow_const (p := (1 : ℝ) / 2) (Or.inl one_ne_zero)
  have hprod : Tendsto
      (fun x : ℝ => (Real.log (Real.exp 1 + x) ^ 2 / (Real.exp 1 + x) ^ ((1 : ℝ) / 2)) *
        ((Real.exp 1 + x) / x) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.one_rpow, zero_mul] using hshift.mul hratio
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hy : 0 < Real.exp 1 + x := add_pos (Real.exp_pos 1) hx
  rw [Real.div_rpow hy.le hx.le]
  unfold materialLogFactor
  field_simp [(Real.rpow_pos_of_pos hy ((1 : ℝ) / 2)).ne',
    (Real.rpow_pos_of_pos hx ((1 : ℝ) / 2)).ne']

theorem tendsto_materialM_term_div_cube :
    Tendsto (fun x : ℝ => (x ^ ((5 : ℝ) / 2) * materialLogFactor x ^ 2) / x ^ 3)
      atTop (𝓝 0) := by
  apply tendsto_materialLogFactor_sq_div_rpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hp : x ^ ((5 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x ^ (3 : ℕ) := by
    rw [← Real.rpow_add hx]
    norm_num
  rw [← hp]
  field_simp [(Real.rpow_pos_of_pos hx ((5 : ℝ) / 2)).ne',
    (Real.rpow_pos_of_pos hx ((1 : ℝ) / 2)).ne']

private theorem exists_exp_bound_of_eventually_le {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0)) {K : ℝ} (htail : ∀ᶠ x : ℝ in atTop, f x ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → Real.exp (f x) ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (hf.mono (show Icc 0 (max 0 N) ⊆ Ici 0 from fun _ hx => hx.1))
  refine ⟨Real.exp (max K B), Real.exp_pos _, ?_⟩
  intro x hx
  apply Real.exp_le_exp.mpr
  by_cases hlarge : max 0 N ≤ x
  · exact (hN x ((le_max_right 0 N).trans hlarge)).trans (le_max_left K B)
  · exact (hB ⟨x, ⟨hx, (not_le.mp hlarge).le⟩, rfl⟩).trans (le_max_right K B)

theorem materialE0_rpow_div_materialM (A x : ℝ) :
    materialE0 x ^ A / materialM x =
      Real.exp (A * materialE0Exponent x - materialMExponent x) := by
  rw [materialE0, materialM, ← Real.exp_mul, ← Real.exp_sub]
  congr 1
  ring

/-- Any fixed real power of `E0` costs only one material weight order.
The constant covers the whole nonnegative material half-axis. -/
theorem materialE0_rpow_le_materialM (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → materialE0 x ^ A ≤ C * materialM x := by
  have htail : ∀ᶠ x : ℝ in atTop,
      A * materialE0Exponent x - materialMExponent x ≤ A - 1 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      tendsto_materialLogFactor_atTop.eventually_ge_atTop (max A 0)] with x hx hlog
    have hl0 : 0 ≤ materialLogFactor x := (le_max_right A 0).trans hlog
    have hlA : A ≤ materialLogFactor x := (le_max_left A 0).trans hlog
    have hquad : A * materialLogFactor x - materialLogFactor x ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg hl0 (sub_nonneg.mpr hlA)]
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (Real.rpow_nonneg hx ((5 : ℝ) / 2)) hquad
    unfold materialE0Exponent materialMExponent
    nlinarith only [hmul]
  obtain ⟨C, hC, hbound⟩ := exists_exp_bound_of_eventually_le
    ((continuousOn_const.mul continuousOn_materialE0Exponent).sub continuousOn_materialMExponent) htail
  refine ⟨C, hC, fun x hx => ?_⟩
  apply (div_le_iff₀ (materialM_pos x)).mp
  rw [materialE0_rpow_div_materialM]
  exact hbound x hx

theorem materialH_rpow_mul_materialM_rpow (A ε x : ℝ) :
    materialH x ^ ε * materialM x ^ A =
      Real.exp (ε * (-2 * x ^ 3 / 3) + A * materialMExponent x) := by
  rw [materialH, materialM, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- Every positive power of `H` absorbs every fixed real material weight
power. The estimate has one global constant, independent of `x ≥ 0`. -/
theorem materialH_rpow_mul_materialM_rpow_le (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → materialH x ^ ε * materialM x ^ A ≤ C := by
  have hsmall : Tendsto
      (fun x : ℝ => A * ((x ^ ((5 : ℝ) / 2) * materialLogFactor x ^ 2) / x ^ 3))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_materialM_term_div_cube.const_mul A
  have htail : ∀ᶠ x : ℝ in atTop,
      ε * (-2 * x ^ 3 / 3) + A * materialMExponent x ≤ A := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hsmall.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < 2 * ε / 3))] with x hx hsmallx
    have hb : A * (x ^ ((5 : ℝ) / 2) * materialLogFactor x ^ 2) < (2 * ε / 3) * x ^ 3 := by
      apply (div_lt_iff₀ (pow_pos hx 3)).mp
      simpa only [mul_div_assoc] using hsmallx
    unfold materialMExponent
    nlinarith only [hb.le]
  have hcont : ContinuousOn
      (fun x : ℝ => ε * (-2 * x ^ 3 / 3) + A * materialMExponent x) (Ici 0) :=
    (continuousOn_const.mul ((continuousOn_const.mul (continuousOn_id.pow 3)).div_const 3)).add
      (continuousOn_const.mul continuousOn_materialMExponent)
  obtain ⟨C, hC, hbound⟩ := exists_exp_bound_of_eventually_le hcont htail
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [materialH_rpow_mul_materialM_rpow]
  exact hbound x hx

theorem tendsto_materialH_zero : Tendsto materialH atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x ^ (3 : ℕ)) atTop atTop :=
    tendsto_pow_atTop (by decide)
  have hn := hp.const_mul_atTop_of_neg (by norm_num : (-2 / 3 : ℝ) < 0)
  convert Real.tendsto_exp_atBot.comp hn using 1
  funext x
  unfold materialH
  congr 1
  ring

/-- The absorption estimate yields actual vanishing, not just boundedness:
reserve half of the positive `H` exponent to tend to zero. -/
theorem tendsto_materialH_rpow_mul_materialM_rpow_zero (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => materialH x ^ ε * materialM x ^ A) atTop (𝓝 0) := by
  have hh : 0 < ε / 2 := by linarith
  obtain ⟨C, _, hC⟩ := materialH_rpow_mul_materialM_rpow_le A hh
  have hlim : Tendsto (fun x : ℝ => materialH x ^ (ε / 2) * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_materialH_zero.rpow_const_nhds_zero hh).mul_const C
  apply squeeze_zero'
    (Eventually.of_forall (fun x => mul_nonneg
      (Real.rpow_nonneg (materialH_pos x).le ε) (Real.rpow_nonneg (materialM_pos x).le A))) _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hsplit : materialH x ^ ε = materialH x ^ (ε / 2) * materialH x ^ (ε / 2) := by
    calc
      _ = materialH x ^ (ε / 2 + ε / 2) := by congr 1; ring
      _ = _ := Real.rpow_add (materialH_pos x) _ _
  calc
    _ = materialH x ^ (ε / 2) * (materialH x ^ (ε / 2) * materialM x ^ A) := by
      rw [hsplit]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hC x hx) (Real.rpow_nonneg (materialH_pos x).le _)

theorem materialH_rpow_mul_materialE0_rpow_le (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → materialH x ^ ε * materialE0 x ^ A ≤ C := by
  obtain ⟨CE, hCE, hE⟩ := materialE0_rpow_le_materialM A
  obtain ⟨CM, hCM, hM⟩ := materialH_rpow_mul_materialM_rpow_le (1 : ℝ) hε
  refine ⟨CE * CM, mul_pos hCE hCM, fun x hx => ?_⟩
  have hM' : materialH x ^ ε * materialM x ≤ CM := by
    simpa only [Real.rpow_one] using hM x hx
  calc
    _ ≤ materialH x ^ ε * (CE * materialM x) :=
      mul_le_mul_of_nonneg_left (hE x hx) (Real.rpow_nonneg (materialH_pos x).le _)
    _ = CE * (materialH x ^ ε * materialM x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hM' hCE.le

theorem tendsto_materialH_rpow_mul_materialE0_rpow_zero (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => materialH x ^ ε * materialE0 x ^ A) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := materialE0_rpow_le_materialM A
  have hlim : Tendsto (fun x : ℝ => C * (materialH x ^ ε * materialM x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_zero] using
      (tendsto_materialH_rpow_mul_materialM_rpow_zero (1 : ℝ) hε).const_mul C
  apply squeeze_zero'
    (Eventually.of_forall (fun x => mul_nonneg
      (Real.rpow_nonneg (materialH_pos x).le ε) (Real.rpow_nonneg (materialE0_pos x).le A))) _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  calc
    _ ≤ materialH x ^ ε * (C * materialM x) :=
      mul_le_mul_of_nonneg_left (hC x hx) (Real.rpow_nonneg (materialH_pos x).le _)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
