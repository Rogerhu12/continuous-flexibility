module

public import ContinuousFlexibility.Analysis.RootRescaledAngularControl
public import ContinuousFlexibility.Analysis.LinearWeightedCompositionJets

/-!
# Actual spatial jets of the rescaled root field

The two external parameters and the angle are differentiated, with time
held fixed. The coefficient argument is a linear contraction, and both
polynomial prefactors are linear functions with a uniformly bounded
value on the parameter box. The resulting estimate uses coefficient
jets only through the requested order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private def rootParameterProjection (side : Bool) : N04FlowPoint →L[ℝ] ℝ :=
  (if side then ContinuousLinearMap.snd ℝ ℝ ℝ else ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

private theorem rootParameterProjection_apply (side : Bool) (q : N04FlowPoint) :
    rootParameterProjection side q = if side then q.1.2 else q.1.1 := by
  cases side <;> simp only [rootParameterProjection, Bool.false_eq_true, if_false,
    if_true, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']

private theorem rootParameterProjection_norm (side : Bool) :
    ‖rootParameterProjection side‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  rw [rootParameterProjection_apply, one_mul]
  cases side with
  | false => exact (norm_fst_le q.1).trans (norm_fst_le q)
  | true => exact (norm_snd_le q.1).trans (norm_fst_le q)

private theorem rootParameterProjection_value (side : Bool)
    {q : N04FlowPoint} (hq : q.1 ∈ n04FlowParameterBox) :
    ‖rootParameterProjection side q‖ ≤ 1 := by
  rw [rootParameterProjection_apply, Real.norm_eq_abs]
  cases side with
  | false => exact abs_le.mpr hq.1
  | true => exact abs_le.mpr hq.2

private def rootArgumentLinear (a : ℝ) : N04FlowPoint →L[ℝ] PolarPoint :=
  (a • rootParameterProjection false).prod (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)

private theorem rootArgumentLinear_apply (a : ℝ) (q : N04FlowPoint) :
    rootArgumentLinear a q = (a * q.1.1, q.2) := by
  simp only [rootArgumentLinear, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, rootParameterProjection_apply,
    Bool.false_eq_true, if_false, ContinuousLinearMap.coe_snd', smul_eq_mul]

private theorem rootArgumentLinear_norm {a : ℝ} (ha : |a| ≤ 1) :
    ‖rootArgumentLinear a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  rw [rootArgumentLinear_apply, one_mul, Prod.norm_def, max_le_iff]
  refine ⟨?_, norm_snd_le q⟩
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ 1 * |q.1.1| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    _ ≤ ‖q‖ := by
      simpa only [one_mul, Real.norm_eq_abs] using
        (norm_fst_le q.1).trans (norm_fst_le q)

private theorem rootWeightedParameter_bounds
    (side : Bool) {a : ℝ} (ha : |a| ≤ 2)
    {q : N04FlowPoint} (hq : q.1 ∈ n04FlowParameterBox) :
    ‖a • rootParameterProjection side‖ ≤ 2 ∧
      ‖(a • rootParameterProjection side) q‖ ≤ 2 := by
  constructor
  · rw [norm_smul, Real.norm_eq_abs]
    simpa only [mul_one] using
      mul_le_mul ha (rootParameterProjection_norm side) (norm_nonneg _) (by norm_num)
  · rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs]
    simpa only [mul_one] using
      mul_le_mul ha (rootParameterProjection_value side hq) (norm_nonneg _) (by norm_num)

/-- The coefficient input is evaluated at the actual point x·t².
This is a same-order estimate; no high parameter derivative is included
in the separate angular Grönwall control. -/
theorem rootRescaledField_jet_le
    {d c : PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    {δ M : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hM : 0 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {q : N04FlowPoint} (hq : q.1 ∈ n04FlowParameterBox)
    (n : ℕ)
    (hdb : ∀ k : ℕ, k ≤ n →
      ‖iteratedFDeriv ℝ k d (δ * q.1.1 * t ^ 2, q.2)‖ ≤ M)
    (hcb : ∀ k : ℕ, k ≤ n →
      ‖iteratedFDeriv ℝ k c (δ * q.1.1 * t ^ 2, q.2)‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => rootRescaledField d c δ (t, y)) q‖ ≤
      (4 * linearWeightedCompositionJetConstant n) * M := by
  have ht2 : t ^ 2 ≤ 1 := by
    simpa only [pow_two, one_mul] using mul_le_mul ht.2 ht.2 ht.1 zero_le_one
  have hδt : δ * t ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hδone ht.2 ht.1 zero_le_one
  have hδt2 : δ * t ^ 2 ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hδone ht2 (sq_nonneg t) zero_le_one
  have ha : |δ * t ^ 2| ≤ 1 := by
    rwa [abs_of_nonneg (mul_nonneg hδ (sq_nonneg t))]
  have hl : |2 * δ * t| ≤ 2 := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδ) ht.1)]
    nlinarith only [hδt]
  have hr : |2 * δ * t ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδ) (sq_nonneg t))]
    nlinarith only [hδt2]
  let A := rootArgumentLinear (δ * t ^ 2)
  let l := (2 * δ * t) • rootParameterProjection false
  let r := (2 * δ * t ^ 2) • rootParameterProjection true
  have hA : ‖A‖ ≤ 1 := rootArgumentLinear_norm ha
  have hlb : ‖l‖ ≤ 2 ∧ ‖l q‖ ≤ 2 := rootWeightedParameter_bounds false hl hq
  have hrb : ‖r‖ ≤ 2 ∧ ‖r q‖ ≤ 2 := rootWeightedParameter_bounds true hr hq
  have hAx : A q = (δ * q.1.1 * t ^ 2, q.2) := by
    change rootArgumentLinear (δ * t ^ 2) q = (δ * q.1.1 * t ^ 2, q.2)
    rw [rootArgumentLinear_apply]
    congr 1
    ring
  have hdl := norm_iteratedFDeriv_linearWeightedComposition_le hd A l q
    (by norm_num : (0 : ℝ) ≤ 2) hM hA hlb.1 hlb.2 n
    (fun k hk => by rw [hAx]; exact hdb k hk)
  have hcr := norm_iteratedFDeriv_linearWeightedComposition_le hc A r q
    (by norm_num : (0 : ℝ) ≤ 2) hM hA hrb.1 hrb.2 n
    (fun k hk => by rw [hAx]; exact hcb k hk)
  have hD : ContDiff ℝ ∞ (fun y => l y * d (A y)) := l.contDiff.mul (hd.comp A.contDiff)
  have hC : ContDiff ℝ ∞ (fun y => r y * c (A y)) := r.contDiff.mul (hc.comp A.contDiff)
  have he : (fun y : N04FlowPoint => rootRescaledField d c δ (t, y)) =
      (fun y => l y * d (A y)) + (fun y => r y * c (A y)) := by
    funext y
    simp only [rootRescaledField, rootRegularizedField, Pi.add_apply,
      l, r, ContinuousLinearMap.smul_apply, smul_eq_mul,
      rootParameterProjection_apply, Bool.false_eq_true, if_false, if_true,
      A, rootArgumentLinear_apply]
    have hx : δ * y.1.1 * t ^ 2 = δ * t ^ 2 * y.1.1 := by ring
    rw [hx]
    ring
  rw [he, iteratedFDeriv_add_apply
    (hD.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (hC.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
  exact (norm_add_le _ _).trans ((add_le_add hdl hcr).trans_eq (by ring))

end ContinuousFlexibility.Analysis
