import ContinuousFlexibility.Analysis.MaterialSampleIndexModels
import ContinuousFlexibility.Analysis.MaterialShiftedEnvelope

/-!
# Uniform discrete envelopes at the actual material samples

The endpoint model at a sample uses an endpoint coordinate a bounded
distance from its reference-cell index.  Positive powers of the actual
sample height therefore absorb arbitrary discrete radial losses, while
negative powers admit a uniform cubic exponential bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

theorem materialH_natCast (n : ℕ) :
    materialH (n : ℝ) = radialH n := by
  unfold materialH radialH radialS
  congr 1
  ring

theorem radialE_rpow_eq_materialE0 (n : ℕ) (A : ℝ) :
    radialE n ^ A = Real.exp (-A) * materialE0 (n : ℝ) ^ A := by
  simp only [radialE, radialQ, materialE0, materialE0Exponent,
    materialLogFactor, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- The constant is uniform in the actual reference-cell sample. -/
theorem materialSample_H_radialE_envelope
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample m) ^ γ * radialE (D.cellIndex m) ^ A ≤
        K * radialH (D.cellIndex m) ^ (γ / 16) := by
  obtain ⟨d0, L, _, hL, hmodels⟩ := materialSample_eventually_endpoint_models hT hRef
  obtain ⟨K, _, hb⟩ := material_bounded_shift_envelope hγ A hL
  apply exists_pos_mul_bound_of_cofinite
    (fun m => Real.rpow_pos_of_pos (Real.exp_pos (-radialS (D.cellIndex m))) _)
    (K := Real.exp (-A) * K)
  filter_upwards [hmodels, cellIndex_eventually_ge_real hRef (2 * L)] with m hm hn
  dsimp only at hm
  have he := hb (D.cellIndex m)
    (endpointX d0 (endpointDistance D (T.sample m))) (D.cellIndex m)
    hn hm.2.2.2 (by simpa using hL) (Nat.cast_nonneg _)
  rw [hm.1, radialE_rpow_eq_materialE0]
  calc
    _ = Real.exp (-A) *
        (materialH (endpointX d0 (endpointDistance D (T.sample m))) ^ γ *
          materialE0 (D.cellIndex m : ℝ) ^ A) := by ring
    _ ≤ Real.exp (-A) * (K * materialH (D.cellIndex m : ℝ) ^ (γ / 16)) :=
      mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ = _ := by rw [materialH_natCast, radialH]; ring

/-- This coarse upper bound is sufficient when the sample height occurs
with a negative exponent in the control-curvature estimate. -/
theorem materialSample_H_neg_envelope
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧ ∀ m,
      T.H (T.sample m) ^ (-γ) ≤
        K * Real.exp (L * ((D.cellIndex m : ℝ) + 1) ^ 3) := by
  obtain ⟨d0, C, _, hC, hmodels⟩ := materialSample_eventually_endpoint_models hT hRef
  let L := (2 * γ / 3) * (C + 1) ^ 3
  have hL : 0 < L := mul_pos (by positivity) (pow_pos (by linarith) _)
  have heventual : ∀ᶠ m in cofinite,
      T.H (T.sample m) ^ (-γ) ≤
        (1 : ℝ) * Real.exp (L * ((D.cellIndex m : ℝ) + 1) ^ 3) := by
    filter_upwards [hmodels] with m hm
    dsimp only at hm
    let n : ℝ := D.cellIndex m
    let x := endpointX d0 (endpointDistance D (T.sample m))
    have hn : 0 ≤ n := Nat.cast_nonneg _
    have hx : 0 ≤ x := Real.sqrt_nonneg _
    have hxle : x ≤ (C + 1) * (n + 1) := by
      have hb := (abs_le.mp hm.2.2.2).2
      change x - n ≤ C at hb
      nlinarith only [hb, mul_nonneg hC hn]
    have hcube : x ^ 3 ≤ ((C + 1) * (n + 1)) ^ 3 :=
      pow_le_pow_left₀ hx hxle 3
    rw [hm.1, materialH, ← Real.exp_mul, one_mul]
    apply Real.exp_le_exp.mpr
    change (-2 * x ^ 3 / 3) * (-γ) ≤ L * (n + 1) ^ 3
    dsimp only [L]
    nlinarith only [mul_le_mul_of_nonneg_left hcube
      (by positivity : 0 ≤ 2 * γ / 3)]
  obtain ⟨K, hK, hb⟩ := exists_pos_mul_bound_of_cofinite
    (fun m => Real.exp_pos (L * ((D.cellIndex m : ℝ) + 1) ^ 3)) heventual
  exact ⟨K, L, hK, hL, hb⟩

/-- Material absorption holds at all samples, without any relation
between the sample index and a control's support interval. -/
theorem materialSample_H_E0_envelope
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A ≤ K := by
  have hdata := hT
  rcases hdata with ⟨_, hpos, _, _, _, _, _, _, _, _, _, hE, hM, _, _, _, _, _⟩
  obtain ⟨CE, hCE, he⟩ := hE A
  obtain ⟨CM, hCM, hm, _, _⟩ := hM (1 : ℝ) γ hγ
  obtain ⟨_, hb⟩ := hRef
  refine ⟨CE * CM, mul_pos hCE hCM, fun m => ?_⟩
  have hr := materialSample_mem_radialCore hT hb.2.1 m
  have hp : 0 < T.H (T.sample m) := (hpos _ hr).2.1
  have hm' : T.H (T.sample m) ^ γ * T.M (T.sample m) ≤ CM := by
    simpa only [Real.rpow_one] using hm _ hr
  calc
    _ ≤ T.H (T.sample m) ^ γ * (CE * T.M (T.sample m)) :=
      mul_le_mul_of_nonneg_left (he _ hr) (Real.rpow_pos_of_pos hp _).le
    _ = CE * (T.H (T.sample m) ^ γ * T.M (T.sample m)) := by ring
    _ ≤ CE * CM := mul_le_mul_of_nonneg_left hm' hCE.le

theorem materialSample_H_M_envelope
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample m) ^ γ * T.M (T.sample m) ^ A ≤ K := by
  have hdata := hT
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hM, _, _, _, _, _⟩
  obtain ⟨K, hK, hm, _, _⟩ := hM A γ hγ
  obtain ⟨_, hb⟩ := hRef
  exact ⟨K, hK, fun m => hm _ (materialSample_mem_radialCore hT hb.2.1 m)⟩

end ContinuousFlexibility.Statements
