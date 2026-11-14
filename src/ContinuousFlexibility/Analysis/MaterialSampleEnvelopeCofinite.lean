module

public import ContinuousFlexibility.Analysis.MaterialSampleCofinite
public import ContinuousFlexibility.Analysis.MaterialCoordinate
public import ContinuousFlexibility.Analysis.ComponentConstantAbsorption

/-!
# Divergence of the actual material envelope along cell samples

Local finiteness makes the actual sample distances tend to zero. The exact
two-ended formulas in IsMaterialData identify their envelope with the
explicit material model, whose growth follows from a direct lower bound.
Thus the generic countable-constant absorption theorem applies to the
actual E0 samples.

No canonical component index is changed here, and no neighborhood,
fixed-loss estimate, or endpoint jet estimate is inferred.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace ContinuousFlexibility.Analysis

/-- A simple lower bound on the genuine material envelope at large
endpoint coordinate. -/
theorem le_materialE0_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    x ≤ materialE0 x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hlog : 1 ≤ materialLogFactor x := by
    unfold materialLogFactor
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.exp 1 + x) :=
        Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hx0)
  have hpow : x ≤ x ^ ((5 : ℝ) / 2) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 : ℝ) ≤ 5 / 2)
  have hmul : x ^ ((5 : ℝ) / 2) ≤
      x ^ ((5 : ℝ) / 2) * materialLogFactor x := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx0 ((5 : ℝ) / 2))
  have he : x ≤ materialE0Exponent x := by
    unfold materialE0Exponent
    exact (hpow.trans hmul).trans (le_add_of_nonneg_left zero_le_one)
  change x ≤ Real.exp (materialE0Exponent x)
  exact he.trans ((le_add_of_nonneg_right zero_le_one).trans
    (Real.add_one_le_exp (materialE0Exponent x)))

/-- The displayed material model really diverges, without an abstract
unbounded-envelope hypothesis. -/
theorem tendsto_materialE0_atTop : Tendsto materialE0 atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [eventually_ge_atTop (max (1 : ℝ) R)] with x hx
  exact ((le_max_right (1 : ℝ) R).trans hx).trans
    (le_materialE0_of_one_le ((le_max_left (1 : ℝ) R).trans hx))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

/-- The actual E0 values at the actual cell samples tend to infinity
along the cofinite filter, even when the samples alternate endpoints. -/
theorem materialSample_E0_tendsto_atTop
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    Tendsto (fun m => T.E0 (T.sample m)) cofinite atTop := by
  have hsample : ∀ m, T.sample m ∈ Ioo D.a D.b := by
    obtain ⟨_, hbounds⟩ := hRef
    exact materialSample_mem_radialCore hT hbounds.2.1
  have hdist := materialSample_endpointDistance_tendsto_zero hT hRef
  have hdistPos : Tendsto (fun m => endpointDistance D (T.sample m))
      cofinite (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hdist, Filter.Eventually.of_forall fun m => ?_⟩
    exact lt_min (sub_pos.mpr (hsample m).1) (sub_pos.mpr (hsample m).2)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨d0, δ, hd0, hδ, _, hleft, hright⟩, _⟩ := hT
  have hmodel : Tendsto (fun m =>
      Analysis.materialE0 (Analysis.endpointX d0 (endpointDistance D (T.sample m))))
      cofinite atTop :=
    (Analysis.tendsto_materialE0_atTop.comp
      (Analysis.tendsto_endpointX_atTop hd0)).comp hdistPos
  apply hmodel.congr'
  filter_upwards [hdist.eventually (Iio_mem_nhds hδ)] with m hm
  change Analysis.materialE0 (Analysis.endpointX d0 (endpointDistance D (T.sample m))) =
    T.E0 (T.sample m)
  unfold endpointDistance at hm ⊢
  by_cases hs : T.sample m - D.a ≤ D.b - T.sample m
  · rw [min_eq_left hs] at hm ⊢
    have hrl : T.sample m ∈ Ioo D.a (D.a + δ) :=
      ⟨(hsample m).1, by linarith only [hm]⟩
    obtain ⟨_, _, hE, _⟩ := hleft (T.sample m) hrl
    exact hE.symm
  · rw [min_eq_right (le_of_not_ge hs)] at hm ⊢
    have hrr : T.sample m ∈ Ioo (D.b - δ) D.b :=
      ⟨by linarith only [hm], (hsample m).2⟩
    obtain ⟨_, _, hE, _⟩ := hright (T.sample m) hrr
    exact hE.symm

/-- Already established countable component constants can be absorbed
in actual material sample weights. This theorem only selects indices. -/
theorem exists_materialSample_component_constant_absorption
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (A : ℕ → ℕ → ℝ) :
    ∃ κ : ℕ → ℕ, (∀ m, 1 ≤ T.E0 (T.sample (κ m))) ∧
      ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ m, A s m ≤ B * T.E0 (T.sample (κ m)) ^ B :=
  Analysis.exists_component_constant_absorption_of_tendsto
    (materialSample_E0_tendsto_atTop hT hRef) A

end ContinuousFlexibility.Statements
