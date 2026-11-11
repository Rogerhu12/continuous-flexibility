import ContinuousFlexibility.Analysis.MaterialSampleDiscreteEnvelope

/-!
# A linearly reindexed radial loss costs one material weight

The actual sample coordinate differs by a bounded amount from its cell
index.  Any fixed linear enlargement of that index changes the exponent
of the radial loss by at most a constant multiple.  The extra logarithm
in the material weight then absorbs every fixed radial power.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

theorem materialE0_rpow_scale_bound
    {C x y R : ℝ} (hC : 1 ≤ C) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : y ≤ C * x) (hR : 0 ≤ R) :
    materialE0 y ^ R ≤
      materialE0 x ^ (R * (C ^ (5 / 2 : ℝ) * (Real.log C + 1))) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hex : 0 < Real.exp 1 + x := add_pos_of_pos_of_nonneg (Real.exp_pos _) hx
  have hey : 0 < Real.exp 1 + y := add_pos_of_pos_of_nonneg (Real.exp_pos _) hy
  have hlogx : 1 ≤ materialLogFactor x := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + x by linarith only [hx])
    simpa only [Real.log_exp, materialLogFactor] using h
  have hlogy0 : 0 ≤ materialLogFactor y := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + y by linarith only [hy])
    rw [Real.log_exp] at h
    exact zero_le_one.trans h
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogxy : materialLogFactor y ≤
      (Real.log C + 1) * materialLogFactor x := by
    have he : Real.exp 1 + y ≤ C * (Real.exp 1 + x) := by
      have hc := mul_le_mul_of_nonneg_right hC (Real.exp_pos 1).le
      nlinarith only [hc, hxy]
    have hlog := Real.log_le_log hey he
    rw [Real.log_mul hC0.ne' hex.ne'] at hlog
    unfold materialLogFactor
    have hmul := mul_le_mul_of_nonneg_left hlogx hlogC
    unfold materialLogFactor at hmul
    nlinarith only [hlog, hmul]
  have hp := Real.rpow_le_rpow hy hxy (by norm_num : (0 : ℝ) ≤ 5 / 2)
  rw [Real.mul_rpow hC0.le hx] at hp
  have hpC : 0 ≤ C ^ (5 / 2 : ℝ) := Real.rpow_nonneg hC0.le _
  have hpX : 0 ≤ x ^ (5 / 2 : ℝ) := Real.rpow_nonneg hx _
  have hpC1 : 1 ≤ C ^ (5 / 2 : ℝ) := Real.one_le_rpow hC (by norm_num)
  let K := C ^ (5 / 2 : ℝ) * (Real.log C + 1)
  have hK1 : 1 ≤ K := by
    dsimp only [K]
    nlinarith only [hpC1, mul_nonneg hpC hlogC]
  have hq : y ^ (5 / 2 : ℝ) * materialLogFactor y ≤
      K * (x ^ (5 / 2 : ℝ) * materialLogFactor x) := by
    have hprod := mul_le_mul hp hlogxy hlogy0 (mul_nonneg hpC hpX)
    dsimp only [K]
    nlinarith only [hprod]
  have hE : materialE0Exponent y ≤ K * materialE0Exponent x := by
    dsimp only [materialE0Exponent]
    nlinarith only [hq, hK1]
  have hER := mul_le_mul_of_nonneg_left hE hR
  simp only [materialE0, ← Real.exp_mul, Real.exp_le_exp]
  dsimp only [K] at hER
  nlinarith only [hER]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

theorem radialE_rpow_le_materialE0_natCast
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    radialE n ^ R ≤ materialE0 (n : ℝ) ^ R := by
  simp only [radialE, radialQ, materialE0, materialE0Exponent,
    materialLogFactor, ← Real.exp_mul, Real.exp_le_exp]
  nlinarith only [hR]

/-- Every fixed radial power at a linearly controlled cell index is
bounded by one power of the actual material sample weight. -/
theorem materialSample_radialE_rpow_le_M_of_index_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {A R : ℝ} (hA : 0 < A) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ m n : ℕ,
      (n : ℝ) ≤ A * ((D.cellIndex m : ℝ) + 1) →
      radialE n ^ R ≤ K * T.M (T.sample m) := by
  obtain ⟨d0, C, _, hC, hmodels⟩ := materialSample_eventually_endpoint_models hT hRef
  let B := max (4 * A) 1
  have hB : 1 ≤ B := le_max_right _ _
  let P := R * (B ^ (5 / 2 : ℝ) * (Real.log B + 1))
  have hdata := hT
  rcases hdata with ⟨_, hpos, _, _, _, _, _, _, _, _, _, hE, _, _, _, _, _, _⟩
  obtain ⟨CE, _, he⟩ := hE P
  have hRef' := hRef
  obtain ⟨_, hgeom⟩ := hRef'
  have hsample (m : ℕ) : T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hgeom.2.1 m
  let F (m : ℕ) := materialE0 (A * ((D.cellIndex m : ℝ) + 1)) ^ R
  have heventual : ∀ᶠ m in cofinite, F m ≤ CE * T.M (T.sample m) := by
    filter_upwards [hmodels, cellIndex_eventually_ge_real hRef (max (2 * C) 1)] with m hm hn
    dsimp only at hm
    let x := endpointX d0 (endpointDistance D (T.sample m))
    let q : ℝ := D.cellIndex m
    have hx : 0 ≤ x := Real.sqrt_nonneg _
    have hqC : 2 * C ≤ q := (le_max_left _ _).trans hn
    have hq1 : 1 ≤ q := (le_max_right _ _).trans hn
    have hxl : q - C ≤ x := by
      have hh := (abs_le.mp hm.2.2.2).1
      change -C ≤ x - q at hh
      linarith only [hh]
    have hfour : q + 1 ≤ 4 * x := by linarith only [hxl, hqC, hq1]
    have hyx : A * (q + 1) ≤ B * x := by
      have h1 := mul_le_mul_of_nonneg_left hfour hA.le
      have h2 := mul_le_mul_of_nonneg_right (le_max_left (4 * A) 1) hx
      dsimp only [B]
      nlinarith only [h1, h2]
    have hy : 0 ≤ A * (q + 1) := mul_nonneg hA.le (by linarith only [hq1])
    have hscale := materialE0_rpow_scale_bound hB hx hy hyx hR
    have hmodel : T.E0 (T.sample m) = materialE0 x := hm.2.1
    change F m ≤ _
    calc
      F m ≤ materialE0 x ^ P := hscale
      _ = T.E0 (T.sample m) ^ P := by rw [hmodel]
      _ ≤ CE * T.M (T.sample m) := he _ (hsample m)
  obtain ⟨K, hK, hb⟩ := exists_pos_mul_bound_of_cofinite
    (fun m => zero_lt_one.trans_le (hpos _ (hsample m)).2.2.2) heventual
  refine ⟨K, hK, fun m n hnm => ?_⟩
  have hy : 0 ≤ A * ((D.cellIndex m : ℝ) + 1) :=
    mul_nonneg hA.le (by positivity)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hscale := materialE0_rpow_scale_bound (C := (1 : ℝ)) (by norm_num)
    hy hn (by simpa only [one_mul] using hnm) hR
  have hscale' : materialE0 (n : ℝ) ^ R ≤ F m := by
    simpa only [Real.one_rpow, Real.log_one, zero_add, mul_one] using hscale
  exact ((radialE_rpow_le_materialE0_natCast n hR).trans hscale').trans (hb m)

end ContinuousFlexibility.Statements
