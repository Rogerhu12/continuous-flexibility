import ContinuousFlexibility.Analysis.MaterialWeights

/-!
# Material powers under a scale close to one

The material exponent has an explicit scale coefficient tending to one
as the scale tends to one. Consequently every fixed power can be
transferred across a bounded coordinate displacement at the cost of any
prescribed positive extra material order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

def materialMScale (C : ℝ) : ℝ :=
  C ^ (5 / 2 : ℝ) * (Real.log C + 1) ^ 2

theorem materialM_one_le {x : ℝ} (hx : 0 ≤ x) : 1 ≤ materialM x := by
  apply Real.one_le_exp_iff.mpr
  have hterm : 0 ≤ x ^ (5 / 2 : ℝ) * materialLogFactor x ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _)
  change 0 ≤ 1 + x ^ (5 / 2 : ℝ) * materialLogFactor x ^ 2
  linarith only [hterm]

theorem materialM_rpow_scale_bound
    {C x y p : ℝ} (hC : 1 ≤ C) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : y ≤ C * x) (hp : 0 ≤ p) :
    materialM y ^ p ≤ materialM x ^ (p * materialMScale C) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hex : 0 < Real.exp 1 + x := add_pos_of_pos_of_nonneg (Real.exp_pos _) hx
  have hey : 0 < Real.exp 1 + y := add_pos_of_pos_of_nonneg (Real.exp_pos _) hy
  have hlogx : 1 ≤ materialLogFactor x := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + x by linarith only [hx])
    simpa only [Real.log_exp, materialLogFactor] using h
  have hlogy : 0 ≤ materialLogFactor y := by
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
    have hmul := mul_le_mul_of_nonneg_left hlogx hlogC
    unfold materialLogFactor at hmul ⊢
    nlinarith only [hlog, hmul]
  have hrpow := Real.rpow_le_rpow hy hxy (by norm_num : (0 : ℝ) ≤ 5 / 2)
  rw [Real.mul_rpow hC0.le hx] at hrpow
  have hlogsq := pow_le_pow_left₀ hlogy hlogxy 2
  have hpC : 0 ≤ C ^ (5 / 2 : ℝ) := Real.rpow_nonneg hC0.le _
  have hpX : 0 ≤ x ^ (5 / 2 : ℝ) := Real.rpow_nonneg hx _
  have hpC1 : 1 ≤ C ^ (5 / 2 : ℝ) := Real.one_le_rpow hC (by norm_num)
  have hlogsq1 : 1 ≤ (Real.log C + 1) ^ 2 := by nlinarith only [hlogC, sq_nonneg (Real.log C)]
  have hscale1 : 1 ≤ materialMScale C := by
    exact (one_mul 1).symm.trans_le
      (mul_le_mul hpC1 hlogsq1 (by norm_num) hpC)
  have hterm : y ^ (5 / 2 : ℝ) * materialLogFactor y ^ 2 ≤
      materialMScale C * (x ^ (5 / 2 : ℝ) * materialLogFactor x ^ 2) := by
    have hb := mul_le_mul hrpow hlogsq (sq_nonneg _) (mul_nonneg hpC hpX)
    dsimp only [materialMScale]
    nlinarith only [hb]
  have hE : materialMExponent y ≤ materialMScale C * materialMExponent x := by
    dsimp only [materialMExponent]
    nlinarith only [hterm, hscale1]
  have hEp := mul_le_mul_of_nonneg_left hE hp
  simp only [materialM, ← Real.exp_mul, Real.exp_le_exp]
  nlinarith only [hEp]

theorem monotoneOn_materialM : MonotoneOn materialM (Ici 0) := by
  intro x hx y hy hxy
  have h := materialM_rpow_scale_bound (C := (1 : ℝ)) (p := (1 : ℝ))
    (by norm_num) hy hx (by simpa only [one_mul] using hxy) (by norm_num)
  simpa only [materialMScale, Real.one_rpow, Real.log_one, zero_add,
    one_pow, one_mul, Real.rpow_one] using h

theorem exists_materialM_scale_for_extra_order
    {p σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 < C ∧ p * materialMScale C ≤ p + σ := by
  have hpower : ContinuousAt (fun C : ℝ => C ^ (5 / 2 : ℝ)) 1 :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 2)).continuousAt
  have hlog : ContinuousAt (fun C : ℝ => (Real.log C + 1) ^ 2) 1 :=
    ((Real.continuousAt_log one_ne_zero).add continuousAt_const).pow 2
  have hc : ContinuousAt (fun C : ℝ => p * materialMScale C) 1 :=
    continuousAt_const.mul (hpower.mul hlog)
  have hn : ∀ᶠ C : ℝ in 𝓝 1, p * materialMScale C < p + σ :=
    hc.eventually (Iio_mem_nhds (by
      simp only [materialMScale, Real.one_rpow, Real.log_one, zero_add,
        one_pow, mul_one]
      linarith only [hσ]))
  have hh : ∀ᶠ C : ℝ in 𝓝[>] 1, 1 < C ∧ p * materialMScale C < p + σ := by
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with C hC hgt
    exact ⟨hgt, hC⟩
  obtain ⟨C, hC, hp⟩ := hh.exists
  exact ⟨C, hC, hp.le⟩

theorem materialM_rpow_le_of_scale_or_bound
    {p σ C R x y : ℝ} (hp : 0 ≤ p) (hσ : 0 < σ) (hC : 1 ≤ C)
    (hscale : p * materialMScale C ≤ p + σ) (hR : 0 ≤ R)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ C * y ∨ x ≤ R) :
    materialM x ^ p ≤ materialM R ^ p * materialM y ^ (p + σ) := by
  have hMR : 1 ≤ materialM R ^ p := Real.one_le_rpow (materialM_one_le hR) hp
  have hMY : 1 ≤ materialM y ^ (p + σ) :=
    Real.one_le_rpow (materialM_one_le hy) (add_nonneg hp hσ.le)
  rcases hxy with hxy | hxR
  · have hxyM := materialM_rpow_scale_bound hC hy hx hxy hp
    have horder := Real.rpow_le_rpow_of_exponent_le (materialM_one_le hy) hscale
    exact (hxyM.trans horder).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hMR (Real.rpow_nonneg (materialM_pos y).le _))
  · have hxyM := Real.rpow_le_rpow (materialM_pos x).le
      (monotoneOn_materialM hx hR hxR) hp
    exact hxyM.trans (by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hMY (Real.rpow_nonneg (materialM_pos R).le _))

/-- A bounded coordinate displacement costs an arbitrarily small fixed
positive extra material order; the constant may depend on the input order. -/
theorem materialM_rpow_oneSided_shift
    {p σ L : ℝ} (hp : 0 ≤ p) (hσ : 0 < σ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ y + L →
      materialM x ^ p ≤ K * materialM y ^ (p + σ) := by
  obtain ⟨C, hC, hscale⟩ := exists_materialM_scale_for_extra_order (p := p) hσ
  let R := L / (C - 1) + L
  have hR : 0 ≤ R := add_nonneg (div_nonneg hL (sub_pos.mpr hC).le) hL
  refine ⟨materialM R ^ p, Real.rpow_pos_of_pos (materialM_pos R) _, fun x y hx hy hxyL => ?_⟩
  apply materialM_rpow_le_of_scale_or_bound hp hσ hC.le hscale hR hx hy
  by_cases hxy : x ≤ C * y
  · exact Or.inl hxy
  · right
    have hyx : C * y ≤ x := (lt_of_not_ge hxy).le
    have hyL : y ≤ L / (C - 1) := by
      apply (le_div_iff₀ (sub_pos.mpr hC)).mpr
      nlinarith only [hyx, hxyL]
    exact hxyL.trans (add_le_add hyL le_rfl)

theorem materialM_rpow_bounded_shift
    {p σ L : ℝ} (hp : 0 ≤ p) (hσ : 0 < σ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |x - y| ≤ L →
      materialM x ^ p ≤ K * materialM y ^ (p + σ) := by
  obtain ⟨K, hK, hb⟩ := materialM_rpow_oneSided_shift hp hσ hL
  refine ⟨K, hK, fun x y hx hy hxy => hb x y hx hy ?_⟩
  linarith only [(abs_le.mp hxy).2]

end ContinuousFlexibility.Analysis
