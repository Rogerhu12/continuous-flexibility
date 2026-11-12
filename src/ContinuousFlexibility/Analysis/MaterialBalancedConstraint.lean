import ContinuousFlexibility.Analysis.MaterialMScale

/-!
# Fixed material-order loss from a balanced height constraint

The positive and negative height powers in the constraint have the same
cubic coefficient. Every other fixed weight is subcubic. Thus the first
coordinate is at most an arbitrarily small multiplicative enlargement
of the second, apart from a bounded initial region. Combining this with
the explicit material scaling bound costs any prescribed positive extra
material order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

theorem exists_small_height_reserve
    {β C : ℝ} (hβ : 0 < β) (hC : 1 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ε < β ∧ β + ε < (β - ε) * C ^ 3 := by
  have hC3 : (1 : ℝ) < C ^ 3 := by
    simpa only [one_pow] using pow_lt_pow_left₀ hC (by norm_num) (by decide : 3 ≠ 0)
  have hgap : 0 < (β - 0) * C ^ 3 - (β + 0) := by
    have h := mul_lt_mul_of_pos_left hC3 hβ
    nlinarith only [h]
  have hc : ContinuousAt (fun ε : ℝ => (β - ε) * C ^ 3 - (β + ε)) 0 := by
    fun_prop
  have hpositive : ∀ᶠ ε : ℝ in 𝓝 0, 0 < (β - ε) * C ^ 3 - (β + ε) :=
    hc.eventually (Ioi_mem_nhds hgap)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0, ε < β := Iio_mem_nhds hβ
  have hh : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ ε < β ∧ β + ε < (β - ε) * C ^ 3 := by
    filter_upwards [hpositive.filter_mono nhdsWithin_le_nhds,
      hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hp hs he
    exact ⟨he, hs, sub_pos.mp hp⟩
  exact hh.exists

theorem exists_bound_or_scale_of_cubic_exp
    {K C a b : ℝ} (hK : 0 < K) (hC : 0 < C) (hb : 0 ≤ b)
    (hgap : b < a * C ^ 3) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      1 ≤ K * Real.exp (-a * x ^ 3 + b * y ^ 3) → x ≤ C * y ∨ x ≤ R := by
  let Q := C ^ 3 * |Real.log K| / (a * C ^ 3 - b)
  have hden : 0 < a * C ^ 3 - b := sub_pos.mpr hgap
  have hQ : 0 ≤ Q := div_nonneg
    (mul_nonneg (pow_nonneg hC.le 3) (abs_nonneg _)) hden.le
  refine ⟨1 + Q, by linarith only [hQ], fun x y hx hy hraw => ?_⟩
  by_cases hxy : x ≤ C * y
  · exact Or.inl hxy
  · right
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hraw
    rw [Real.log_one, Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    have hcube : C ^ 3 * y ^ 3 ≤ x ^ 3 := by
      have h := pow_le_pow_left₀ (mul_nonneg hC.le hy) (le_of_not_ge hxy) 3
      simpa only [mul_pow] using h
    have hbcube := mul_le_mul_of_nonneg_left hcube hb
    have hmain : (a * C ^ 3 - b) * x ^ 3 ≤ C ^ 3 * |Real.log K| := by
      calc
        _ ≤ C ^ 3 * (a * x ^ 3 - b * y ^ 3) := by nlinarith only [hbcube]
        _ ≤ C ^ 3 * Real.log K := mul_le_mul_of_nonneg_left
          (by linarith only [hlog]) (pow_nonneg hC.le 3)
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hC.le 3)
    have hxQ : x ^ 3 ≤ Q := by
      apply (le_div_iff₀ hden).mpr
      simpa only [mul_comm (x ^ 3) (a * C ^ 3 - b)] using hmain
    by_cases hx1 : x ≤ 1
    · linarith only [hx1, hQ]
    · have hxpow : x ≤ x ^ 3 := by
        simpa only [pow_one] using
          pow_le_pow_right₀ (le_of_not_ge hx1) (by decide : 1 ≤ 3)
      exact (hxpow.trans hxQ).trans (by linarith only [hQ])

/-- Equal positive and negative height powers yield a fixed material
loss, even in the presence of arbitrary fixed `E0` and `M` powers. -/
theorem materialM_rpow_le_of_balanced_height_constraint
    {β A N K p σ : ℝ} (hβ : 0 < β) (hK : 0 < K)
    (hp : 0 ≤ p) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      1 ≤ K * materialH x ^ β * materialE0 x ^ A *
        materialH y ^ (-β) * materialM y ^ N →
      materialM x ^ p ≤ C * materialM y ^ (p + σ) := by
  obtain ⟨c, hc, hscale⟩ := exists_materialM_scale_for_extra_order (p := p) hσ
  obtain ⟨ε, hε, hεβ, hreserve⟩ := exists_small_height_reserve hβ hc
  obtain ⟨CE, hCE, hE⟩ := materialH_rpow_mul_materialE0_rpow_le A hε
  obtain ⟨CM, hCM, hM⟩ := materialH_rpow_mul_materialM_rpow_le N hε
  let a := (β - ε) * 2 / 3
  let b := (β + ε) * 2 / 3
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hgap : b < a * c ^ 3 := by
    dsimp only [a, b]
    nlinarith only [hreserve]
  obtain ⟨R, hR, hRbound⟩ := exists_bound_or_scale_of_cubic_exp
    (mul_pos hK (mul_pos hCE hCM)) (zero_lt_one.trans hc) hb hgap
  refine ⟨materialM R ^ p, Real.rpow_pos_of_pos (materialM_pos R) _,
    fun x y hx hy hraw => ?_⟩
  have hH : materialH x ^ β * materialH y ^ (-β) =
      (materialH x ^ ε * materialH y ^ ε) *
        Real.exp (-a * x ^ 3 + b * y ^ 3) := by
    simp only [materialH, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    dsimp only [a, b]
    ring
  have hfactor :
      K * materialH x ^ β * materialE0 x ^ A * materialH y ^ (-β) * materialM y ^ N =
        K * ((materialH x ^ ε * materialE0 x ^ A) *
          (materialH y ^ ε * materialM y ^ N)) *
            Real.exp (-a * x ^ 3 + b * y ^ 3) := by
    calc
      _ = K * (materialH x ^ β * materialH y ^ (-β)) *
          (materialE0 x ^ A * materialM y ^ N) := by ring
      _ = K * ((materialH x ^ ε * materialH y ^ ε) *
          Real.exp (-a * x ^ 3 + b * y ^ 3)) *
            (materialE0 x ^ A * materialM y ^ N) := by rw [hH]
      _ = _ := by ring
  have hprod : (materialH x ^ ε * materialE0 x ^ A) *
      (materialH y ^ ε * materialM y ^ N) ≤ CE * CM :=
    mul_le_mul (hE x hx) (hM y hy)
      (mul_nonneg (Real.rpow_nonneg (materialH_pos y).le _)
        (Real.rpow_nonneg (materialM_pos y).le _)) hCE.le
  have hraw' : 1 ≤ (K * (CE * CM)) * Real.exp (-a * x ^ 3 + b * y ^ 3) :=
    hraw.trans (hfactor.le.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod hK.le) (Real.exp_pos _).le))
  exact materialM_rpow_le_of_scale_or_bound hp hσ hc.le hscale hR hx hy
    (hRbound x y hx hy hraw')

end ContinuousFlexibility.Analysis
