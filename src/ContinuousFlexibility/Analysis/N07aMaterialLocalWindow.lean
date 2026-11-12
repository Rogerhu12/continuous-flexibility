import ContinuousFlexibility.Analysis.MaterialLocalComparison

/-!
# Material ratios on a short physical radial segment

The first logarithmic material derivative bounds make the scale ell
Lipschitz. On a radial segment short compared with ell at its initial
point, ell stays above half that value. The same bounds then compare H
and M in both directions. No relation between discrete cell labels is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff Interval

private theorem n07a_material_first_log_bounds
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D,
      |deriv T.ell r| ≤ C ∧
      |T.ell r * deriv (fun t => Real.log (T.H t)) r| ≤ C ∧
      |T.ell r * deriv (fun t => Real.log (T.M t)) r| ≤ C := by
  have h := hT
  obtain ⟨hsmooth, hpos, _, _, _, _, _, _, _, _, _, _, _, hlog, _⟩ := h
  obtain ⟨C, hC, hb⟩ := hlog 1 (by decide)
  have hell : ContDiffOn ℝ ∞ T.ell (radialCore D) := hsmooth T.ell (by simp)
  refine ⟨C, hC, fun r hr => ?_⟩
  have hd : HasDerivAt T.ell (deriv T.ell r) r :=
    ((hell.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hp : 0 < T.ell r := (hpos r hr).1
  have he : T.ell r * deriv (fun t => Real.log (T.ell t)) r = deriv T.ell r := by
    rw [(hd.log hp.ne').deriv]
    field_simp [hp.ne'] <;> ring
  have hbr := hb r hr
  simp only [materialDerivativeIterate, Function.iterate_one, materialDerivative] at hbr
  exact ⟨by simpa only [he] using hbr.2.2, hbr.1, hbr.2.1⟩

private theorem n07a_ratios_of_log_difference
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlog : |Real.log x - Real.log y| ≤ 1) :
    x / y ≤ Real.exp 1 ∧ y / x ≤ Real.exp 1 := by
  constructor
  · have h := Real.exp_le_exp.mpr (abs_le.mp hlog).2
    simpa only [Real.exp_sub, Real.exp_log hx, Real.exp_log hy] using h
  · have h := Real.exp_le_exp.mpr (show Real.log y - Real.log x ≤ 1 by
      linarith only [(abs_le.mp hlog).1])
    simpa only [Real.exp_sub, Real.exp_log hx, Real.exp_log hy] using h

/-- A single positive fraction of the initial material length controls both
directions of both physical weight ratios. -/
theorem n07a_material_local_ratio_window
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r₀ ∈ radialCore D, ∀ r ∈ radialCore D,
      |r - r₀| ≤ δ * T.ell r₀ →
        T.H r / T.H r₀ ≤ Real.exp 1 ∧ T.H r₀ / T.H r ≤ Real.exp 1 ∧
        T.M r / T.M r₀ ≤ Real.exp 1 ∧ T.M r₀ / T.M r ≤ Real.exp 1 := by
  obtain ⟨C, hC, hb⟩ := n07a_material_first_log_bounds hT
  let δ : ℝ := (2 * (C + 1))⁻¹
  have hden : 0 < 2 * (C + 1) := by positivity
  have hδ : 0 < δ := inv_pos.mpr hden
  have hell : ContDiffOn ℝ ∞ T.ell (radialCore D) := hT.1 T.ell (by simp)
  have hH : ContDiffOn ℝ ∞ T.H (radialCore D) := hT.1 T.H (by simp)
  have hM : ContDiffOn ℝ ∞ T.M (radialCore D) := hT.1 T.M (by simp)
  refine ⟨δ, hδ, fun r₀ hr₀ r hr hdist => ?_⟩
  have hℓ : 0 < T.ell r₀ := (hT.2.1 r₀ hr₀).1
  have hsmall : 2 * (C + 1) * |r - r₀| ≤ T.ell r₀ := by
    calc
      _ ≤ 2 * (C + 1) * (δ * T.ell r₀) :=
        mul_le_mul_of_nonneg_left hdist hden.le
      _ = _ := by dsimp only [δ]; field_simp [hden.ne'] <;> ring
  have hseg : uIcc r₀ r ⊆ radialCore D := ordConnected_Ioo.uIcc_subset hr₀ hr
  have hellhalf : ∀ t ∈ uIcc r₀ r, T.ell r₀ / 2 ≤ T.ell t := by
    intro t ht
    have hd : |t - r₀| ≤ |r - r₀| := abs_sub_left_of_mem_uIcc ht
    have hb' : |T.ell t - T.ell r₀| ≤ C * |t - r₀| := by
      simpa only [Real.norm_eq_abs] using
        (convex_Ioo D.a D.b).norm_image_sub_le_of_norm_deriv_le
          (fun x hx => (hell.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by simp))
          (fun x hx => by simpa only [Real.norm_eq_abs] using (hb x hx).1)
          hr₀ (hseg ht)
    have hble := hb'.trans (mul_le_mul_of_nonneg_left hd hC)
    have habs : 0 ≤ |r - r₀| := abs_nonneg _
    have hlow := (abs_le.mp hble).1
    nlinarith only [hsmall, habs, hlow]
  have hlog (w : ℝ → ℝ) (hw : ContDiffOn ℝ ∞ w (radialCore D))
      (hwp : ∀ t ∈ radialCore D, 0 < w t)
      (hwb : ∀ t ∈ radialCore D, |T.ell t * deriv (fun x => Real.log (w x)) t| ≤ C) :
      |Real.log (w r) - Real.log (w r₀)| ≤ 1 := by
    have hderiv : ∀ t ∈ uIcc r₀ r,
        ‖deriv (fun x => Real.log (w x)) t‖ ≤ 2 * C / T.ell r₀ := by
      intro t ht
      have htD := hseg ht
      have hb' := hwb t htD
      rw [abs_mul, abs_of_pos (hT.2.1 t htD).1] at hb'
      rw [Real.norm_eq_abs]
      apply (le_div_iff₀ hℓ).mpr
      have hp := hellhalf t ht
      have hscaled := mul_le_mul_of_nonneg_right hp
        (abs_nonneg (deriv (fun x => Real.log (w x)) t))
      nlinarith only [hb', hscaled]
    have hmv : |Real.log (w r) - Real.log (w r₀)| ≤
        (2 * C / T.ell r₀) * |r - r₀| := by
      simpa only [Real.norm_eq_abs] using
        (convex_uIcc r₀ r).norm_image_sub_le_of_norm_deriv_le
          (fun t ht => ((hw.contDiffAt (isOpen_Ioo.mem_nhds (hseg ht))).log
            (hwp t (hseg ht)).ne').differentiableAt (by simp))
          hderiv left_mem_uIcc right_mem_uIcc
    apply hmv.trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hℓ).mpr
    nlinarith only [hsmall, abs_nonneg (r - r₀)]
  have hHp (t : ℝ) (ht : t ∈ radialCore D) : 0 < T.H t := (hT.2.1 t ht).2.1
  have hMp (t : ℝ) (ht : t ∈ radialCore D) : 0 < T.M t :=
    zero_lt_one.trans_le (hT.2.1 t ht).2.2.2
  have hHr := n07a_ratios_of_log_difference (hHp r hr) (hHp r₀ hr₀)
    (hlog T.H hH hHp (fun t ht => (hb t ht).2.1))
  have hMr := n07a_ratios_of_log_difference (hMp r hr) (hMp r₀ hr₀)
    (hlog T.M hM hMp (fun t ht => (hb t ht).2.2))
  exact ⟨hHr.1, hHr.2, hMr.1, hMr.2⟩

end ContinuousFlexibility.Analysis
