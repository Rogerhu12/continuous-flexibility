module

public import ContinuousFlexibility.Analysis.CylinderSobolev

/-!
# Point evaluation on a closed subinterval of a smooth open interval

The estimate uses the real derivative and the real interval integrals.
No smooth extension, endpoint value, or trace hypothesis is required.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

theorem n07a_abs_le_interval_average_add_deriv
    {f : ℝ → ℝ} {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b))
    (hfd : ContinuousOn (deriv f) (Icc a b))
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x) :
    |f t| ≤ (b - a)⁻¹ * (∫ y in Ioc a b, |f y|) +
      ∫ y in Ioc a b, |deriv f y| := by
  let A : ℝ := ∫ y in Ioc a b, |deriv f y|
  have hA : IntegrableOn (fun y => |deriv f y|) (Ioc a b) volume :=
    (hfd.abs.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hordered (u v : ℝ) (hau : a ≤ u) (hvb : v ≤ b) (huv : u ≤ v) :
      |f v - f u| ≤ A := by
    have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hau hvb
    have he : (∫ y in u..v, deriv f y) = f v - f u :=
      intervalIntegral.integral_deriv_eq_sub
        (fun y hy => hd y (hsub (by simpa only [uIcc_of_le huv] using hy)))
        ((hfd.mono hsub).intervalIntegrable_of_Icc huv)
    calc
      |f v - f u| = ‖∫ y in u..v, deriv f y‖ := by rw [he, Real.norm_eq_abs]
      _ ≤ ∫ y in u..v, |deriv f y| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm (f := deriv f) huv)
      _ ≤ A := by
        rw [intervalIntegral.integral_of_le huv]
        exact setIntegral_mono_set hA (Eventually.of_forall fun _ => abs_nonneg _)
          (Eventually.of_forall fun _ hy => ⟨hau.trans_lt hy.1, hy.2.trans hvb⟩)
  have hpoint (y : ℝ) (hy : y ∈ Ioc a b) : |f t| ≤ |f y| + A := by
    have hdiff : |f t - f y| ≤ A := by
      by_cases hyt : y ≤ t
      · exact hordered y t hy.1.le ht.2 hyt
      · rw [abs_sub_comm]
        exact hordered t y ht.1 hy.2 (le_of_not_ge hyt)
    calc
      |f t| = |f t - f y + f y| := by rw [sub_add_cancel]
      _ ≤ |f t - f y| + |f y| := abs_add_le _ _
      _ ≤ |f y| + A := by linarith
  have hleft : IntegrableOn (fun _ : ℝ => |f t|) (Ioc a b) volume :=
    continuous_const.integrableOn_Ioc
  have hfi : IntegrableOn (fun y => |f y|) (Ioc a b) volume :=
    (hf.abs.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hconst : IntegrableOn (fun _ : ℝ => A) (Ioc a b) volume :=
    continuous_const.integrableOn_Ioc
  have hm := setIntegral_mono_on hleft (hfi.add hconst) measurableSet_Ioc hpoint
  change (∫ y in Ioc a b, |f t|) ≤ ∫ y in Ioc a b, |f y| + A at hm
  rw [integral_add hfi hconst, setIntegral_const, setIntegral_const] at hm
  simp only [measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), smul_eq_mul] at hm
  have hlen : 0 < b - a := sub_pos.mpr hab
  calc
    |f t| = (b - a)⁻¹ * ((b - a) * |f t|) := by
      rw [← mul_assoc, inv_mul_cancel₀ hlen.ne', one_mul]
    _ ≤ (b - a)⁻¹ * ((∫ y in Ioc a b, |f y|) + (b - a) * A) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hlen.le)
    _ = _ := by rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hlen.ne', one_mul]

theorem n07a_abs_le_openInterval_average_add_deriv
    {f : ℝ → ℝ} {A B a b t : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo A B))
    (ha : A < a) (hb : b < B) (hab : a < b) (ht : t ∈ Icc a b) :
    |f t| ≤ (b - a)⁻¹ * (∫ y in Ioc a b, |f y|) +
      ∫ y in Ioc a b, |deriv f y| := by
  have hsub : Icc a b ⊆ Ioo A B :=
    fun _ hx => ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hd : ContDiffOn ℝ ∞ (deriv f) (Ioo A B) :=
    (hf.deriv_of_isOpen isOpen_Ioo (by simp))
  exact n07a_abs_le_interval_average_add_deriv hab ht
    (hf.continuousOn.mono hsub) (hd.continuousOn.mono hsub)
    (fun x hx => (hf.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt
      (by simp))

/-- A point in an open interval lies in an interior compact interval of
at least half the original length. -/
theorem n07a_inner_interval_half_length {A B x : ℝ} (hx : x ∈ Ioo A B) :
    ∃ a b : ℝ, A < a ∧ b < B ∧ a < b ∧ x ∈ Icc a b ∧ (B - A) / 2 ≤ b - a := by
  let δ := min ((x - A) / 2) (min ((B - x) / 2) ((B - A) / 4))
  have hδ : 0 < δ := lt_min (half_pos (sub_pos.mpr hx.1))
    (lt_min (half_pos (sub_pos.mpr hx.2)) (div_pos (sub_pos.mpr (hx.1.trans hx.2))
      (by norm_num)))
  have hδa : δ ≤ (x - A) / 2 := min_le_left _ _
  have hδb : δ ≤ (B - x) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδl : δ ≤ (B - A) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨A + δ, B - δ, by linarith, by linarith, by linarith [hx.1, hx.2],
    ⟨by linarith, by linarith⟩, by linarith⟩

end ContinuousFlexibility.Analysis
