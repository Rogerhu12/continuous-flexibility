import ContinuousFlexibility.Analysis.EndpointResistance
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Unbounded primitive of endpoint resistance

A primitive of the positive reciprocal coefficient grows without bound at a
vanishing endpoint. If it were bounded, the ordinary integrals over interior
intervals would give an integrable reciprocal by exhaustion, contradicting
the inverse-distance comparison. This argument needs only C¹ regularity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem intervalIntegrable_inverse_on_inner_Icc {a b x : ℝ}
    {w : ℝ → ℝ} (hw : Continuous w) (hwpos : ∀ r ∈ Ico a b, 0 < w r)
    (hx : x ∈ Ico a b) :
    IntervalIntegrable (fun r => (w r)⁻¹) volume a x := by
  have hc : ContinuousOn (fun r => (w r)⁻¹) (Icc a x) :=
    hw.continuousOn.inv₀ (fun r hr =>
      (hwpos r ⟨hr.1, hr.2.trans_lt hx.2⟩).ne')
  have hcu : ContinuousOn (fun r => (w r)⁻¹) (uIcc a x) := by
    simpa only [uIcc_of_le hx.1] using hc
  exact hcu.intervalIntegrable

theorem inverse_primitive_unbounded {a b : ℝ} (hab : a < b)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w)
    (hwpos : ∀ r ∈ Ico a b, 0 < w r) (hwb : w b = 0) :
    ∀ R : ℝ, ∃ r ∈ Ioo a b, R < ∫ x in a..r, (w x)⁻¹ := by
  intro R
  by_contra hn
  push_neg at hn
  let t : ℝ → ℝ := fun x => if x ∈ Ioo a b then x else a
  have ht (x : ℝ) : t x ∈ Ico a b := by
    by_cases hx : x ∈ Ioo a b
    · simpa only [t, if_pos hx] using (show x ∈ Ico a b from ⟨hx.1.le, hx.2⟩)
    · simp only [t, if_neg hx, mem_Ico, le_refl, true_and]
      exact hab
  have hti (x : ℝ) : IntegrableOn (fun r => (w r)⁻¹) (Ioc a (t x)) volume :=
    (intervalIntegrable_inverse_on_inner_Icc hw.continuous hwpos (ht x)).1
  have hlo : ∀ᶠ x in 𝓝 b, a < x := Ioi_mem_nhds hab
  have hnear : ∀ᶠ x in 𝓝[<] b, x ∈ Ioo a b :=
    (hlo.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  have htendsto : Tendsto t (𝓝[<] b) (𝓝 b) := by
    apply (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact hnear.mono (fun x hx => by simp only [t, if_pos hx, id_eq])
  have hbounded : ∀ᶠ x in 𝓝[<] b,
      (∫ r in Ioc a (t x), ‖(w r)⁻¹‖) ≤ max R 0 := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ Ioo a b
    · simp only [t, if_pos hx]
      calc
        (∫ r in Ioc a x, ‖(w r)⁻¹‖) = ∫ r in a..x, (w r)⁻¹ := by
          rw [intervalIntegral.integral_of_le hx.1.le]
          apply setIntegral_congr_fun measurableSet_Ioc
          intro r hr
          change ‖(w r)⁻¹‖ = (w r)⁻¹
          exact Real.norm_of_nonneg (inv_nonneg.mpr
            (hwpos r ⟨hr.1.le, hr.2.trans_lt hx.2⟩).le)
        _ ≤ R := hn x hx
        _ ≤ max R 0 := le_max_left _ _
    · simp only [t, if_neg hx, Ioc_self, setIntegral_empty]
      exact le_max_right _ _
  have hi : IntegrableOn (fun r => (w r)⁻¹) (Ioc a b) volume :=
    integrableOn_Ioc_of_intervalIntegral_norm_bounded_right hti htendsto hbounded
  exact not_integrableOn_inverse_of_vanishing_endpoint hab hw
    (fun r hr => hwpos r ⟨hr.1.le, hr.2⟩) hwb
    (hi.mono_set Ioo_subset_Ioc_self)

theorem inverse_primitive_mono {a b x y : ℝ} {w : ℝ → ℝ}
    (hw : Continuous w) (hwpos : ∀ r ∈ Ico a b, 0 < w r)
    (hx : a ≤ x) (hxy : x ≤ y) (hy : y < b) :
    (∫ r in a..x, (w r)⁻¹) ≤ ∫ r in a..y, (w r)⁻¹ := by
  have hix := intervalIntegrable_inverse_on_inner_Icc hw hwpos ⟨hx, hxy.trans_lt hy⟩
  have hixy : IntervalIntegrable (fun r => (w r)⁻¹) volume x y := by
    apply intervalIntegrable_inverse_on_inner_Icc hw
      (fun r hr => hwpos r ⟨hx.trans hr.1, hr.2⟩)
    exact ⟨hxy, hy⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals hix hixy
  have hnonneg : 0 ≤ ∫ r in x..y, (w r)⁻¹ :=
    intervalIntegral.integral_nonneg hxy (fun r hr =>
      inv_nonneg.mpr (hwpos r ⟨hx.trans hr.1, hr.2.trans_lt hy⟩).le)
  linarith

end ContinuousFlexibility.Analysis
