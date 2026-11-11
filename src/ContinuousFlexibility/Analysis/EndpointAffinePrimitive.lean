import ContinuousFlexibility.Analysis.EndpointPrimitive
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weighted exclusion of homogeneous endpoint solutions

An affine function of the reciprocal-coefficient primitive cannot have finite
square integral with reciprocal weight unless both affine coefficients vanish.
This is the endpoint uniqueness mechanism for the weak zero angular channel.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem affine_inverse_primitive_eq_zero_of_integrable {a b : ℝ} (hab : a < b)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w)
    (hwpos : ∀ r ∈ Ico a b, 0 < w r) (hwb : w b = 0) (c q : ℝ)
    (hi : IntegrableOn (fun r => (w r)⁻¹ *
      (c + q * (∫ x in a..r, (w x)⁻¹)) ^ 2) (Ioo a b) volume) :
    c = 0 ∧ q = 0 := by
  let P : ℝ → ℝ := fun r => ∫ x in a..r, (w x)⁻¹
  change IntegrableOn (fun r => (w r)⁻¹ * (c + q * P r) ^ 2) (Ioo a b) volume at hi
  have hq : q = 0 := by
    by_contra hq
    have hqabs : 0 < |q| := abs_pos.mpr hq
    obtain ⟨r₀, hr₀, hP₀⟩ :=
      inverse_primitive_unbounded hab hw hwpos hwb ((|c| + 1) / |q|)
    have hlarge (r : ℝ) (hr : r ∈ Ioo r₀ b) : 1 ≤ (c + q * P r) ^ 2 := by
      have hmono : P r₀ ≤ P r :=
        inverse_primitive_mono hw.continuous hwpos hr₀.1.le hr.1.le hr.2
      have hR : (|c| + 1) / |q| < P r := hP₀.trans_le hmono
      have hPr : 0 < P r := (div_pos (by positivity) hqabs).trans hR
      have hbig : |c| + 1 < |q| * P r := by
        have h := (div_lt_iff₀ hqabs).mp hR
        simpa only [mul_comm] using h
      have htri : |q| * P r ≤ |c + q * P r| + |c| := by
        calc
          |q| * P r = |q * P r| := by rw [abs_mul, abs_of_pos hPr]
          _ = |(c + q * P r) + -c| := by congr 1; ring
          _ ≤ |c + q * P r| + |-c| := by
            simpa only [Real.norm_eq_abs] using norm_add_le (c + q * P r) (-c)
          _ = |c + q * P r| + |c| := by rw [abs_neg]
      have hOne : (1 : ℝ) ≤ |c + q * P r| := by linarith
      have hs := (sq_le_sq₀ zero_le_one (abs_nonneg (c + q * P r))).mpr hOne
      simpa only [one_pow, sq_abs] using hs
    have hmajor : IntegrableOn (fun r => (w r)⁻¹ * (c + q * P r) ^ 2)
        (Ioo r₀ b) volume :=
      hi.mono_set (Ioo_subset_Ioo hr₀.1.le le_rfl)
    have hinv : IntegrableOn (fun r => (w r)⁻¹) (Ioo r₀ b) volume := by
      apply hmajor.mono' (hw.continuous.measurable.inv.aestronglyMeasurable)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hw0 : 0 ≤ (w r)⁻¹ :=
        inv_nonneg.mpr (hwpos r ⟨hr₀.1.le.trans hr.1.le, hr.2⟩).le
      change ‖(w r)⁻¹‖ ≤ (w r)⁻¹ * (c + q * P r) ^ 2
      rw [Real.norm_of_nonneg hw0]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hlarge r hr) hw0
    exact not_integrableOn_inverse_of_vanishing_endpoint hr₀.2 hw
      (fun r hr => hwpos r ⟨hr₀.1.le.trans hr.1.le, hr.2⟩) hwb hinv
  have hc : c = 0 := by
    by_contra hc
    have hi' : IntegrableOn (fun r => (w r)⁻¹ * c ^ 2) (Ioo a b) volume := by
      simpa only [hq, zero_mul, add_zero] using hi
    have hinv : IntegrableOn (fun r => (w r)⁻¹) (Ioo a b) volume := by
      apply (hi'.mul_const ((c ^ 2)⁻¹)).congr
      apply Eventually.of_forall
      intro r
      change ((w r)⁻¹ * c ^ 2) * (c ^ 2)⁻¹ = (w r)⁻¹
      rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hc), mul_one]
    exact not_integrableOn_inverse_of_vanishing_endpoint hab hw
      (fun r hr => hwpos r ⟨hr.1.le, hr.2⟩) hwb hinv
  exact ⟨hc, hq⟩

theorem affine_inverse_primitive_eq_zero_of_memLp {a b : ℝ} (hab : a < b)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w)
    (hwpos : ∀ r ∈ Ico a b, 0 < w r) (hwb : w b = 0) (c q : ℝ)
    (hu : MemLp (fun r => Real.sqrt ((w r)⁻¹) *
      (c + q * (∫ x in a..r, (w x)⁻¹))) 2 (volume.restrict (Ioo a b))) :
    c = 0 ∧ q = 0 := by
  apply affine_inverse_primitive_eq_zero_of_integrable hab hw hwpos hwb c q
  apply hu.integrable_sq.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  change (Real.sqrt ((w r)⁻¹) * (c + q * (∫ x in a..r, (w x)⁻¹))) ^ 2 =
    (w r)⁻¹ * (c + q * (∫ x in a..r, (w x)⁻¹)) ^ 2
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr (hwpos r ⟨hr.1.le, hr.2⟩).le)]

end ContinuousFlexibility.Analysis
