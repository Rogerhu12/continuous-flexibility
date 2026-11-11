import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# L² bounds for the actual Seeley reflection series

Each reflection scale is at least one, so pulling a function back from the
positive half-line to the negative half-line does not increase its L² norm.
The summable absolute moments then control the same extension formula at every
derivative order. The estimates concern the actual pointwise series and do not
assume an extension operator as input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A dilation followed by reflection, with scale at least one, sends negative
half-line volume to a measure bounded by positive half-line volume. -/
theorem map_neg_mul_restrict_Iic_le {b : ℝ} (hb : 1 ≤ b) :
    Measure.map (fun x : ℝ => -b * x) (volume.restrict (Iic 0)) ≤
      volume.restrict (Ici 0) := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hpre : (fun x : ℝ => -b * x) ⁻¹' Ici 0 = Iic 0 := by
    ext x
    simpa only [mem_preimage, mem_Ici, mem_Iic, neg_mul, neg_nonneg, mul_zero] using
      (mul_le_mul_iff_right₀ hbpos : b * x ≤ b * 0 ↔ x ≤ 0)
  have hmap : Measure.map (fun x : ℝ => -b * x) (volume.restrict (Iic 0)) =
      ENNReal.ofReal |(-b)⁻¹| • volume.restrict (Ici 0) := by
    rw [← hpre, ← Measure.restrict_map (measurable_const_mul (-b)) measurableSet_Ici,
      Real.map_volume_mul_left (neg_ne_zero.mpr hbpos.ne'), Measure.restrict_smul]
  have hc : ENNReal.ofReal |(-b)⁻¹| ≤ 1 := by
    rw [inv_neg, abs_neg, abs_of_nonneg (inv_nonneg.mpr hbpos.le)]
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ hb)
  rw [hmap]
  apply Measure.le_iff'.mpr
  intro s
  rw [Measure.smul_apply, smul_eq_mul]
  exact (mul_le_mul_left hc _).trans_eq (one_mul _)

/-- The reflection estimate is valid for every exponent, before specializing
to the Hilbert exponent used by the Sobolev completion. -/
theorem eLpNorm_neg_mul_Iic_le (f : ℝ → F) (p : ℝ≥0∞) {b : ℝ} (hb : 1 ≤ b) :
    eLpNorm (fun x => f (-b * x)) p (volume.restrict (Iic 0)) ≤
      eLpNorm f p (volume.restrict (Ici 0)) := by
  have hneg : -b ≠ 0 := neg_ne_zero.mpr (zero_lt_one.trans_le hb).ne'
  calc
    eLpNorm (fun x => f (-b * x)) p (volume.restrict (Iic 0)) =
        eLpNorm f p (Measure.map (fun x : ℝ => -b * x)
          (volume.restrict (Iic 0))) :=
      (measurableEmbedding_mulLeft₀ hneg).eLpNorm_map_measure.symm
    _ ≤ eLpNorm f p (volume.restrict (Ici 0)) :=
      eLpNorm_mono_measure f (map_neg_mul_restrict_Iic_le hb)

theorem eLpNorm_neg_mul_Iio_le (f : ℝ → F) (p : ℝ≥0∞) {b : ℝ} (hb : 1 ≤ b) :
    eLpNorm (fun x => f (-b * x)) p (volume.restrict (Iio 0)) ≤
      eLpNorm f p (volume.restrict (Ici 0)) := by
  have hmeasure : (volume : Measure ℝ).restrict (Iio 0) ≤
      volume.restrict (Iic 0) :=
    Measure.restrict_mono (fun (x : ℝ) (hx : x < 0) => hx.le)
      (le_refl (volume : Measure ℝ))
  calc
    eLpNorm (fun x => f (-b * x)) p (volume.restrict (Iio 0)) ≤
        eLpNorm (fun x => f (-b * x)) p (volume.restrict (Iic 0)) :=
      eLpNorm_mono_measure (fun x => f (-b * x)) hmeasure
    _ ≤ eLpNorm f p (volume.restrict (Ici 0)) := eLpNorm_neg_mul_Iic_le f p hb

theorem memLp_neg_mul_Iio {f : ℝ → F} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Ici 0))) {b : ℝ} (hb : 1 ≤ b) :
    MemLp (fun x => f (-b * x)) p (volume.restrict (Iio 0)) :=
  memLp_iff.mpr ((eLpNorm_neg_mul_Iio_le f p hb).trans_lt (memLp_iff.mp hf))

end ContinuousFlexibility.Analysis
