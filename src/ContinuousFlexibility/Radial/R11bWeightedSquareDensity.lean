import ContinuousFlexibility.Radial.R11bPartitionL2

/-!
# Real weighted square densities and Tonelli

A summable family of nonnegative ordinary integrals has an integrable real
pointwise sum. The proof passes through the nonnegative extended-real sum,
whose finiteness almost everywhere also handles the real tsum's junk value.
-/

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped ENNReal

theorem r11b_integrable_tsum_of_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℝ) (hF : ∀ n, Integrable (F n) μ)
    (h0 : ∀ n x, 0 ≤ F n x) (hs : Summable (fun n => ∫ x, F n x ∂μ)) :
    Integrable (fun x => ∑' n, F n x) μ ∧
      (∫ x, ∑' n, F n x ∂μ) = ∑' n, ∫ x, F n x ∂μ := by
  let H : α → ℝ≥0∞ := fun x => ∑' n, ENNReal.ofReal (F n x)
  have hHm : AEMeasurable H μ :=
    AEMeasurable.tsum (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hlin : (∫⁻ x, H x ∂μ) = ENNReal.ofReal (∑' n, ∫ x, F n x ∂μ) := by
    dsimp [H]
    rw [lintegral_tsum
      (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    calc
      (∑' n, ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) =
          ∑' n, ENNReal.ofReal (∫ x, F n x ∂μ) := by
        apply tsum_congr
        intro n
        exact (ofReal_integral_eq_lintegral_ofReal (hF n)
          (Eventually.of_forall (h0 n))).symm
      _ = ENNReal.ofReal (∑' n, ∫ x, F n x ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (h0 n)) hs).symm
  have hreal (x : α) : (H x).toReal = ∑' n, F n x := by
    dsimp [H]
    rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun n => ENNReal.toReal_ofReal (h0 n x))
  have hm : AEStronglyMeasurable (fun x => ∑' n, F n x) μ :=
    hHm.ennreal_toReal.aestronglyMeasurable.congr (Eventually.of_forall hreal)
  have hnn : ∀ᵐ x ∂μ, 0 ≤ ∑' n, F n x :=
    Eventually.of_forall (fun x => tsum_nonneg (fun n => h0 n x))
  have hfinite : (∫⁻ x, H x ∂μ) ≠ ∞ := by
    rw [hlin]
    exact ENNReal.ofReal_ne_top
  have hrealLin : (∫⁻ x, ENNReal.ofReal (∑' n, F n x) ∂μ) =
      ENNReal.ofReal (∑' n, ∫ x, F n x ∂μ) := by
    calc
      _ = ∫⁻ x, H x ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_lt_top' hHm hfinite] with x hx
        rw [← hreal x, ENNReal.ofReal_toReal hx.ne]
      _ = _ := hlin
  have hint : Integrable (fun x => ∑' n, F n x) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm hnn).mp (by
      rw [hrealLin]
      exact ENNReal.ofReal_ne_top)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm, hrealLin,
    ENNReal.toReal_ofReal (tsum_nonneg (fun n => integral_nonneg (h0 n)))]

theorem r11b_integrable_weighted_square
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : MemLp g 2 μ) (w : ℝ) :
    Integrable (fun x => w * g x ^ 2) μ :=
  hg.integrable_sq.const_mul w

theorem r11b_weighted_square_tsum_nonneg
    {α : Type*} (g : ℕ → α → ℝ) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (x : α) :
    0 ≤ ∑' n, w n * g n x ^ 2 :=
  tsum_nonneg (fun n => mul_nonneg (hw n) (sq_nonneg _))

theorem r11b_integrable_weighted_square_tsum
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : ℕ → α → ℝ) (w : ℕ → ℝ)
    (hg : ∀ n, MemLp (g n) 2 μ) (hw : ∀ n, 0 ≤ w n)
    (hs : Summable (fun n => w n * ∫ x, g n x ^ 2 ∂μ)) :
    Integrable (fun x => ∑' n, w n * g n x ^ 2) μ ∧
      (∫ x, ∑' n, w n * g n x ^ 2 ∂μ) = ∑' n, w n * ∫ x, g n x ^ 2 ∂μ := by
  have hs' : Summable (fun n => ∫ x, w n * g n x ^ 2 ∂μ) := by
    simpa only [integral_const_mul] using hs
  have h := r11b_integrable_tsum_of_nonneg (fun n x => w n * g n x ^ 2)
    (fun n => r11b_integrable_weighted_square (hg n) (w n))
    (fun n x => mul_nonneg (hw n) (sq_nonneg _)) hs'
  simpa only [integral_const_mul] using h

end ContinuousFlexibility.Radial
