import ContinuousFlexibility.Radial.BufferIntervalTrace

/-!
# Bounded traces of weak energy representatives

The interval indicator realizes an integral as a true `L²` pairing.
Cauchy--Schwarz and an interval average then give bounded point evaluation
without requiring classical differentiability of the representative.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

def bufferIntervalUnit (x y : ℝ) : RadialL2 :=
  indicatorConstLp (s := Ioc x y) 2 measurableSet_Ioc
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) 1

theorem bufferIntervalUnit_ae (x y : ℝ) :
    (bufferIntervalUnit x y : ℝ → ℝ) =ᵐ[volume] (Ioc x y).indicator (fun _ => 1) :=
  indicatorConstLp_coeFn

theorem bufferInterval_pairing (g : RadialL2) {f : ℝ → ℝ}
    (hf : (g : ℝ → ℝ) =ᵐ[volume] f) (x y : ℝ) :
    ⟪g, bufferIntervalUnit x y⟫_ℝ = ∫ t in Ioc x y, f t := by
  rw [L2.inner_def, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [hf, bufferIntervalUnit_ae x y] with t hft ht
  simp only [RCLike.inner_apply, conj_trivial, hft, ht]
  by_cases h : t ∈ Ioc x y
  · simp only [indicator_of_mem h, one_mul]
  · simp only [indicator_of_notMem h, zero_mul]

theorem bufferIntervalUnit_norm {x y : ℝ} (hxy : x ≤ y) :
    ‖bufferIntervalUnit x y‖ = sqrt (y - x) := by
  have h : ‖bufferIntervalUnit x y‖ ^ 2 = y - x := by
    rw [← real_inner_self_eq_norm_sq,
      bufferInterval_pairing _ (bufferIntervalUnit_ae x y) x y]
    calc
      _ = ∫ _ in Ioc x y, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact indicator_of_mem ht _
      _ = _ := by rw [setIntegral_const, Real.volume_real_Ioc_of_le hxy, smul_eq_mul, mul_one]
  have hs := congrArg sqrt h
  rwa [sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs

theorem bufferRepresentative_abs_sub_le {U : ℝ → ℝ} (d : RadialL2)
    (hprim : ∀ x y : ℝ, U y - U x = ∫ t in x..y, d t) {x y : ℝ} (hxy : x ≤ y) :
    |U y - U x| ≤ ‖d‖ * sqrt (y - x) := by
  rw [hprim x y, intervalIntegral.integral_of_le hxy,
    ← bufferInterval_pairing d (EventuallyEq.rfl) x y,
    ← Real.norm_eq_abs, ← bufferIntervalUnit_norm hxy]
  exact norm_inner_le_norm (𝕜 := ℝ) _ _

def bufferIntervalAverage (g : RadialL2) (x δ : ℝ) : ℝ :=
  δ⁻¹ * ⟪g, bufferIntervalUnit x (x + δ)⟫_ℝ

theorem bufferRepresentative_average_error {U : ℝ → ℝ} (hU : Continuous U)
    (u d : RadialL2) (hu : (u : ℝ → ℝ) =ᵐ[volume] U)
    (hprim : ∀ x y : ℝ, U y - U x = ∫ t in x..y, d t)
    (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |U x - bufferIntervalAverage u x δ| ≤ ‖d‖ * sqrt δ := by
  have hxy : x ≤ x + δ := by linarith
  have hid : U x - bufferIntervalAverage u x δ =
      δ⁻¹ * (∫ t in x..(x + δ), U x - U t) := by
    rw [bufferIntervalAverage, bufferInterval_pairing u hu,
      ← intervalIntegral.integral_of_le hxy,
      intervalIntegral.integral_sub intervalIntegrable_const (hU.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
    field_simp [hδ.ne']
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + δ)
    (C := ‖d‖ * sqrt δ) (f := fun t => U x - U t) (fun t ht => by
      rw [uIoc_of_le hxy] at ht
      rw [Real.norm_eq_abs, abs_sub_comm]
      refine (bufferRepresentative_abs_sub_le d hprim ht.1.le).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [ht.2])) (norm_nonneg d))
  rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hδ] at hi
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
  calc
    _ ≤ δ⁻¹ * ((‖d‖ * sqrt δ) * δ) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hδ.le)
    _ = _ := by field_simp [hδ.ne']

theorem bufferIntervalAverage_one_bound (g : RadialL2) (x : ℝ) :
    |bufferIntervalAverage g x 1| ≤ ‖g‖ := by
  have hxy : x ≤ x + 1 := by linarith
  have hi := norm_inner_le_norm (𝕜 := ℝ) g (bufferIntervalUnit x (x + 1))
  rw [bufferIntervalUnit_norm hxy, add_sub_cancel_left, sqrt_one, mul_one, Real.norm_eq_abs] at hi
  simpa only [bufferIntervalAverage, inv_one, one_mul] using hi

/-- Uniform point evaluation is bounded by the genuine first-order graph norm. -/
theorem bufferRepresentative_abs_le {U : ℝ → ℝ} (hU : Continuous U)
    (u d : RadialL2) (hu : (u : ℝ → ℝ) =ᵐ[volume] U)
    (hprim : ∀ x y : ℝ, U y - U x = ∫ t in x..y, d t) (x : ℝ) :
    |U x| ≤ ‖u‖ + ‖d‖ := by
  have he := bufferRepresentative_average_error hU u d hu hprim x (by norm_num : 0 < (1 : ℝ))
  rw [sqrt_one, mul_one] at he
  calc
    _ = |(U x - bufferIntervalAverage u x 1) + bufferIntervalAverage u x 1| := by
      rw [sub_add_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ ‖u‖ + ‖d‖ := by linarith [bufferIntervalAverage_one_bound u x]

end ContinuousFlexibility.Radial
