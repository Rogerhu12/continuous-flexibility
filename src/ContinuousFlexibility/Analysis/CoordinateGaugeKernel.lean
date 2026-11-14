module

public import ContinuousFlexibility.Analysis.SquareDensityIsometry
public import ContinuousFlexibility.Analysis.CoordinateL2Isometry

/-!
# Integral kernels under an exact coordinate and gauge isometry

The density is allowed to vanish or grow at an endpoint.  The proof uses
the exact square-density change of measure, so no bounded reciprocal
multiplier is required.  Both the all-source formula and the individual
L² kernel rows are transported.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory Filter
open scoped ENNReal

variable {μ ν : Measure ℝ} {R a : ℝ → ℝ} {s : ℝ}
  (hR : MeasurableEmbedding R) (ha : Measurable a) (hpos : ∀ x, 0 < a x)
  (hmeasure : Measure.map R (squareDensityMeasure μ a) = ν)
  {K H : ℝ → ℝ → ℝ}

include hR ha hmeasure in
/-- The exact integral change with both amplitude factors. -/
theorem coordinateGauge_kernel_integral (f : ℝ → ℝ) (x : ℝ)
    (hK : ∀ᵐ y ∂μ, a x * a y * H (R x) (R y) = s * K x y) :
    a x * (∫ r, H (R x) r * f r ∂ν) =
      ∫ y, K x y * (s * (a y * f (R y))) ∂μ := by
  have hi : (∫ r, H (R x) r * f r ∂ν) =
      ∫ y, a y ^ 2 * (H (R x) (R y) * f (R y)) ∂μ := by
    rw [← hmeasure, hR.integral_map, squareDensityMeasure,
      integral_withDensity_eq_integral_toReal_smul
        (ha.pow_const 2).ennreal_ofReal (by simp)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by
      change (ENNReal.ofReal (a y ^ 2)).toReal • (H (R x) (R y) * f (R y)) = _
      rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul])
  rw [hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hK] with y hy
  calc
    a x * (a y ^ 2 * (H (R x) (R y) * f (R y))) =
        (a x * a y * H (R x) (R y)) * (a y * f (R y)) := by ring
    _ = K x y * (s * (a y * f (R y))) := by rw [hy]; ring

include hR ha hpos hmeasure in
/-- An actual L² row is preserved by the exact coordinate/gauge change. -/
theorem coordinateGauge_kernel_row_memLp (x : ℝ)
    (hK : ∀ᵐ y ∂μ, a x * a y * H (R x) (R y) = s * K x y)
    (hrow : MemLp (K x) 2 μ) : MemLp (H (R x)) 2 ν := by
  rw [← hmeasure]
  apply hR.memLp_map_measure_iff.mpr
  apply (squareDensity_memLp_iff μ ha hpos _).mpr
  refine (memLp_congr_ae ?_).mp (hrow.const_mul (s / a x))
  filter_upwards [hK] with y hy
  change (s / a x) * K x y = a y * H (R x) (R y)
  apply mul_left_cancel₀ (hpos x).ne'
  calc
    a x * ((s / a x) * K x y) = s * K x y := by field_simp [(hpos x).ne'] <;> ring
    _ = a x * (a y * H (R x) (R y)) := by rw [← hy]; ring

include hR ha hpos hmeasure in
/-- The conjugated bounded operator has the transformed kernel for every
L² source.  The exact isometry and conjugacy are supplied by the coordinate
and square-density constructions. -/
theorem coordinateGauge_operator_kernel
    (E : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ)
    (hE : ∀ f : Lp ℝ 2 ν, (E f : ℝ → ℝ) =ᵐ[μ] fun x => a x * f (R x))
    (G : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (D : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hconj : ∀ f, E (D f) = G (s • E f))
    (hG : ∀ f : Lp ℝ 2 μ, (G f : ℝ → ℝ) =ᵐ[μ] fun x =>
      ∫ y, K x y * f y ∂μ)
    (hK : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, a x * a y * H (R x) (R y) = s * K x y)
    (f : Lp ℝ 2 ν) :
    (D f : ℝ → ℝ) =ᵐ[ν] fun r => ∫ t, H r t * f t ∂ν := by
  have hin : ((s • E f : Lp ℝ 2 μ) : ℝ → ℝ) =ᵐ[μ]
      fun y => s * (a y * f (R y)) := by
    filter_upwards [Lp.coeFn_smul s (E f), hE f] with y hy hfy
    simp only [Pi.smul_apply, smul_eq_mul] at hy
    rw [hy, hfy]
  have hg := hG (s • E f)
  rw [← hconj f] at hg
  have halong : (fun x => D f (R x)) =ᵐ[μ]
      fun x => ∫ t, H (R x) t * f t ∂ν := by
    filter_upwards [hE (D f), hg, hK] with x hx hgx hKx
    apply mul_left_cancel₀ (hpos x).ne'
    calc
      a x * D f (R x) = E (D f) x := hx.symm
      _ = ∫ y, K x y * (s * (a y * f (R y))) ∂μ := by
        rw [hgx]
        apply integral_congr_ae
        filter_upwards [hin] with y hy
        rw [hy]
      _ = a x * (∫ t, H (R x) t * f t ∂ν) :=
        (coordinateGauge_kernel_integral hR ha hmeasure f x hKx).symm
  have halong' : (fun x => D f (R x)) =ᵐ[squareDensityMeasure μ a]
      fun x => ∫ t, H (R x) t * f t ∂ν :=
    (withDensity_absolutelyContinuous μ _).ae_eq halong
  have hmap : (D f : ℝ → ℝ) =ᵐ[Measure.map R (squareDensityMeasure μ a)]
      fun r => ∫ t, H r t * f t ∂ν := by
    change ∀ᵐ r ∂Measure.map R (squareDensityMeasure μ a),
      D f r = ∫ t, H r t * f t ∂ν
    rw [ae_iff, hR.map_apply]
    exact ae_iff.mp halong'
  rwa [hmeasure] at hmap

/-- Coordinate pullback and multiplication compose at the level of
representatives without unfolding either Hilbert isometry. -/
theorem l2Equiv_trans_coordinate_mul_ae {μ ν κ : Measure ℝ}
    (E : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν) (F : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 κ)
    (f : Lp ℝ 2 μ) (a R p : ℝ → ℝ)
    (hE : (fun x => E f (R x)) =ᵐ[κ] p)
    (hF : (F (E f) : ℝ → ℝ) =ᵐ[κ] fun x => a x * E f (R x)) :
    ((E.trans F) f : ℝ → ℝ) =ᵐ[κ] fun x => a x * p x := by
  rw [LinearIsometryEquiv.trans_apply]
  filter_upwards [hE, hF] with x hx hy
  exact hy.trans (congrArg (fun t => a x * t) hx)

end ContinuousFlexibility.Analysis
