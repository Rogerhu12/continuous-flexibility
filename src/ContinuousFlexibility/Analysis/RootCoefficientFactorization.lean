module

public import ContinuousFlexibility.Analysis.RootCharacteristicFactor

/-!
# The actual coefficient discriminant at a simple root

The corrected determinant identity gives b²−ac=x a² c₀² on both sides
of the reference root. This identity uses the actual coefficient fields,
not the square of a speed that is only real on one side.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual coefficient discriminant in oriented root coordinates. -/
def rootCoefficientDiscriminant (w : ℝ → ℝ) (z : PolarPoint → ℝ)
    (r σ : ℝ) (p : PolarPoint) : ℝ :=
  polarLinearB w z (rootProfileShift r σ p) ^ 2 -
    polarLinearA w z (rootProfileShift r σ p) *
      polarCorrectedC w z (rootProfileShift r σ p)

/-- The smooth factor to which one actual radial division will apply. -/
def rootCoefficientRadialFactor (wref g w : ℝ → ℝ) (z : PolarPoint → ℝ)
    (r σ : ℝ) (p : PolarPoint) : ℝ :=
  polarLinearA w z (rootProfileShift r σ p) ^ 2 *
    factoredCharacteristicSpeed wref g w z r σ p ^ 2

/-- Cancelling the actual positive discriminant and nonzero Q identifies
the factor without imposing a sign on the root coordinate. -/
theorem rootCoefficientRadialFactor_eq
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ} {r σ : ℝ} {p : PolarPoint}
    (hr : 0 < (rootProfileShift r σ p).1)
    (hw : 0 < wref (rootProfileShift r σ p).1) (hg : 0 < g p.1)
    (hD : 0 < polarDiscriminant w z (rootProfileShift r σ p))
    (hQ : heightQ (profileEnergy w (rootProfileShift r σ p))
      (heightRadial z (rootProfileShift r σ p))
      (angularPartial (heightAngular z) (rootProfileShift r σ p)) ≠ 0) :
    rootCoefficientRadialFactor wref g w z r σ p =
      rootProfileRadicand wref g r σ p.1 /
        polarDiscriminant w z (rootProfileShift r σ p) ^ 2 := by
  have hA := rootProfileRadicand_pos hr hw hg
  unfold rootCoefficientRadialFactor polarLinearA linearRadial polarScale
    factoredCharacteristicSpeed
  rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hD.le,
    inverseDThreeHalves_sq _ hD]
  field_simp [hQ, hD.ne']
  <;> ring

/-- The genuine determinant identity holds through the turning point,
including the side on which the unregularized speed is totalized. -/
theorem rootCoefficientDiscriminant_factorization
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ} {r σ : ℝ} {p : PolarPoint}
    (hw : DifferentiableAt ℝ w (rootProfileShift r σ p).1)
    (hr : 0 < (rootProfileShift r σ p).1)
    (hwref : 0 < wref (rootProfileShift r σ p).1) (hg : 0 < g p.1)
    (hD : 0 < polarDiscriminant w z (rootProfileShift r σ p))
    (hQ : heightQ (profileEnergy w (rootProfileShift r σ p))
      (heightRadial z (rootProfileShift r σ p))
      (angularPartial (heightAngular z) (rootProfileShift r σ p)) ≠ 0)
    (hweq : w (rootProfileShift r σ p).1 = wref (rootProfileShift r σ p).1)
    (hdivide : -deriv w (rootProfileShift r σ p).1 = p.1 * g p.1) :
    rootCoefficientDiscriminant w z r σ p =
      p.1 * rootCoefficientRadialFactor wref g w z r σ p := by
  have hdet := polar_corrected_determinant z hw hr.ne' hD hQ
  have hwr : deriv w (rootProfileShift r σ p).1 = -(p.1 * g p.1) := by
    linarith only [hdivide]
  rw [rootCoefficientRadialFactor_eq hr hwref hg hD hQ]
  calc
    rootCoefficientDiscriminant w z r σ p =
        -(w (rootProfileShift r σ p).1 * deriv w (rootProfileShift r σ p).1 /
          (rootProfileShift r σ p).1) /
            polarDiscriminant w z (rootProfileShift r σ p) ^ 2 := by
      unfold rootCoefficientDiscriminant
      rw [neg_div, ← hdet]
      ring
    _ = _ := by
      rw [hweq, hwr]
      unfold rootProfileRadicand rootProfileShift
      ring

/-- The same factor is genuinely smooth wherever the actual field
denominators and reference radial radicand are positive. -/
theorem contDiffAt_rootCoefficientRadialFactor
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    {r σ : ℝ} {p : PolarPoint}
    (hr : 0 < (rootProfileShift r σ p).1)
    (hwp : 0 < wref (rootProfileShift r σ p).1) (hgp : 0 < g p.1)
    (hD : 0 < polarDiscriminant w z (rootProfileShift r σ p))
    (hQ : 0 < heightQ (profileEnergy w (rootProfileShift r σ p))
      (heightRadial z (rootProfileShift r σ p))
      (angularPartial (heightAngular z) (rootProfileShift r σ p))) :
    ContDiffAt ℝ ∞ (rootCoefficientRadialFactor wref g w z r σ) p := by
  have hshift : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have ha := (contDiffAt_heightLinearCoefficients
    hw.contDiffAt hz.contDiffAt hr.ne' hD hQ.ne').1
  have has : ContDiffAt ℝ ∞
      (fun q => polarLinearA w z (rootProfileShift r σ q)) p := by
    simpa only [Function.comp_def] using ha.comp p hshift.contDiffAt
  have hc := (contDiffAt_factoredCharacteristicField
    hwref hg hw hz hr hwp hgp hD hQ).1
  exact (has.pow 2).mul (hc.pow 2)

end ContinuousFlexibility.Analysis
