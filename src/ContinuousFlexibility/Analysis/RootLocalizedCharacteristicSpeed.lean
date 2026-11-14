module

public import ContinuousFlexibility.Analysis.N01RootFieldLocalization
public import ContinuousFlexibility.Analysis.RootPhysicalCharacteristicFlow

/-!
# The localized root field is the actual oriented characteristic speed

The coefficient determinant and height compatibility identify the stored
quadratic-form speed directly. This includes the root itself and uses
the true positive square-root factor. No corrected-operator regularity
certificate or characteristic-flow identification is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem rootPhysicalSpeed_eq_oriented_polarMinus
    {wref g w : ℝ → ℝ} {Z : PolarPoint → ℝ} {r σ : ℝ} {p : PolarPoint}
    (hw : DifferentiableAt ℝ w (rootProfileShift r σ p).1)
    (hZ : ContDiffAt ℝ 2 Z (rootProfileShift r σ p))
    (hx : 0 ≤ p.1) (hr : 0 < (rootProfileShift r σ p).1)
    (hwref : 0 < wref (rootProfileShift r σ p).1) (hg : 0 < g p.1)
    (hD : 0 < polarDiscriminant w Z (rootProfileShift r σ p))
    (hQ : 0 < heightQ (profileEnergy w (rootProfileShift r σ p))
      (heightRadial Z (rootProfileShift r σ p))
      (angularPartial (heightAngular Z) (rootProfileShift r σ p)))
    (hweq : w (rootProfileShift r σ p).1 = wref (rootProfileShift r σ p).1)
    (hdivide : -deriv w (rootProfileShift r σ p).1 = p.1 * g p.1) :
    rootPhysicalSpeed (orientedCharacteristicDrift w Z r σ)
        (factoredCharacteristicSpeed wref g w Z r σ) (-σ) p =
      σ * minusCharacteristicSpeed
        ⟨polarLinearA w Z, polarLinearB w Z, polarCorrectedC w Z⟩
        (rootProfileShift r σ p) := by
  let y := rootProfileShift r σ p
  let a := polarLinearA w Z y
  let c := factoredCharacteristicSpeed wref g w Z r σ p
  have ha : 0 < a := mul_pos hQ (inverseDThreeHalves_pos _ hD)
  have hc : 0 < c := factoredCharacteristicSpeed_pos hr hwref hg hD hQ
  have hfactor : polarLinearB w Z y ^ 2 - a * polarCorrectedC w Z y =
      p.1 * (a * c) ^ 2 := by
    have hh := rootCoefficientDiscriminant_factorization hw hr hwref hg hD
      hQ.ne' hweq hdivide
    change rootCoefficientDiscriminant w Z r σ p = _
    rw [hh]
    dsimp only [rootCoefficientRadialFactor, a, c, y]
    ring
  have hcompat := polarLinearA_mul_characteristicDrift hZ hr.ne' hQ.ne'
  have hdrift : polarLinearB w Z y / a = characteristicDrift w Z y := by
    apply (div_eq_iff ha.ne').mpr
    exact hcompat.symm.trans (mul_comm _ _)
  have hsqrt : Real.sqrt (polarLinearB w Z y ^ 2 - a * polarCorrectedC w Z y) / a =
      Real.sqrt p.1 * c := by
    rw [hfactor, Real.sqrt_mul hx, Real.sqrt_sq (mul_nonneg ha.le hc.le)]
    field_simp [ha.ne']
    <;> ring
  change orientedCharacteristicDrift w Z r σ p + (-σ) * Real.sqrt p.1 * c =
    σ * (polarLinearB w Z y / a -
      Real.sqrt (polarLinearB w Z y ^ 2 - a * polarCorrectedC w Z y) / a)
  rw [hdrift, hsqrt]
  dsimp only [orientedCharacteristicDrift, y]
  ring

/-- A single fixed clamp agrees with the actual physical field on its
inner closed quarter. The orientation is shared by both endpoints. -/
theorem rootPhysicalSpeed_localization_eq_oriented_polarMinus
    {wref g w : ℝ → ℝ} {Z : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hZ : ContDiff ℝ ∞ Z)
    {r σ R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions wref g w Z r σ R)
    {p : PolarPoint} (hp : p.1 ∈ Icc (0 : ℝ) (R / 4)) :
    rootPhysicalSpeed
        (rootFieldLocalization (orientedCharacteristicDrift w Z r σ) hR)
        (rootFieldLocalization (factoredCharacteristicSpeed wref g w Z r σ) hR)
        (-σ) p =
      σ * minusCharacteristicSpeed
        ⟨polarLinearA w Z, polarLinearB w Z, polarCorrectedC w Z⟩
        (rootProfileShift r σ p) := by
  have hpinner : p ∈ Ioo (-(R / 2)) (R / 2) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hp.1, hp.2]
  have hpouter : p ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hp.1, hp.2]
  obtain ⟨hr, hwref, hg, hD, hQ, hweq, hdivide⟩ := hstrip p hpouter
  have hd := rootFieldLocalization_eqOn
    (F := orientedCharacteristicDrift w Z r σ) hR hpinner
  have hc := rootFieldLocalization_eqOn
    (F := factoredCharacteristicSpeed wref g w Z r σ) hR hpinner
  have heq : rootPhysicalSpeed
      (rootFieldLocalization (orientedCharacteristicDrift w Z r σ) hR)
      (rootFieldLocalization (factoredCharacteristicSpeed wref g w Z r σ) hR)
      (-σ) p = rootPhysicalSpeed (orientedCharacteristicDrift w Z r σ)
      (factoredCharacteristicSpeed wref g w Z r σ) (-σ) p := by
    simp only [rootPhysicalSpeed, hd, hc]
  exact heq.trans (rootPhysicalSpeed_eq_oriented_polarMinus
    (hw.differentiable (by simp) _) (hZ.contDiffAt.of_le (by simp))
    hp.1 hr hwref hg hD hQ hweq hdivide)

end ContinuousFlexibility.Analysis
