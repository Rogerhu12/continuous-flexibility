import ContinuousFlexibility.Analysis.CoefficientProbeSineRecovery
import ContinuousFlexibility.Analysis.OffAxisContinuousRecovery

/-!
# A common smooth coefficient field reconstructed from the actual probes

The two removable quotients correct the original mixed and angular
coefficients with their actual signs and constants. The resulting field
is smooth wherever the original field is smooth. On an open region, the
true probe identities identify it with any continuous effective field;
off-axis division is extended to the axes by genuine continuity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def coefficientProbeRecoveredCoefficients (A : SymmetricCoefficients)
    (cross square : PolarPoint → ℝ) : SymmetricCoefficients where
  a := A.a
  b := fun p => A.b p + (1 / 4 : ℝ) * coefficientProbeSineQuotient false cross p
  c := fun p => A.c p - (1 / 8 : ℝ) * coefficientProbeSineQuotient true square p

theorem coefficientProbeRecoveredCoefficients_contDiffAt
    {D : ReferenceData} {A : SymmetricCoefficients} {cross square : PolarPoint → ℝ}
    (hcross : CoefficientProbeFieldRegularity D cross)
    (hsquare : CoefficientProbeFieldRegularity D square) {p : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a p) (hb : ContDiffAt ℝ ∞ A.b p)
    (hc : ContDiffAt ℝ ∞ A.c p) :
    let B := coefficientProbeRecoveredCoefficients A cross square
    ContDiffAt ℝ ∞ B.a p ∧ ContDiffAt ℝ ∞ B.b p ∧ ContDiffAt ℝ ∞ B.c p :=
  ⟨ha, hb.add (contDiffAt_const.mul
    (contDiff_coefficientProbeSineQuotient hcross false).contDiffAt),
    hc.sub (contDiffAt_const.mul
      (contDiff_coefficientProbeSineQuotient hsquare true).contDiffAt)⟩

private theorem coefficientProbeRecovery_scalar
    {b c B C s X Y : ℝ} (hs : s ≠ 0)
    (hX : X = -4 * (b - B) * s) (hY : Y = 8 * (c - C) * s ^ 2) :
    b + (1 / 4 : ℝ) * (X / s) = B ∧
      c - (1 / 8 : ℝ) * (Y / s ^ 2) = C := by
  rw [hX, hY]
  constructor <;> field_simp [hs] <;> ring

theorem coefficientProbeRecoveredCoefficients_eq_offAxis
    {A B : SymmetricCoefficients} {cross square : PolarPoint → ℝ}
    {J : Set ℝ} (hJ : IsOpen J)
    (hcross0 : ∀ r ∈ J, cross (r, 0) = 0 ∧ cross (r, Real.pi / 2) = 0)
    (hsquare0 : ∀ r ∈ J, square (r, 0) = 0 ∧ square (r, Real.pi / 2) = 0)
    {p : PolarPoint} (hp : p.1 ∈ J) (haxis : Real.sin (2 * p.2) ≠ 0)
    (hcross : cross p = -4 * (A.b p - B.b p) * Real.sin (2 * p.2))
    (hsquare : square p = 8 * (A.c p - B.c p) * Real.sin (2 * p.2) ^ 2) :
    let R := coefficientProbeRecoveredCoefficients A cross square
    R.b p = B.b p ∧ R.c p = B.c p := by
  have hx := coefficientProbeSineQuotient_eq_div_on_radial_region
    hJ hcross0 false hp haxis
  have hy := coefficientProbeSineQuotient_eq_div_on_radial_region
    hJ hsquare0 true hp haxis
  simp only [sineFactorOrder, Bool.false_eq_true, ↓reduceIte, pow_one] at hx hy
  change A.b p + (1 / 4 : ℝ) * coefficientProbeSineQuotient false cross p = B.b p ∧
    A.c p - (1 / 8 : ℝ) * coefficientProbeSineQuotient true square p = B.c p
  rw [hx, hy]
  exact coefficientProbeRecovery_scalar haxis hcross hsquare

/-- Only genuine continuity of the effective field is used at the axes.
No regularity of an unrelated stored field is an input. -/
theorem coefficientProbeRecoveredCoefficients_eq_on_open
    {D : ReferenceData} {A B : SymmetricCoefficients} {cross square : PolarPoint → ℝ}
    (hcross : CoefficientProbeFieldRegularity D cross)
    (hsquare : CoefficientProbeFieldRegularity D square)
    {U : Set PolarPoint} (hU : IsOpen U) {J : Set ℝ} (hJ : IsOpen J)
    (hUJ : ∀ p ∈ U, p.1 ∈ J)
    (hcross0 : ∀ r ∈ J, cross (r, 0) = 0 ∧ cross (r, Real.pi / 2) = 0)
    (hsquare0 : ∀ r ∈ J, square (r, 0) = 0 ∧ square (r, Real.pi / 2) = 0)
    (hAb : ContinuousOn A.b U) (hAc : ContinuousOn A.c U)
    (hBb : ContinuousOn B.b U) (hBc : ContinuousOn B.c U)
    (hidentity : ∀ p ∈ U,
      cross p = -4 * (A.b p - B.b p) * Real.sin (2 * p.2) ∧
      square p = 8 * (A.c p - B.c p) * Real.sin (2 * p.2) ^ 2) :
    let R := coefficientProbeRecoveredCoefficients A cross square
    ∀ p ∈ U, R.b p = B.b p ∧ R.c p = B.c p := by
  dsimp only
  intro p hp
  have hRcross : ContinuousAt
      (coefficientProbeRecoveredCoefficients A cross square).b p :=
    (hAb.continuousAt (hU.mem_nhds hp)).add
      (continuousAt_const.mul (contDiff_coefficientProbeSineQuotient hcross false).continuous.continuousAt)
  have hRsquare : ContinuousAt
      (coefficientProbeRecoveredCoefficients A cross square).c p :=
    (hAc.continuousAt (hU.mem_nhds hp)).sub
      (continuousAt_const.mul (contDiff_coefficientProbeSineQuotient hsquare true).continuous.continuousAt)
  have he (q : PolarPoint) (hq : q ∈ U) (haxis : Real.sin (2 * q.2) ≠ 0) :=
    coefficientProbeRecoveredCoefficients_eq_offAxis hJ hcross0 hsquare0 (hUJ q hq) haxis
      (hidentity q hq).1 (hidentity q hq).2
  exact ⟨scalar_eq_of_offAxis_on_open hU hp hRcross
      (hBb.continuousAt (hU.mem_nhds hp)) (fun q hq haxis => (he q hq haxis).1),
    scalar_eq_of_offAxis_on_open hU hp hRsquare
      (hBc.continuousAt (hU.mem_nhds hp)) (fun q hq haxis => (he q hq haxis).2)⟩

end ContinuousFlexibility.Analysis
