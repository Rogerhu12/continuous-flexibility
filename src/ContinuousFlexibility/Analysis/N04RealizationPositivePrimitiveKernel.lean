import ContinuousFlexibility.Analysis.ParameterizedPositiveReference

/-!
# The existing positive primitive with finite-dimensional parameters

Fixed-interval integration and the moving-endpoint primitive are the
proved compact-parameter operations. This applies them to the same
normalized slope, before composing with any topological state map.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- The literal normalized positive primitive is smooth in any finite
coefficient vector. The endpoints, collar, base value, and mass are fixed. -/
theorem n04Realization_positivePrimitive_finiteParameter_contDiff
    (A : Bool → P × ℝ → ℝ) (hA : ∀ side, ContDiff ℝ ∞ (A side))
    (l r δ v m : ℝ) :
    ContDiff ℝ ∞ (fun p : P × ℝ =>
      v + m * positiveReferenceCoordinate l r δ
        (fun t => A false (p.1, t) / m)
        (fun t => A true (p.1, t) / m) p.2) := by
  let B : Bool → P × ℝ → ℝ := fun side p => A side p / m
  have hB (side : Bool) : ContDiff ℝ ∞ (B side) := (hA side).div_const m
  have hL : ContDiff ℝ ∞ (fun p : P × ℝ => positiveEndpointCutoff l δ p.2) :=
    (contDiff_positiveEndpointCutoff l δ).comp contDiff_snd
  have hR : ContDiff ℝ ∞ (fun p : P × ℝ => positiveEndpointCutoff r δ p.2) :=
    (contDiff_positiveEndpointCutoff r δ).comp contDiff_snd
  have hEnd : ContDiff ℝ ∞ (fun p : P × ℝ =>
      positiveEndpointCutoff l δ p.2 * B false p +
        positiveEndpointCutoff r δ p.2 * B true p) :=
    (hL.mul (hB false)).add (hR.mul (hB true))
  have hMass : ContDiff ℝ ∞ (fun a : P =>
      positiveReferenceEndMass l r δ (fun t => B false (a, t))
        (fun t => B true (a, t))) :=
    contDiff_parametric_intervalIntegral hEnd l r
  have hScale : ContDiff ℝ ∞ (fun a : P =>
      positiveReferenceScale l r δ (fun t => B false (a, t))
        (fun t => B true (a, t))) :=
    (contDiff_const.sub hMass).div_const (positiveReferenceMiddleMass l r δ)
  have hSlope : ContDiff ℝ ∞ (fun p : P × ℝ =>
      positiveReferenceSlope l r δ (fun t => B false (p.1, t))
        (fun t => B true (p.1, t)) p.2) :=
    hEnd.add ((hScale.comp contDiff_fst).mul
      ((contDiff_const.sub hL).sub hR))
  have hPrimitive : ContDiff ℝ ∞ (fun p : P × ℝ =>
      positiveReferenceCoordinate l r δ (fun t => B false (p.1, t))
        (fun t => B true (p.1, t)) p.2) :=
    contDiff_parametric_primitive hSlope l
  exact contDiff_const.add (contDiff_const.mul hPrimitive)

end ContinuousFlexibility.Analysis
