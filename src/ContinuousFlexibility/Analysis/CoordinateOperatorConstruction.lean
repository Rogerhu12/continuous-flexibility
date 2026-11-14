module

public import ContinuousFlexibility.Analysis.CoordinateDivergenceIdentity
public import ContinuousFlexibility.Analysis.PrincipalDensityBoundaryJets

/-!
# Explicit coefficient and potential fields for an actual coordinate map

The canonical fields are defined by the physical principal density composed
with an actual inverse chart. Their regularity and full operator identity
are consequences of these formulas and the local inverse identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- The explicit canonical coefficients, as actual functions. -/
def inverseChartPrincipalCoefficients (A : SymmetricCoefficients)
    (F G : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) : SymmetricCoefficients where
  a p := (coordinatePrincipalDensity A F h).a (G p)
  b p := (coordinatePrincipalDensity A F h).b (G p)
  c p := (coordinatePrincipalDensity A F h).c (G p)

/-- The potential before the canonical elliptic/hyperbolic type sign. -/
def inverseChartPotential (A : SymmetricCoefficients)
    (F G : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  h (G p) * divergenceOperator A h (G p) / |planeJacobian F (G p)|

/-- The explicit formulas give the full actual coordinate operator,
without assuming a transformed operator identity or coefficient jets. -/
theorem coordinateOperator_explicit_fields
    {A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    {h W : PolarPoint → ℝ} {x : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a x) (hb : ContDiffAt ℝ ∞ A.b x)
    (hc : ContDiffAt ℝ ∞ A.c x)
    (hF : ContDiffAt ℝ ∞ F x) (hG : ContDiffAt ℝ ∞ G (F x))
    (hh : ContDiffAt ℝ ∞ h x) (hW : ContDiff ℝ ∞ W)
    (hJ : planeJacobian F x ≠ 0)
    (hInverse : ∀ᶠ y in 𝓝 x, G (F y) = y) :
    h x * divergenceOperator A (fun y => h y * W (F y)) x /
        |planeJacobian F x| =
      divergenceOperator (inverseChartPrincipalCoefficients A F G h) W (F x) +
        inverseChartPotential A F G h (F x) * W (F x) := by
  have hi : G (F x) = x := hInverse.self_of_nhds
  have hd := contDiffAt_coordinatePrincipalDensity ha hb hc hF hh hJ
  have haG : ContDiffAt ℝ ∞ (coordinatePrincipalDensity A F h).a (G (F x)) := by
    simpa only [hi] using hd.1
  have hbG : ContDiffAt ℝ ∞ (coordinatePrincipalDensity A F h).b (G (F x)) := by
    simpa only [hi] using hd.2.1
  have hcG : ContDiffAt ℝ ∞ (coordinatePrincipalDensity A F h).c (G (F x)) := by
    simpa only [hi] using hd.2.2
  have hBa : DifferentiableAt ℝ (inverseChartPrincipalCoefficients A F G h).a (F x) :=
    (haG.comp (F x) hG).differentiableAt (by simp)
  have hBb : DifferentiableAt ℝ (inverseChartPrincipalCoefficients A F G h).b (F x) :=
    (hbG.comp (F x) hG).differentiableAt (by simp)
  have hBc : DifferentiableAt ℝ (inverseChartPrincipalCoefficients A F G h).c (F x) :=
    (hcG.comp (F x) hG).differentiableAt (by simp)
  have hDensity : ∀ᶠ y in 𝓝 x,
      (inverseChartPrincipalCoefficients A F G h).a (F y) =
        (coordinatePrincipalDensity A F h).a y ∧
      (inverseChartPrincipalCoefficients A F G h).b (F y) =
        (coordinatePrincipalDensity A F h).b y ∧
      (inverseChartPrincipalCoefficients A F G h).c (F y) =
        (coordinatePrincipalDensity A F h).c y := by
    filter_upwards [hInverse] with y hy
    simp only [inverseChartPrincipalCoefficients, hy, and_self]
  have he := heightCoordinateOperator_of_density
    (ha.differentiableAt (by simp)) (hb.differentiableAt (by simp))
    (hc.differentiableAt (by simp)) (hF.of_le (by simp)) (hh.of_le (by simp))
    hBa hBb hBc hW hJ hDensity
  simpa only [inverseChartPotential, hi] using he

end ContinuousFlexibility.Analysis
