module

public import ContinuousFlexibility.Analysis.CanonicalCubicMixed
public import ContinuousFlexibility.Analysis.CanonicalCubicPointwise
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
public import ContinuousFlexibility.Analysis.SmoothCompactIntervalIntegral

/-!
# Mixed cubic-division estimates on a cylinder

Three vanishing radial boundary jets identify the radial quotient with
the cubic Taylor integral.  Commutation of the genuine mixed derivatives
then gives a fixed loss of three radial derivatives, at every mixed order.
The pointwise estimate includes the removable endpoint and has constant
`1 / 6`, independently of the derivative order and the interval length.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Interval

/-- A radial jet can be differentiated in any mixed order by adding its
radial order.  Commutation follows from the actual smooth partials. -/
theorem mixedDerivative_radialJet {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (a b n : ℕ) :
    mixedDerivative a b (mixedDerivative n 0 F) = mixedDerivative (a + n) b F := by
  induction n generalizing a with
  | zero =>
      have hz : mixedDerivative 0 0 F = F := by
        funext p
        simp only [mixedDerivative, iteratedDeriv_zero]
      rw [hz, Nat.add_zero]
  | succ n ih =>
      rw [← radialPartial_mixedDerivative hF n 0]
      funext p
      rw [mixedDerivative_radialPartial isOpen_univ
        (contDiff_mixedDerivative hF n 0).contDiffOn a b (mem_univ p)]
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using congrFun (ih (a + 1)) p

/-- The one-dimensional cubic quotient on each radial slice, with its
prescribed removable value at the origin. -/
def radialCubicQuotient (F : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  cubicQuotient (fun r : ℝ => F (r, p.2)) p.1

private theorem radialSlice_boundaryJets {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (h1 : ∀ θ : ℝ, radialPartial F (0, θ) = 0)
    (h2 : ∀ θ : ℝ, radialPartial (radialPartial F) (0, θ) = 0)
    (θ : ℝ) :
    deriv (fun r : ℝ => F (r, θ)) 0 = 0 ∧
      iteratedDeriv 2 (fun r : ℝ => F (r, θ)) 0 = 0 := by
  have hz : mixedDerivative 0 0 F = F := by
    funext p
    simp only [mixedDerivative, iteratedDeriv_zero]
  have hR : radialPartial F = mixedDerivative 1 0 F := by
    simpa only [hz, Nat.zero_add] using radialPartial_mixedDerivative hF 0 0
  have hRR : radialPartial (radialPartial F) = mixedDerivative 2 0 F := by
    simpa only [← hR] using radialPartial_mixedDerivative hF 1 0
  constructor
  · have h := h1 θ
    rw [hR] at h
    simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one] using h
  · have h := h2 θ
    rw [hRR] at h
    simpa only [mixedDerivative, iteratedDeriv_zero] using h

/-- The radial quotient is the cubic Taylor integral for every radial
value, including zero and negative values. -/
theorem radialCubicQuotient_eq_integral {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (h0 : ∀ θ : ℝ, F (0, θ) = 0)
    (h1 : ∀ θ : ℝ, radialPartial F (0, θ) = 0)
    (h2 : ∀ θ : ℝ, radialPartial (radialPartial F) (0, θ) = 0)
    (p : PolarPoint) :
    radialCubicQuotient F p = (1 / 2 : ℝ) *
      ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * mixedDerivative 3 0 F (t * p.1, p.2) := by
  have hs : ContDiff ℝ ∞ (fun r : ℝ => F (r, p.2)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  obtain ⟨hd1, hd2⟩ := radialSlice_boundaryJets hF h1 h2 p.2
  simpa only [radialCubicQuotient, mixedDerivative, iteratedDeriv_zero] using
    cubicQuotient_eq_integral hs (h0 p.2) hd1 hd2 p.1

/-- Removing the cubic radial zero preserves joint smoothness, including
at the boundary circle.  This permits successive divisions at two ends. -/
theorem contDiff_radialCubicQuotient {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (h0 : ∀ θ : ℝ, F (0, θ) = 0)
    (h1 : ∀ θ : ℝ, radialPartial F (0, θ) = 0)
    (h2 : ∀ θ : ℝ, radialPartial (radialPartial F) (0, θ) = 0) :
    ContDiff ℝ ∞ (radialCubicQuotient F) := by
  have hq : radialCubicQuotient F = fun p : PolarPoint => (1 / 2 : ℝ) *
      ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * mixedDerivative 3 0 F (t * p.1, p.2) :=
    funext (radialCubicQuotient_eq_integral hF h0 h1 h2)
  rw [hq]
  exact contDiff_const.mul (contDiff_scaled_cylinderIntegral
    ((continuous_const.sub continuous_id).pow 2) (contDiff_mixedDerivative hF 3 0))

/-- Exact mixed Taylor formula for radial cubic division.  The loss is
three radial derivatives, independent of both requested orders. -/
theorem mixedDerivative_radialCubicQuotient_eq_integral {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (h0 : ∀ θ : ℝ, F (0, θ) = 0)
    (h1 : ∀ θ : ℝ, radialPartial F (0, θ) = 0)
    (h2 : ∀ θ : ℝ, radialPartial (radialPartial F) (0, θ) = 0)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (radialCubicQuotient F) p =
      (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1,
        (1 - t) ^ 2 * t ^ a * mixedDerivative (a + 3) b F (t * p.1, p.2) := by
  have hq : radialCubicQuotient F = fun q : PolarPoint =>
      ∫ t in (0 : ℝ)..1,
        ((1 / 2 : ℝ) * (1 - t) ^ 2) * mixedDerivative 3 0 F (t * q.1, q.2) := by
    funext q
    rw [radialCubicQuotient_eq_integral hF h0 h1 h2]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hw : Continuous (fun t : ℝ => (1 / 2 : ℝ) * (1 - t) ^ 2) :=
    continuous_const.mul ((continuous_const.sub continuous_id).pow 2)
  rw [hq, mixedDerivative_scaled_cylinderIntegral hw (contDiff_mixedDerivative hF 3 0),
    mixedDerivative_radialJet hF a b 3]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-- Uniform control of the numerator's relevant jet along a radial
segment bounds the quotient jet, including its removable endpoint. -/
theorem abs_mixedDerivative_radialCubicQuotient_le_sixth {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (h0 : ∀ θ : ℝ, F (0, θ) = 0)
    (h1 : ∀ θ : ℝ, radialPartial F (0, θ) = 0)
    (h2 : ∀ θ : ℝ, radialPartial (radialPartial F) (0, θ) = 0)
    (a b : ℕ) {M R : ℝ} {p : PolarPoint}
    (hbound : ∀ r ∈ Icc (0 : ℝ) R, |mixedDerivative (a + 3) b F (r, p.2)| ≤ M)
    (hp : p.1 ∈ Icc (0 : ℝ) R) :
    |mixedDerivative a b (radialCubicQuotient F) p| ≤ M / 6 := by
  rw [mixedDerivative_radialCubicQuotient_eq_integral hF h0 h1 h2]
  exact abs_cubicMoment_le_sixth hbound a hp

end ContinuousFlexibility.Analysis
