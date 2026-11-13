import ContinuousFlexibility.Analysis.PositiveFiberCoordinates
import ContinuousFlexibility.Analysis.TravelStripAngularInverse
import ContinuousFlexibility.Analysis.CircleInverseDerivativeBounds

/-!
# Continuity and perturbation bounds of the actual positive radial inverse

The positive radial interpolation is inverted at fixed angle.  Its joint
continuity in a topological state parameter follows from monotonicity and
surjectivity of the original radial function.  No norm on the state space
and no regularity of a selected inverse is assumed.

The perturbation estimate compares two original forward functions at the
second inverse point.  In particular it preserves a small state factor
already present in the forward difference, and charges just one reciprocal
of the original radial derivative lower bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] {U : Set E}

/-- The literal `positiveFiberRadialInverse` is jointly continuous on
the original state domain. -/
theorem n04PositiveGeometry_radialInverse_continuousOn
    (Y : E → PolarPoint → ℝ)
    (hY : ContinuousOn (fun p : E × PolarPoint => Y p.1 p.2) (U ×ˢ univ))
    (hmono : ∀ z ∈ U, ∀ θ, StrictMono (fun r => Y z (r, θ)))
    (hsurj : ∀ z ∈ U, ∀ θ, Function.Surjective (fun r => Y z (r, θ))) :
    ContinuousOn (fun p : E × PolarPoint => positiveFiberRadialInverse (Y p.1) p.2)
      (U ×ˢ univ) := by
  let F : (E × ℝ) × ℝ → ℝ := fun p => Y p.1.1 (p.2, p.1.2)
  have hF : ContinuousOn F ((U ×ˢ univ) ×ˢ univ) :=
    hY.comp
      (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)).continuousOn
      (fun p hp => ⟨hp.1.1, mem_univ _⟩)
  have hI : ContinuousOn (parameterizedCircleInverse F) ((U ×ˢ univ) ×ˢ univ) :=
    continuousOn_parameterizedCircleInverse_of_strictMono hF
      (fun p hp => hmono p.1 hp.1 p.2)
      (fun p hp => hsurj p.1 hp.1 p.2)
  exact hI.comp
    ((continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst).continuousOn
    (fun p hp => ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩)

/-- Positivity of the actual radial derivative supplies both order and
surjectivity; they are not additional inverse-family assumptions. -/
theorem n04PositiveGeometry_radialInverse_continuousOn_of_lower
    (Y : E → PolarPoint → ℝ)
    (hY : ContinuousOn (fun p : E × PolarPoint => Y p.1 p.2) (U ×ˢ univ))
    {B : ℝ} (hB : 0 < B)
    (hlower : ∀ z ∈ U, ∀ r θ, B ≤ deriv (fun t => Y z (t, θ)) r) :
    ContinuousOn (fun p : E × PolarPoint => positiveFiberRadialInverse (Y p.1) p.2)
      (U ×ˢ univ) :=
  n04PositiveGeometry_radialInverse_continuousOn Y hY
    (fun z hz θ => strictMono_of_deriv_pos (fun r => hB.trans_le (hlower z hz r θ)))
    (fun z hz θ => (bijective_of_deriv_lower_bound hB
      (fun r => hlower z hz r θ)).2)

/-- Combining the actual radial inverse with the already constructed
angular inverse proves joint continuity of the stored whole inverse. -/
theorem n04PositiveGeometry_fiberChartInverse_continuousOn
    (φ Y : E → PolarPoint → ℝ)
    (hY : ContinuousOn (fun p : E × PolarPoint => Y p.1 p.2) (U ×ˢ univ))
    (hangle : ContinuousOn
      (fun p : E × PolarPoint => parameterizedCircleInverse (φ p.1) p.2) (U ×ˢ univ))
    {B : ℝ} (hB : 0 < B)
    (hlower : ∀ z ∈ U, ∀ r θ, B ≤ deriv (fun t => Y z (t, θ)) r) :
    ContinuousOn (fun p : E × PolarPoint => positiveFiberChartInverse (φ p.1) (Y p.1) p.2)
      (U ×ˢ univ) := by
  have hR := n04PositiveGeometry_radialInverse_continuousOn_of_lower Y hY hB hlower
  have hA := hangle.comp
    (continuous_fst.continuousOn.prodMk (hR.prodMk continuous_snd.snd.continuousOn))
    (fun p hp => ⟨hp.1, mem_univ _⟩)
  exact hR.prodMk hA

/-- A scalar inverse difference is controlled by the forward discrepancy
at the second inverse point.  The source and the family may both vary. -/
theorem n04PositiveGeometry_inverse_sub_le_forward_discrepancy
    {F G I J : ℝ → ℝ} {B x y : ℝ} (hB : 0 < B)
    (hlower : ∀ r, B ≤ deriv F r)
    (hFI : F (I x) = x) (hGJ : G (J y) = y) :
    |I x - J y| ≤ B⁻¹ * (|x - y| + |F (J y) - G (J y)|) := by
  have h := mul_abs_sub_le_abs_image_sub_of_deriv_lower_bound hB hlower (I x) (J y)
  rw [hFI] at h
  have htri : |x - F (J y)| ≤ |x - y| + |F (J y) - G (J y)| := by
    calc
      |x - F (J y)| ≤ |x - y| + |y - F (J y)| := abs_sub_le x y (F (J y))
      _ = |x - y| + |F (J y) - G (J y)| := by
        rw [abs_sub_comm y, ← hGJ]
  have hdiv : |I x - J y| ≤ (|x - y| + |F (J y) - G (J y)|) / B := by
    apply (le_div_iff₀ hB).2
    simpa only [mul_comm] using h.trans htri
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- At a fixed canonical point the radial inverse inherits the forward
state difference, with exactly one inverse radial lower bound. -/
theorem n04PositiveGeometry_radialInverse_sub_le_forward_discrepancy
    {Y Z : PolarPoint → ℝ} {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hY : ∀ r θ, B ≤ deriv (fun t => Y (t, θ)) r)
    (hZ : ∀ r θ, C ≤ deriv (fun t => Z (t, θ)) r)
    (p : PolarPoint) :
    |positiveFiberRadialInverse Y p - positiveFiberRadialInverse Z p| ≤
      B⁻¹ * |Y (positiveFiberRadialInverse Z p, p.2) -
        Z (positiveFiberRadialInverse Z p, p.2)| := by
  have hy := Function.rightInverse_invFun
    (bijective_of_deriv_lower_bound hB (fun r => hY r p.2)).2 p.1
  have hz := Function.rightInverse_invFun
    (bijective_of_deriv_lower_bound hC (fun r => hZ r p.2)).2 p.1
  have h := n04PositiveGeometry_inverse_sub_le_forward_discrepancy
    (F := fun r => Y (r, p.2)) (G := fun r => Z (r, p.2))
    (I := Function.invFun (fun r => Y (r, p.2)))
    (J := Function.invFun (fun r => Z (r, p.2))) hB (fun r => hY r p.2) hy hz
  simpa only [sub_self, abs_zero, zero_add, positiveFiberRadialInverse] using h

end ContinuousFlexibility.Analysis
