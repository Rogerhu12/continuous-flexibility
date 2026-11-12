import ContinuousFlexibility.Analysis.N04bRootBoundaryGeometry
import Mathlib.Topology.Order.Basic

/-!
# Regular transport equations for the actual root even and odd fields

The two genuine characteristic first integrals are E minus or plus
x^(3/2) O. Their transport equations imply

  E_r = -d E_theta + x^2 c0 O_theta,
  x O_r + (3/2) O = c0 E_theta - x d O_theta.

These identities involve only smooth fields and integer powers. They
extend to the actual root by continuity. Differentiating them gives a
finite boundary-jet recursion with positive divisor n + 3/2, so higher
root jets need not be introduced as independent data.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (P : N04bRootCoordinateProperties d c₀ β Φ R σ G)

include P

theorem n06_extendedEven_smooth : ContDiff ℝ ∞ (extendedRootEven G) :=
  contDiff_extendedRootEven P.smooth Real.pi_ne_zero (fun r _ θ => P.even_period r θ)

theorem n06_extendedOdd_smooth : ContDiff ℝ ∞ (extendedRootOddCoefficient G) :=
  contDiff_extendedRootOddCoefficient P.smooth Real.pi_ne_zero (fun r _ => P.odd_period r)

omit P in
private theorem n06_hasDerivAt_root_radial_slice
    {f : PolarPoint → ℝ} {x θ : ℝ} (hf : DifferentiableAt ℝ f (x, θ)) :
    HasDerivAt (fun r : ℝ => f (r, θ)) (radialPartial f (x, θ)) x := by
  have hline : HasDerivAt (fun r : ℝ => (r, θ)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x θ)
  have hd := hf.hasFDerivAt.comp_hasDerivAt x hline
  change HasDerivAt (fun r => f (r, θ)) (fderiv ℝ f (x, θ) (1, 0)) x at hd
  exact hd

private theorem n06_radial_characteristic_pair {x θ : ℝ} (hx : 0 < x) :
    radialPartial (rootCharacteristicCoordinate G 1) (x, θ) =
        radialPartial (extendedRootEven G) (x, θ) -
          (((3 : ℝ) / 2) * Real.sqrt x * extendedRootOddCoefficient G (x, θ) +
            x ^ (3 / 2 : ℝ) * radialPartial (extendedRootOddCoefficient G) (x, θ)) ∧
      radialPartial (rootCharacteristicCoordinate G (-1)) (x, θ) =
        radialPartial (extendedRootEven G) (x, θ) +
          (((3 : ℝ) / 2) * Real.sqrt x * extendedRootOddCoefficient G (x, θ) +
            x ^ (3 / 2 : ℝ) * radialPartial (extendedRootOddCoefficient G) (x, θ)) := by
  have hE : HasDerivAt (fun r => extendedRootEven G (r, θ))
      (radialPartial (extendedRootEven G) (x, θ)) x :=
    n06_hasDerivAt_root_radial_slice
      (P.n06_extendedEven_smooth.differentiable (by simp) (x, θ))
  have hO : HasDerivAt (fun r => extendedRootOddCoefficient G (r, θ))
      (radialPartial (extendedRootOddCoefficient G) (x, θ)) x :=
    n06_hasDerivAt_root_radial_slice
      (P.n06_extendedOdd_smooth.differentiable (by simp) (x, θ))
  have hpow : HasDerivAt (fun r : ℝ => r ^ (3 / 2 : ℝ))
      (((3 : ℝ) / 2) * Real.sqrt x) x := by
    have h := (hasDerivAt_id x).rpow_const (p := (3 / 2 : ℝ)) (Or.inl hx.ne')
    convert h using 1 <;> norm_num [Real.sqrt_eq_rpow]
  have hprod := hpow.mul hO
  have hU : HasDerivAt (fun r => rootCharacteristicCoordinate G 1 (r, θ))
      (radialPartial (rootCharacteristicCoordinate G 1) (x, θ)) x :=
    n06_hasDerivAt_root_radial_slice
      ((contDiffAt_rootCharacteristicCoordinate (σ := 1) (x := x) (θ := θ)
        P.smooth hx).differentiableAt (by simp))
  have hV : HasDerivAt (fun r => rootCharacteristicCoordinate G (-1) (r, θ))
      (radialPartial (rootCharacteristicCoordinate G (-1)) (x, θ)) x :=
    n06_hasDerivAt_root_radial_slice
      ((contDiffAt_rootCharacteristicCoordinate (σ := -1) (x := x) (θ := θ)
        P.smooth hx).differentiableAt (by simp))
  have hUgerm : (fun r => rootCharacteristicCoordinate G 1 (r, θ)) =ᶠ[𝓝 x]
      (fun r => extendedRootEven G (r, θ) -
        r ^ (3 / 2 : ℝ) * extendedRootOddCoefficient G (r, θ)) := by
    filter_upwards [Ioi_mem_nhds hx] with r hr
    exact (rootCharacteristicCoordinate_eq_extended_even_odd G (p := (r, θ)) hr).1
  have hVgerm : (fun r => rootCharacteristicCoordinate G (-1) (r, θ)) =ᶠ[𝓝 x]
      (fun r => extendedRootEven G (r, θ) +
        r ^ (3 / 2 : ℝ) * extendedRootOddCoefficient G (r, θ)) := by
    filter_upwards [Ioi_mem_nhds hx] with r hr
    exact (rootCharacteristicCoordinate_eq_extended_even_odd G (p := (r, θ)) hr).2
  exact ⟨hU.unique ((hE.sub hprod).congr_of_eventuallyEq hUgerm),
    hV.unique ((hE.add hprod).congr_of_eventuallyEq hVgerm)⟩

/-- The actual characteristic equations reduce to a smooth regular system
at every positive physical root radius. -/
theorem n06_regular_transport_positive {x θ : ℝ} (hx : 0 < x) :
    radialPartial (extendedRootEven G) (x, θ) =
        -d (x, θ) * angularPartial (extendedRootEven G) (x, θ) +
          x ^ 2 * c₀ (x, θ) * angularPartial (extendedRootOddCoefficient G) (x, θ) ∧
      x * radialPartial (extendedRootOddCoefficient G) (x, θ) +
          ((3 : ℝ) / 2) * extendedRootOddCoefficient G (x, θ) =
        c₀ (x, θ) * angularPartial (extendedRootEven G) (x, θ) -
          x * d (x, θ) * angularPartial (extendedRootOddCoefficient G) (x, θ) := by
  obtain ⟨hUr, hVr⟩ := P.n06_radial_characteristic_pair (θ := θ) hx
  obtain ⟨hUt, hVt⟩ := angularPartial_rootCharacteristicCoordinate_pair
    P.smooth Real.pi_ne_zero (fun r _ => P.odd_period r)
    (fun r _ η => P.even_period r η) (p := (x, θ)) hx
  have hu := P.transport 1 x θ hx
  have hv := P.transport (-1) x θ hx
  rw [hUr, hUt] at hu
  rw [hVr, hVt] at hv
  simp only [rootPhysicalSpeed, one_mul, neg_one_mul] at hu hv
  have hproduct : Real.sqrt x * x ^ (3 / 2 : ℝ) = x ^ 2 := by
    rw [rpow_three_halves_eq_mul_sqrt hx.le]
    calc
      Real.sqrt x * (x * Real.sqrt x) = x * (Real.sqrt x) ^ 2 := by ring
      _ = x ^ 2 := by rw [Real.sq_sqrt hx.le]; ring
  have he : radialPartial (extendedRootEven G) (x, θ) =
      -d (x, θ) * angularPartial (extendedRootEven G) (x, θ) +
        (Real.sqrt x * x ^ (3 / 2 : ℝ)) * c₀ (x, θ) *
          angularPartial (extendedRootOddCoefficient G) (x, θ) := by
    nlinarith only [hu, hv]
  refine ⟨by simpa only [hproduct] using he, ?_⟩
  rw [rpow_three_halves_eq_mul_sqrt hx.le] at hu hv
  have ho : Real.sqrt x *
      (x * radialPartial (extendedRootOddCoefficient G) (x, θ) +
        ((3 : ℝ) / 2) * extendedRootOddCoefficient G (x, θ) -
        c₀ (x, θ) * angularPartial (extendedRootEven G) (x, θ) +
        x * d (x, θ) * angularPartial (extendedRootOddCoefficient G) (x, θ)) = 0 := by
    nlinarith only [hu, hv]
  have hz := (mul_eq_zero.mp ho).resolve_left (Real.sqrt_pos.mpr hx).ne'
  linarith only [hz]

/-- The same regular system holds at the true root by ordinary continuity
of the actual extended fields. No derivative of a totalized odd quotient
on the negative half-line is used. -/
theorem n06_regular_transport_nonnegative
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    {x : ℝ} (hx : 0 ≤ x) (θ : ℝ) :
    radialPartial (extendedRootEven G) (x, θ) =
        -d (x, θ) * angularPartial (extendedRootEven G) (x, θ) +
          x ^ 2 * c₀ (x, θ) * angularPartial (extendedRootOddCoefficient G) (x, θ) ∧
      x * radialPartial (extendedRootOddCoefficient G) (x, θ) +
          ((3 : ℝ) / 2) * extendedRootOddCoefficient G (x, θ) =
        c₀ (x, θ) * angularPartial (extendedRootEven G) (x, θ) -
          x * d (x, θ) * angularPartial (extendedRootOddCoefficient G) (x, θ) := by
  have hEr : ContDiff ℝ ∞ (radialPartial (extendedRootEven G)) :=
    (P.n06_extendedEven_smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hEt : ContDiff ℝ ∞ (angularPartial (extendedRootEven G)) :=
    (P.n06_extendedEven_smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hOr : ContDiff ℝ ∞ (radialPartial (extendedRootOddCoefficient G)) :=
    (P.n06_extendedOdd_smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hOt : ContDiff ℝ ∞ (angularPartial (extendedRootOddCoefficient G)) :=
    (P.n06_extendedOdd_smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hline : Continuous (fun r : ℝ => (r, θ)) := continuous_id.prodMk continuous_const
  have hdline := hd.continuous.comp hline
  have hcline := hc₀.continuous.comp hline
  have hErline := hEr.continuous.comp hline
  have hEtline := hEt.continuous.comp hline
  have hOrline := hOr.continuous.comp hline
  have hOtline := hOt.continuous.comp hline
  have hOline := P.n06_extendedOdd_smooth.continuous.comp hline
  have heclosed : IsClosed {r : ℝ |
      radialPartial (extendedRootEven G) (r, θ) =
        -d (r, θ) * angularPartial (extendedRootEven G) (r, θ) +
          r ^ 2 * c₀ (r, θ) * angularPartial (extendedRootOddCoefficient G) (r, θ)} :=
    isClosed_eq hErline ((hdline.neg.mul hEtline).add
      (((continuous_id.pow 2).mul hcline).mul hOtline))
  have hoclosed : IsClosed {r : ℝ |
      r * radialPartial (extendedRootOddCoefficient G) (r, θ) +
          ((3 : ℝ) / 2) * extendedRootOddCoefficient G (r, θ) =
        c₀ (r, θ) * angularPartial (extendedRootEven G) (r, θ) -
          r * d (r, θ) * angularPartial (extendedRootOddCoefficient G) (r, θ)} :=
    isClosed_eq ((continuous_id.mul hOrline).add (continuous_const.mul hOline))
      ((hcline.mul hEtline).sub ((continuous_id.mul hdline).mul hOtline))
  have heclosure := closure_minimal
    (fun r (hr : r ∈ Ioi (0 : ℝ)) => (P.n06_regular_transport_positive (θ := θ) hr).1)
    heclosed
  have hoclosure := closure_minimal
    (fun r (hr : r ∈ Ioi (0 : ℝ)) => (P.n06_regular_transport_positive (θ := θ) hr).2)
    hoclosed
  rw [closure_Ioi] at heclosure hoclosure
  exact ⟨heclosure hx, hoclosure hx⟩

end N04bRootCoordinateProperties

end ContinuousFlexibility.Analysis
