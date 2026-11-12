import ContinuousFlexibility.Analysis.RootAngularProduct
import ContinuousFlexibility.Analysis.CharacteristicRootDensity

/-!
# A genuine smooth height through the root

The apparent interior factor a v/sqrt(ξ) is represented by
a J_root/(Uθ Vθ). The denominator is the smooth angular-product
expression, with positive boundary value hL'². The actual root chart
Jacobian is smooth and positive at the boundary. Their quotient
therefore defines a positive smooth height through the root and agrees
with the interior characteristic normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootHeightFactor (a : ℝ × ℝ → ℝ) (G : ℝ × ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  a p * planeJacobian (extendedRootEvenOddChart G) p / rootAngularProduct G p

def rootSmoothHeight (a : ℝ × ℝ → ℝ) (G : ℝ × ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  (Real.sqrt (rootHeightFactor a G p))⁻¹

theorem contDiffAt_rootHeightFactor
    {G : ℝ × ℝ × ℝ → ℝ} {a : ℝ × ℝ → ℝ} {T : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (ha : ContDiffAt ℝ ∞ a p)
    (hχ : extendedRootOddCoefficient G p ≠ 0) (hB : rootAngularProduct G p ≠ 0) :
    ContDiffAt ℝ ∞ (rootHeightFactor a G) p := by
  have hc := contDiffAt_extendedRootEvenOddChart_of_ne_zero hG hT hχperiod hφperiod hχ
  have hD := hc.fderiv_right (m := ∞) (by simp)
  have h1 : ContDiffAt ℝ ∞
      (fun q => fderiv ℝ (extendedRootEvenOddChart G) q (1, 0)) p :=
    hD.clm_apply contDiffAt_const
  have h2 : ContDiffAt ℝ ∞
      (fun q => fderiv ℝ (extendedRootEvenOddChart G) q (0, 1)) p :=
    hD.clm_apply contDiffAt_const
  have hJ : ContDiffAt ℝ ∞ (planeJacobian (extendedRootEvenOddChart G)) p :=
    (h1.fst.mul h2.snd).sub (h1.snd.mul h2.fst)
  exact (ha.mul hJ).fun_div
    (contDiff_rootAngularProduct hG hT hχperiod hφperiod).contDiffAt hB

theorem contDiffAt_rootSmoothHeight
    {G : ℝ × ℝ × ℝ → ℝ} {a : ℝ × ℝ → ℝ} {T : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (ha : ContDiffAt ℝ ∞ a p)
    (hχ : extendedRootOddCoefficient G p ≠ 0) (hB : rootAngularProduct G p ≠ 0)
    (hα : 0 < rootHeightFactor a G p) :
    ContDiffAt ℝ ∞ (rootSmoothHeight a G) p := by
  have hf := contDiffAt_rootHeightFactor hG hT hχperiod hφperiod ha hχ hB
  have hs : ContDiffAt ℝ ∞ (fun q => Real.sqrt (rootHeightFactor a G q)) p := by
    simpa only [Real.sqrt_eq_rpow] using
      hf.rpow_const_of_ne (p := (1 / 2 : ℝ)) hα.ne'
  exact hs.fun_inv (Real.sqrt_pos.mpr hα).ne'

/-- The actual boundary angular derivative gives the exact smooth factor
and a genuinely positive smooth height at the root. -/
theorem rootSmoothHeight_boundary
    {G : ℝ × ℝ × ℝ → ℝ} {a : ℝ × ℝ → ℝ}
    {hL : ℝ → ℝ} {T θ k : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun η => rootOddCoefficient G (r, η)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ η, rootEven G (r, η + T) = rootEven G (r, η) + T)
    (hzero : ∀ η : ℝ, G (0, 0, η) = hL η)
    (hLderiv : HasDerivAt hL k θ) (hk : 0 < k)
    (hχ : 0 < rootOddCoefficient G (0, θ))
    (ha : ContDiffAt ℝ ∞ a (0, θ)) (ha0 : 0 < a (0, θ)) :
    rootHeightFactor a G (0, θ) = a (0, θ) * rootRadialFactor G (0, θ) / k ∧
      ContDiffAt ℝ ∞ (rootSmoothHeight a G) (0, θ) ∧
      0 < rootSmoothHeight a G (0, θ) ∧
      rootSmoothHeight a G (0, θ) ^ 2 * rootHeightFactor a G (0, θ) = 1 := by
  have heχ : extendedRootOddCoefficient G (0, θ) ≠ 0 := by
    rw [extendedRootOddCoefficient_of_nonneg G (le_refl (0 : ℝ))]
    exact hχ.ne'
  have hB : rootAngularProduct G (0, θ) ≠ 0 := by
    rw [rootAngularProduct_zero hG hT hφperiod hzero hLderiv]
    exact pow_ne_zero 2 hk.ne'
  have hαeq : rootHeightFactor a G (0, θ) =
      a (0, θ) * rootRadialFactor G (0, θ) / k := by
    rw [rootHeightFactor,
      planeJacobian_extendedRootEvenOddChart_zero hG hT hχperiod hφperiod hzero hLderiv hχ.ne',
      rootAngularProduct_zero hG hT hφperiod hzero hLderiv]
    field_simp [hk.ne']
    <;> ring
  have hα : 0 < rootHeightFactor a G (0, θ) := by
    rw [hαeq]
    exact div_pos (mul_pos ha0 (rootRadialFactor_pos hχ)) hk
  refine ⟨hαeq, contDiffAt_rootSmoothHeight hG hT hχperiod hφperiod ha heχ hB hα,
    inv_pos.mpr (Real.sqrt_pos.mpr hα), ?_⟩
  rw [rootSmoothHeight, inv_pow, Real.sq_sqrt hα.le]
  exact inv_mul_cancel₀ hα.ne'

/-- On the physical interior the smooth quotient is the exact factor
from the characteristic normalization, using the actual transport
equations and the actual scaled radial differential. -/
theorem rootHeightFactor_eq_characteristicFactor
    {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ} (a : ℝ × ℝ → ℝ)
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (hp : 0 < p.1) (hχ : 0 < rootOddCoefficient G p) {d v : ℝ}
    (hUr : radialPartial (rootCharacteristicCoordinate G 1) p =
      -(d + v) * angularPartial (rootCharacteristicCoordinate G 1) p)
    (hVr : radialPartial (rootCharacteristicCoordinate G (-1)) p =
      -(d - v) * angularPartial (rootCharacteristicCoordinate G (-1)) p)
    (hUθ : angularPartial (rootCharacteristicCoordinate G 1) p ≠ 0)
    (hVθ : angularPartial (rootCharacteristicCoordinate G (-1)) p ≠ 0) :
    rootHeightFactor a G p = a p * v * extendedRootScale G p := by
  have hU : DifferentiableAt ℝ (rootCharacteristicCoordinate G 1) p :=
    (contDiffAt_rootCharacteristicCoordinate (σ := 1) (θ := p.2) hG hp).differentiableAt (by simp)
  have hV : DifferentiableAt ℝ (rootCharacteristicCoordinate G (-1)) p :=
    (contDiffAt_rootCharacteristicCoordinate (σ := -1) (θ := p.2) hG hp).differentiableAt (by simp)
  have hJ := planeJacobian_of_scaled_radial_differential
    (fderiv_extendedRootEvenOddChart_scaled_travel hG hT hχperiod hp hχ (1, 0))
    (fderiv_extendedRootEvenOddChart_scaled_travel hG hT hχperiod hp hχ (0, 1))
  rw [planeJacobian_characteristicTravelChart hU hV hUr hVr] at hJ
  rw [rootHeightFactor, hJ, rootAngularProduct_eq_characteristicProduct hG hT hχperiod hφperiod hp]
  field_simp [hUθ, hVθ]
  <;> ring

theorem rootSmoothHeight_eq_characteristicRootHeight
    {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (A : SymmetricCoefficients) (d v : ℝ × ℝ → ℝ)
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (hp : 0 < p.1) (hχ : 0 < rootOddCoefficient G p)
    (hUr : radialPartial (rootCharacteristicCoordinate G 1) p =
      -(d p + v p) * angularPartial (rootCharacteristicCoordinate G 1) p)
    (hVr : radialPartial (rootCharacteristicCoordinate G (-1)) p =
      -(d p - v p) * angularPartial (rootCharacteristicCoordinate G (-1)) p)
    (hUθ : angularPartial (rootCharacteristicCoordinate G 1) p ≠ 0)
    (hVθ : angularPartial (rootCharacteristicCoordinate G (-1)) p ≠ 0) :
    rootSmoothHeight A.a G p =
      characteristicRootHeight A v (extendedRootScale G) p := by
  unfold rootSmoothHeight characteristicRootHeight
  rw [rootHeightFactor_eq_characteristicFactor A.a hG hT hχperiod hφperiod hp hχ hUr hVr hUθ hVθ]

end ContinuousFlexibility.Analysis
