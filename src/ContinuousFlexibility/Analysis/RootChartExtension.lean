module

public import ContinuousFlexibility.Analysis.SeeleyPeriodicExtension
public import ContinuousFlexibility.Analysis.RootChartWithin

/-!
# A genuine smooth extension of the root chart

The odd coefficient is periodic; the even angular coordinate is a
degree-one lift. Extend the odd coefficient and the periodic angular
displacement separately by the fixed joint Seeley operator. The radial
power is then formed from the extended coefficient, so smoothness is
claimed precisely where that coefficient is nonzero. On the physical
half-plane the resulting chart is exactly the original root formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def extendedRootOddCoefficient (G : ℝ × ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  seeleyPeriodicExtension (rootOddCoefficient G)

def extendedRootEven (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  seeleyPeriodicExtension (fun q => rootEven G q - q.2) p + p.2

def extendedRootRadialFactor (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (((3 : ℝ) / 2) * extendedRootOddCoefficient G p) ^ (2 / 3 : ℝ)

def extendedRootRadialCoordinate (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * extendedRootRadialFactor G p

def extendedRootEvenOddChart (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (extendedRootRadialCoordinate G p, extendedRootEven G p)

@[simp] theorem extendedRootOddCoefficient_of_nonneg
    (G : ℝ × ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    extendedRootOddCoefficient G p = rootOddCoefficient G p :=
  seeleyPeriodicExtension_of_nonneg _ hp

@[simp] theorem extendedRootEven_of_nonneg
    (G : ℝ × ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    extendedRootEven G p = rootEven G p := by
  rw [extendedRootEven, seeleyPeriodicExtension_of_nonneg _ hp, sub_add_cancel]

theorem extendedRootEvenOddChart_of_nonneg
    (G : ℝ × ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    extendedRootEvenOddChart G p = rootEvenOddChart G p := by
  simp only [extendedRootEvenOddChart, rootEvenOddChart,
    extendedRootRadialCoordinate, rootRadialCoordinate,
    extendedRootRadialFactor, rootRadialFactor,
    extendedRootOddCoefficient_of_nonneg G hp, extendedRootEven_of_nonneg G hp]

private theorem rootEven_displacement_periodic
    {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    (r : ℝ) (hr : 0 ≤ r) :
    Function.Periodic (fun θ => rootEven G (r, θ) - θ) T := by
  intro θ
  change rootEven G (r, θ + T) - (θ + T) = rootEven G (r, θ) - θ
  rw [hperiod r hr θ]
  ring

theorem contDiff_extendedRootOddCoefficient
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {T : ℝ} (hT : T ≠ 0)
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T) :
    ContDiff ℝ ∞ (extendedRootOddCoefficient G) :=
  contDiff_seeleyPeriodicExtension (contDiffOn_rootOddCoefficient hG) hT hperiod

theorem contDiff_extendedRootEven
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {T : ℝ} (hT : T ≠ 0)
    (hperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T) :
    ContDiff ℝ ∞ (extendedRootEven G) := by
  have hd : ContDiffOn ℝ ∞ (fun p => rootEven G p - p.2) seeleyHalfPlane :=
    (contDiffOn_rootEven hG).sub contDiffOn_snd
  exact (contDiff_seeleyPeriodicExtension hd hT
    (rootEven_displacement_periodic hperiod)).add contDiff_snd

/-- The fixed extension respects the original period of the chart. -/
theorem extendedRootEvenOddChart_period
    {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hχ : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφ : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    (r θ : ℝ) :
    extendedRootEvenOddChart G (r, θ + T) =
      extendedRootEvenOddChart G (r, θ) + (0, T) := by
  have hχe :
      seeleyPeriodicExtension (rootOddCoefficient G) (r, θ + T) =
        seeleyPeriodicExtension (rootOddCoefficient G) (r, θ) :=
    seeleyPeriodicExtension_periodic hχ r θ
  have hφe :
      seeleyPeriodicExtension (fun q => rootEven G q - q.2) (r, θ + T) =
        seeleyPeriodicExtension (fun q => rootEven G q - q.2) (r, θ) :=
    seeleyPeriodicExtension_periodic
      (f := fun q => rootEven G q - q.2) (rootEven_displacement_periodic hφ) r θ
  apply Prod.ext
  · change r * (((3 : ℝ) / 2) *
        seeleyPeriodicExtension (rootOddCoefficient G) (r, θ + T)) ^ (2 / 3 : ℝ) =
      r * (((3 : ℝ) / 2) *
        seeleyPeriodicExtension (rootOddCoefficient G) (r, θ)) ^ (2 / 3 : ℝ) + 0
    rw [hχe, add_zero]
  · change seeleyPeriodicExtension (fun q => rootEven G q - q.2) (r, θ + T) + (θ + T) =
      (seeleyPeriodicExtension (fun q => rootEven G q - q.2) (r, θ) + θ) + T
    rw [hφe]
    ring

/-- The new chart is genuinely smooth at a boundary or interior point
where the physical odd coefficient is nonzero. -/
theorem contDiffAt_extendedRootEvenOddChart
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {T : ℝ} (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (hp : p ∈ rootChartHalfPlane) (hχ : rootOddCoefficient G p ≠ 0) :
    ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) p := by
  have heχ : extendedRootOddCoefficient G p ≠ 0 := by
    rwa [extendedRootOddCoefficient_of_nonneg G hp.1]
  have hs : ContDiffAt ℝ ∞ (extendedRootRadialFactor G) p :=
    (contDiffAt_const.mul
      (contDiff_extendedRootOddCoefficient hG hT hχperiod).contDiffAt).rpow_const_of_ne
        (mul_ne_zero (by norm_num : (3 : ℝ) / 2 ≠ 0) heχ)
  exact (contDiffAt_fst.mul hs).prodMk
    (contDiff_extendedRootEven hG hT hφperiod).contDiffAt

/-- The ordinary derivative of the new chart is the actual within
derivative already computed for the physical-side root formula. -/
theorem fderiv_extendedRootEvenOddChart_eq_within
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {T : ℝ} (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (hp : p ∈ rootChartHalfPlane) (hχ : rootOddCoefficient G p ≠ 0) :
    fderiv ℝ (extendedRootEvenOddChart G) p =
      fderivWithin ℝ (rootEvenOddChart G) rootChartHalfPlane p := by
  have hd := ((contDiffAt_extendedRootEvenOddChart hG hT hχperiod hφperiod hp hχ).differentiableAt
    (by simp)).hasFDerivAt
  calc
    _ = fderivWithin ℝ (extendedRootEvenOddChart G) rootChartHalfPlane p :=
      (hd.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_rootChartHalfPlane p hp)).symm
    _ = _ := fderivWithin_congr' (fun q hq => extendedRootEvenOddChart_of_nonneg G hq.1) hp

/-- The same identification holds at every finite jet order. -/
theorem iteratedFDeriv_extendedRootEvenOddChart_eq_within
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {T : ℝ} (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    (n : ℕ) {p : ℝ × ℝ} (hp : p ∈ rootChartHalfPlane) (hχ : rootOddCoefficient G p ≠ 0) :
    iteratedFDeriv ℝ n (extendedRootEvenOddChart G) p =
      iteratedFDerivWithin ℝ n (rootEvenOddChart G) rootChartHalfPlane p := by
  calc
    _ = iteratedFDerivWithin ℝ n (extendedRootEvenOddChart G) rootChartHalfPlane p :=
      (iteratedFDerivWithin_eq_iteratedFDeriv (n := n) uniqueDiffOn_rootChartHalfPlane
        ((contDiffAt_extendedRootEvenOddChart hG hT hχperiod hφperiod hp hχ).of_le (by simp)) hp).symm
    _ = _ := iteratedFDerivWithin_congr
      (fun q hq => extendedRootEvenOddChart_of_nonneg G hq.1) hp n

end ContinuousFlexibility.Analysis
