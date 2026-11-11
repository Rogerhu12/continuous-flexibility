import ContinuousFlexibility.Radial.LogSlopeConnector
import ContinuousFlexibility.Radial.CentralStatementBridges

/-!
# Logarithmic slopes of actual second-mode solutions

The connector argument uses C¹ closeness of the logarithmic slope, not
only convergence of the slope itself.  The second-mode equation supplies
its first derivative.  This file proves that identity for actual radial
functions and applies it to the central model at both ends.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

/-- The logarithmic slope of the height, in the coordinate `y = log r`. -/
def seedLogSlope (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  exp y * deriv u (exp y) / u (exp y)

/-- The logarithmic slope of the profile at the same point. -/
def seedProfileSlope (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  exp y * deriv w (exp y) / w (exp y)

theorem seedLogSlope_log (u : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    seedLogSlope u (log r) = r * deriv u r / u r := by
  simp only [seedLogSlope, exp_log hr]

theorem seedProfileSlope_log (w : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    seedProfileSlope w (log r) = r * deriv w r / w r := by
  simp only [seedProfileSlope, exp_log hr]

/-- Differentiation before using the differential equation. -/
theorem hasDerivAt_seedLogSlope {u : ℝ → ℝ} {y : ℝ}
    (hu : DifferentiableAt ℝ u (exp y))
    (hu' : DifferentiableAt ℝ (deriv u) (exp y))
    (hne : u (exp y) ≠ 0) :
    HasDerivAt (seedLogSlope u)
      (seedLogSlope u y + exp y ^ 2 * deriv (deriv u) (exp y) / u (exp y) -
        seedLogSlope u y ^ 2) y := by
  have he := hasDerivAt_exp y
  have h := (he.mul (hu'.hasDerivAt.comp y he)).div
    (hu.hasDerivAt.comp y he) hne
  apply h.congr_deriv
  simp only [seedLogSlope, Function.comp_apply]
  field_simp
  <;> ring

/-- The second-mode equation determines the derivative of its logarithmic slope. -/
theorem deriv_seedLogSlope_of_radialJacobi {w u : ℝ → ℝ} {y : ℝ}
    (hw : DifferentiableAt ℝ w (exp y))
    (hu : DifferentiableAt ℝ u (exp y))
    (hu' : DifferentiableAt ℝ (deriv u) (exp y))
    (hwne : w (exp y) ≠ 0) (hune : u (exp y) ≠ 0)
    (hode : radialJacobi 4 w u (exp y) = 0) :
    deriv (seedLogSlope u) y =
      (4 - seedLogSlope u y) * seedProfileSlope w y -
        seedLogSlope u y ^ 2 + seedLogSlope u y := by
  rw [(hasDerivAt_seedLogSlope hu hu' hune).deriv]
  have he : exp y ≠ 0 := (exp_pos y).ne'
  have hflux := hw.hasDerivAt.mul hu'.hasDerivAt
  unfold radialJacobi at hode
  rw [hflux.deriv] at hode
  unfold seedLogSlope seedProfileSlope
  field_simp [hwne, hune, he] at hode ⊢
  nlinarith only [hode]

theorem contDiff_seedLogSlope {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Ioi 0))
    (hne : ∀ r : ℝ, 0 < r → u r ≠ 0) :
    ContDiff ℝ ∞ (seedLogSlope u) := by
  have hu' : ContDiffOn ℝ ∞ (deriv u) (Ioi 0) :=
    hu.deriv_of_isOpen isOpen_Ioi (by simp)
  have hmap : MapsTo exp univ (Ioi (0 : ℝ)) := fun y _ => exp_pos y
  have huc : ContDiff ℝ ∞ (fun y : ℝ => u (exp y)) :=
    contDiffOn_univ.mp (hu.comp contDiff_exp.contDiffOn hmap)
  have hdc : ContDiff ℝ ∞ (fun y : ℝ => deriv u (exp y)) :=
    contDiffOn_univ.mp (hu'.comp contDiff_exp.contDiffOn hmap)
  exact (contDiff_exp.mul hdc).div huc (fun y => hne _ (exp_pos y))

theorem contDiffOn_centralKernelHeight :
    ContDiffOn ℝ ∞ centralKernelHeight (Ioi 0) := by
  intro r hr
  have h := contDiffAt_centralKernelHeight (centralModelCoordinate r)
  rw [centralRadius_modelCoordinate hr] at h
  exact h.contDiffWithinAt

theorem contDiff_centralSeedLogSlope :
    ContDiff ℝ ∞ (seedLogSlope centralKernelHeight) :=
  contDiff_seedLogSlope contDiffOn_centralKernelHeight
    (fun r _ => (centralKernelHeight_pos r).ne')

/-- The actual logarithmic derivative, evaluated in the central model coordinate. -/
theorem centralSeedLogSlope_pullback (x : ℝ) :
    seedLogSlope centralKernelHeight (log (centralRadius x)) =
      (centralRadiusA - 2 * x) / Statements.centralUpsilon x := by
  rw [seedLogSlope_log _ (centralRadius_pos x)]
  exact centralKernelHeight_radial_logarithmic_derivative x

theorem centralSeedProfileSlope_pullback (x : ℝ) :
    seedProfileSlope (centralRadialProfile 1) (log (centralRadius x)) =
      (x ^ 2 - centralOscillatorA) / Statements.centralUpsilon x ^ 2 := by
  rw [seedProfileSlope_log _ (centralRadius_pos x)]
  exact centralRadialProfile_radial_logarithmic_derivative x

theorem centralSeedLogSlope_deriv (x : ℝ) :
    deriv (seedLogSlope centralKernelHeight) (log (centralRadius x)) =
      (4 - (centralRadiusA - 2 * x) / Statements.centralUpsilon x) *
          ((x ^ 2 - centralOscillatorA) / Statements.centralUpsilon x ^ 2) -
        ((centralRadiusA - 2 * x) / Statements.centralUpsilon x) ^ 2 +
          (centralRadiusA - 2 * x) / Statements.centralUpsilon x := by
  have hu : ContDiffAt ℝ ∞ centralKernelHeight (exp (log (centralRadius x))) := by
    simpa only [exp_log (centralRadius_pos x)] using contDiffAt_centralKernelHeight x
  have hw : ContDiffAt ℝ ∞ (centralRadialProfile 1) (exp (log (centralRadius x))) := by
    simpa only [exp_log (centralRadius_pos x)] using contDiffAt_centralRadialProfile 1 x
  have hune : centralKernelHeight (exp (log (centralRadius x))) ≠ 0 :=
    (centralKernelHeight_pos _).ne'
  have hwne : centralRadialProfile 1 (exp (log (centralRadius x))) ≠ 0 := by
    rw [exp_log (centralRadius_pos x), centralRadialProfile_pullback]
    positivity
  have hode : radialJacobi 4 (centralRadialProfile 1) centralKernelHeight
      (exp (log (centralRadius x))) = 0 := by
    rw [exp_log (centralRadius_pos x)]
    exact radialJacobi_centralKernel 1 x
  rw [deriv_seedLogSlope_of_radialJacobi
    (hw.differentiableAt (by simp)) (hu.differentiableAt (by simp))
    ((hu.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)) hwne hune hode,
    centralSeedLogSlope_pullback, centralSeedProfileSlope_pullback]

/-- Both limits, with a single statement for the two possible end filters. -/
theorem centralSeedLogSlope_C1_at_end {F : Filter ℝ} {a : ℝ}
    (ha : a ^ 2 = 4)
    (hk : Tendsto (fun x => (centralRadiusA - 2 * x) / Statements.centralUpsilon x)
      F (𝓝 a))
    (hq : Tendsto (fun x => (x ^ 2 - centralOscillatorA) /
      Statements.centralUpsilon x ^ 2) F (𝓝 1)) :
    Tendsto (fun x => seedLogSlope centralKernelHeight (log (centralRadius x))) F (𝓝 a) ∧
    Tendsto (fun x => deriv (seedLogSlope centralKernelHeight) (log (centralRadius x)))
      F (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · simpa only [centralSeedLogSlope_pullback] using hk
  · have h := (((tendsto_const_nhds (x := (4 : ℝ))).sub hk).mul hq).sub (hk.pow 2)
    have hh := h.add hk
    have hzero : (4 - a) * 1 - a ^ 2 + a = 0 := by nlinarith only [ha]
    simpa only [centralSeedLogSlope_deriv, hzero] using hh

theorem centralSeedLogSlope_C1_left :
    Tendsto (fun x => seedLogSlope centralKernelHeight (log (centralRadius x)))
      atBot (𝓝 2) ∧
    Tendsto (fun x => deriv (seedLogSlope centralKernelHeight) (log (centralRadius x)))
      atBot (𝓝 0) := by
  rcases centralRadialContact_statement with
    ⟨_, _, _, _, _, hk, _, hq, _⟩
  exact centralSeedLogSlope_C1_at_end (by norm_num) hk hq

theorem centralSeedLogSlope_C1_right :
    Tendsto (fun x => seedLogSlope centralKernelHeight (log (centralRadius x)))
      atTop (𝓝 (-2)) ∧
    Tendsto (fun x => deriv (seedLogSlope centralKernelHeight) (log (centralRadius x)))
      atTop (𝓝 0) := by
  rcases centralRadialContact_statement with
    ⟨_, _, _, _, _, _, hk, _, hq⟩
  exact centralSeedLogSlope_C1_at_end (by norm_num) hk hq

end ContinuousFlexibility.Radial
