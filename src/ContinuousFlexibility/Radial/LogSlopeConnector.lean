import ContinuousFlexibility.Radial.Gauge
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Joining by a prescribed logarithmic slope

Section 6, equation `eq:rad-eq-sp1` of the manuscript
(`06-global-reference-inverse.tex`, "Joining the distinguished solution first").
On the positive half-line put `y = log r`, `w = r e^f`, and prescribe the
logarithmic slope `k = φ_y / φ` of a positive second-mode solution `φ`.  Then
`L₂ φ = (w φ')' - 4 w' φ / r = 0` holds exactly when
`f_y = (k² + k_y - 4) / (4 - k)`, and `1 + f_y = (k² - k + k_y) / (4 - k)`.

This file constructs `f` and `log φ` as primitives, and proves that the
resulting `w, φ` are smooth and positive on `(0, ∞)` and satisfy
`radialJacobi 4 w φ = 0` there.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Filter Set
open scoped Topology ContDiff

/-- The prescribed logarithmic derivative `f_y = (k² + k_y - 4) / (4 - k)`. -/
def connectorSlope (k : ℝ → ℝ) (y : ℝ) : ℝ :=
  (k y ^ 2 + deriv k y - 4) / (4 - k y)

/-- The logarithmic profile `f`, with `f(y₀) = f₀`. -/
def connectorLogProfile (k : ℝ → ℝ) (y₀ f₀ : ℝ) (y : ℝ) : ℝ :=
  f₀ + ∫ t in y₀..y, connectorSlope k t

/-- The logarithm `log φ` of the solution, with value `κ₀` at `y₀`. -/
def connectorLogHeight (k : ℝ → ℝ) (y₀ κ₀ : ℝ) (y : ℝ) : ℝ :=
  κ₀ + ∫ t in y₀..y, k t

/-- The profile `w(r) = r e^{f(log r)}`. -/
def connectorProfile (k : ℝ → ℝ) (y₀ f₀ : ℝ) (r : ℝ) : ℝ :=
  r * Real.exp (connectorLogProfile k y₀ f₀ (Real.log r))

/-- The second-mode solution `φ(r) = e^{(log φ)(log r)}`. -/
def connectorHeight (k : ℝ → ℝ) (y₀ κ₀ : ℝ) (r : ℝ) : ℝ :=
  Real.exp (connectorLogHeight k y₀ κ₀ (Real.log r))

private theorem primitive_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (a y : ℝ) :
    HasDerivAt (fun y => ∫ t in a..y, g t) (g y) y :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

private theorem primitive_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    ContDiff ℝ ∞ (fun y => ∫ t in a..y, g t) := by
  have hd := primitive_hasDerivAt hg.continuous a
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  rw [funext fun x => (hd x).deriv]
  exact hg

theorem connectorSlope_contDiff {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (hk4 : ∀ y, k y < 4) :
    ContDiff ℝ ∞ (connectorSlope k) := by
  have hk' : ContDiff ℝ ∞ (deriv k) := (contDiff_infty_iff_deriv.mp hk).2
  exact (((hk.pow 2).add hk').sub contDiff_const).div (contDiff_const.sub hk)
    (fun y => (sub_pos.2 (hk4 y)).ne')

/-- `1 + f_y = (k² - k + k_y) / (4 - k)`. -/
theorem one_add_connectorSlope (k : ℝ → ℝ) {y : ℝ} (hk4 : k y < 4) :
    1 + connectorSlope k y = (k y ^ 2 - k y + deriv k y) / (4 - k y) := by
  have hne : 4 - k y ≠ 0 := (sub_pos.2 hk4).ne'
  rw [connectorSlope, eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
  ring

theorem hasDerivAt_connectorLogProfile {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) (y₀ f₀ y : ℝ) :
    HasDerivAt (connectorLogProfile k y₀ f₀) (connectorSlope k y) y :=
  (primitive_hasDerivAt (connectorSlope_contDiff hk hk4).continuous y₀ y).const_add f₀

theorem hasDerivAt_connectorLogHeight {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (y₀ κ₀ y : ℝ) :
    HasDerivAt (connectorLogHeight k y₀ κ₀) (k y) y :=
  (primitive_hasDerivAt hk.continuous y₀ y).const_add κ₀

theorem connectorLogProfile_contDiff {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) (y₀ f₀ : ℝ) :
    ContDiff ℝ ∞ (connectorLogProfile k y₀ f₀) :=
  contDiff_const.add (primitive_contDiff (connectorSlope_contDiff hk hk4) y₀)

theorem connectorLogHeight_contDiff {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (y₀ κ₀ : ℝ) :
    ContDiff ℝ ∞ (connectorLogHeight k y₀ κ₀) :=
  contDiff_const.add (primitive_contDiff hk y₀)

/-! ### Positivity and smoothness -/

theorem connectorProfile_pos (k : ℝ → ℝ) (y₀ f₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < connectorProfile k y₀ f₀ r :=
  mul_pos hr (Real.exp_pos _)

theorem connectorHeight_pos (k : ℝ → ℝ) (y₀ κ₀ r : ℝ) :
    0 < connectorHeight k y₀ κ₀ r :=
  Real.exp_pos _

private theorem Ioi_subset_compl_zero : Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := by
  intro x hx
  simp only [mem_compl_iff, mem_singleton_iff]
  exact (mem_Ioi.mp hx).ne'

theorem connectorProfile_contDiffOn {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) (y₀ f₀ : ℝ) :
    ContDiffOn ℝ ∞ (connectorProfile k y₀ f₀) (Ioi 0) := by
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) :=
    Real.contDiffOn_log.mono Ioi_subset_compl_zero
  exact contDiffOn_id.mul
    ((connectorLogProfile_contDiff hk hk4 y₀ f₀).comp_contDiffOn hlog).exp

theorem connectorHeight_contDiffOn {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (y₀ κ₀ : ℝ) :
    ContDiffOn ℝ ∞ (connectorHeight k y₀ κ₀) (Ioi 0) := by
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) :=
    Real.contDiffOn_log.mono Ioi_subset_compl_zero
  exact ((connectorLogHeight_contDiff hk y₀ κ₀).comp_contDiffOn hlog).exp

/-! ### First derivatives -/

/-- `φ_r = k φ / r`. -/
theorem hasDerivAt_connectorHeight {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (y₀ κ₀ : ℝ)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (connectorHeight k y₀ κ₀)
      (k (Real.log r) * connectorHeight k y₀ κ₀ r / r) r := by
  have h := ((hasDerivAt_connectorLogHeight hk y₀ κ₀ (Real.log r)).comp r
    (Real.hasDerivAt_log hr.ne')).exp
  refine h.congr_deriv ?_
  simp only [connectorHeight, Function.comp_apply]
  ring

/-- `w_r = e^f (1 + f_y) = e^f (k² - k + k_y) / (4 - k)`. -/
theorem hasDerivAt_connectorProfile {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) (y₀ f₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (connectorProfile k y₀ f₀)
      (Real.exp (connectorLogProfile k y₀ f₀ (Real.log r)) *
        ((k (Real.log r) ^ 2 - k (Real.log r) + deriv k (Real.log r)) /
          (4 - k (Real.log r)))) r := by
  have h := (hasDerivAt_id' r).mul
    ((hasDerivAt_connectorLogProfile hk hk4 y₀ f₀ (Real.log r)).comp r
      (Real.hasDerivAt_log hr.ne')).exp
  refine h.congr_deriv ?_
  rw [← one_add_connectorSlope k (hk4 _)]
  simp only [Function.comp_apply]
  linear_combination
    (Real.exp (connectorLogProfile k y₀ f₀ (Real.log r)) * connectorSlope k (Real.log r)) *
      mul_inv_cancel₀ hr.ne'

theorem deriv_connectorProfile_pos {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) (y₀ f₀ : ℝ) {r : ℝ} (hr : 0 < r)
    (hpos : 0 < k (Real.log r) ^ 2 - k (Real.log r) + deriv k (Real.log r)) :
    0 < deriv (connectorProfile k y₀ f₀) r := by
  rw [(hasDerivAt_connectorProfile hk hk4 y₀ f₀ hr).deriv]
  exact mul_pos (Real.exp_pos _) (div_pos hpos (sub_pos.2 (hk4 _)))

/-- `r w_r / w = 1 + f_y`. -/
theorem connectorProfile_logDeriv {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) (y₀ f₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    r * deriv (connectorProfile k y₀ f₀) r / connectorProfile k y₀ f₀ r =
      1 + connectorSlope k (Real.log r) := by
  rw [(hasDerivAt_connectorProfile hk hk4 y₀ f₀ hr).deriv,
    ← one_add_connectorSlope k (hk4 _), connectorProfile]
  have hE := (Real.exp_pos (connectorLogProfile k y₀ f₀ (Real.log r))).ne'
  field_simp

/-! ### The second-mode equation -/

/-- The main identity: `(w φ')' - 4 w' φ / r = 0` on `(0, ∞)`. -/
theorem radialJacobi_connector {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) (y₀ f₀ κ₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    radialJacobi 4 (connectorProfile k y₀ f₀) (connectorHeight k y₀ κ₀) r = 0 := by
  set F := connectorLogProfile k y₀ f₀ with hFdef
  set G := connectorLogHeight k y₀ κ₀ with hGdef
  have hEq : (fun t => connectorProfile k y₀ f₀ t * deriv (connectorHeight k y₀ κ₀) t)
      =ᶠ[𝓝 r] (fun t => Real.exp ((F ∘ Real.log) t) * (k ∘ Real.log) t *
        Real.exp ((G ∘ Real.log) t)) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    have ht' : 0 < t := ht
    rw [(hasDerivAt_connectorHeight hk y₀ κ₀ ht').deriv]
    simp only [connectorProfile, connectorHeight, Function.comp_apply]
    rw [← hFdef, ← hGdef]
    linear_combination
      (Real.exp (F (Real.log t)) * k (Real.log t) * Real.exp (G (Real.log t))) *
        mul_inv_cancel₀ ht'.ne'
  have hlog := Real.hasDerivAt_log hr.ne'
  have hE := ((hasDerivAt_connectorLogProfile hk hk4 y₀ f₀ (Real.log r)).comp r hlog).exp
  have hK := (hk.differentiable (by simp) (Real.log r)).hasDerivAt.comp r hlog
  have hP := ((hasDerivAt_connectorLogHeight hk y₀ κ₀ (Real.log r)).comp r hlog).exp
  have hh := (hE.mul hK).mul hP
  unfold radialJacobi
  have hd := hh.congr_of_eventuallyEq hEq
  rw [hd.deriv, (hasDerivAt_connectorProfile hk hk4 y₀ f₀ hr).deriv]
  simp only [connectorHeight, connectorSlope, Function.comp_apply, Pi.mul_apply]
  rw [← hFdef, ← hGdef]
  have hq : (4 - k (Real.log r)) * (4 - k (Real.log r))⁻¹ = 1 :=
    mul_inv_cancel₀ (sub_pos.2 (hk4 _)).ne'
  linear_combination
    (-(Real.exp (F (Real.log r)) * Real.exp (G (Real.log r)) * r⁻¹ *
      (deriv k (Real.log r) + k (Real.log r) ^ 2))) * hq

/-! ### Exact cones -/

/-- If `k ≡ a` with `a² = 4` on an open interval, the slope `f_y` vanishes there. -/
theorem connectorSlope_eq_zero_of_const {k : ℝ → ℝ} {y₁ y₂ a : ℝ}
    (hka : ∀ y ∈ Ioo y₁ y₂, k y = a) (ha : a ^ 2 = 4) {y : ℝ} (hy : y ∈ Ioo y₁ y₂) :
    connectorSlope k y = 0 := by
  have hev : k =ᶠ[𝓝 y] fun _ => a :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hy.1 hy.2) hka
  have hd : deriv k y = 0 := by rw [hev.deriv_eq, deriv_const]
  rw [connectorSlope, hd, hka y hy, ha]
  simp

/-- On a log-interval where `k ≡ a`, `a² = 4`, the profile is an exact cone `w = c r`. -/
theorem connectorProfile_eq_cone_of_const {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) {y₁ y₂ a : ℝ}
    (hka : ∀ y ∈ Ioo y₁ y₂, k y = a) (ha : a ^ 2 = 4) (y₀ f₀ : ℝ)
    {y₃ : ℝ} (hy₃ : y₃ ∈ Ioo y₁ y₂) {r : ℝ} (hr : Real.log r ∈ Ioo y₁ y₂) :
    connectorProfile k y₀ f₀ r =
      Real.exp (connectorLogProfile k y₀ f₀ y₃) * r := by
  have hzero : ∀ y ∈ Ioo y₁ y₂, connectorSlope k y = 0 :=
    fun y hy => connectorSlope_eq_zero_of_const hka ha hy
  have hsub : uIcc y₃ (Real.log r) ⊆ Ioo y₁ y₂ :=
    (ordConnected_Ioo).uIcc_subset hy₃ hr
  have hint : (∫ t in y₃..Real.log r, connectorSlope k t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
      (fun t ht => hzero t (hsub ht))]
    simp
  have hcont := (connectorSlope_contDiff hk hk4).continuous
  have hdiff : connectorLogProfile k y₀ f₀ (Real.log r) =
      connectorLogProfile k y₀ f₀ y₃ := by
    have h := intervalIntegral.integral_interval_sub_left
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) y₀ (Real.log r))
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) y₀ y₃)
    rw [hint] at h
    simp only [connectorLogProfile]
    linarith
  rw [connectorProfile, hdiff, mul_comm]

theorem connectorProfile_eq_cone_of_two {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) {y₁ y₂ : ℝ}
    (hk2 : ∀ y ∈ Ioo y₁ y₂, k y = 2) (y₀ f₀ : ℝ)
    {y₃ : ℝ} (hy₃ : y₃ ∈ Ioo y₁ y₂) {r : ℝ} (hr : Real.log r ∈ Ioo y₁ y₂) :
    connectorProfile k y₀ f₀ r =
      Real.exp (connectorLogProfile k y₀ f₀ y₃) * r :=
  connectorProfile_eq_cone_of_const hk hk4 hk2 (by norm_num) y₀ f₀ hy₃ hr

theorem connectorProfile_eq_cone_of_neg_two {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hk4 : ∀ y, k y < 4) {y₁ y₂ : ℝ}
    (hk2 : ∀ y ∈ Ioo y₁ y₂, k y = -2) (y₀ f₀ : ℝ)
    {y₃ : ℝ} (hy₃ : y₃ ∈ Ioo y₁ y₂) {r : ℝ} (hr : Real.log r ∈ Ioo y₁ y₂) :
    connectorProfile k y₀ f₀ r =
      Real.exp (connectorLogProfile k y₀ f₀ y₃) * r :=
  connectorProfile_eq_cone_of_const hk hk4 hk2 (by norm_num) y₀ f₀ hy₃ hr

/-! ### Initial values -/

@[simp] theorem connectorLogProfile_self (k : ℝ → ℝ) (y₀ f₀ : ℝ) :
    connectorLogProfile k y₀ f₀ y₀ = f₀ := by
  simp [connectorLogProfile]

@[simp] theorem connectorLogHeight_self (k : ℝ → ℝ) (y₀ κ₀ : ℝ) :
    connectorLogHeight k y₀ κ₀ y₀ = κ₀ := by
  simp [connectorLogHeight]

theorem connectorProfile_exp_self (k : ℝ → ℝ) (y₀ f₀ : ℝ) :
    connectorProfile k y₀ f₀ (Real.exp y₀) = Real.exp y₀ * Real.exp f₀ := by
  simp [connectorProfile]

theorem connectorHeight_exp_self (k : ℝ → ℝ) (y₀ κ₀ : ℝ) :
    connectorHeight k y₀ κ₀ (Real.exp y₀) = Real.exp κ₀ := by
  simp [connectorHeight]

end

end ContinuousFlexibility.Radial
