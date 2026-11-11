import ContinuousFlexibility.Analysis.TravelStripAngularInverse
import ContinuousFlexibility.Scalar.Conservation

/-!
# First integrals from the actual inverse characteristic flow

The hypotheses concern the forward flow on one closed physical component.
Its actual fiberwise `invFun` is continuous up to both endpoints and smooth
in the interior. Composing that inverse with the left angular normalization
defines the first integral; no inverse regularity or coordinate conclusion
is included among the hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Qualitative regularity of the actual forward characteristic flow.
The radial variable may fail to be smooth at the turning endpoints. -/
structure N04bCircleFlowRegularity (Φ : PolarPoint → ℝ) (a b P : ℝ) : Prop where
  continuous : ContinuousOn Φ (Icc a b ×ˢ univ)
  smooth : ContDiffOn ℝ ∞ Φ (Ioo a b ×ˢ univ)
  positive : ∀ r ∈ Icc a b, ∀ θ : ℝ,
    0 < deriv (fun η => Φ (r, η)) θ
  periodic : ∀ r ∈ Icc a b, ∀ θ : ℝ, Φ (r, θ + P) = Φ (r, θ) + P

namespace N04bCircleFlowRegularity

variable {Φ : PolarPoint → ℝ} {a b P : ℝ}
  (hΦ : N04bCircleFlowRegularity Φ a b P)

include hΦ

theorem strictMono {r : ℝ} (hr : r ∈ Icc a b) :
    StrictMono (fun θ : ℝ => Φ (r, θ)) :=
  strictMono_of_deriv_pos (hΦ.positive r hr)

theorem continuous_slice {r : ℝ} (hr : r ∈ Icc a b) :
    Continuous (fun θ : ℝ => Φ (r, θ)) :=
  continuousOn_univ.mp (hΦ.continuous.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨hr, mem_univ _⟩))

theorem surjective (hP : P ≠ 0) {r : ℝ} (hr : r ∈ Icc a b) :
    Function.Surjective (fun θ : ℝ => Φ (r, θ)) :=
  surjective_of_continuous_periodic_lift hP (hΦ.continuous_slice hr)
    (hΦ.periodic r hr)

theorem inverse_right (hP : P ≠ 0) {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    Φ (r, parameterizedCircleInverse Φ (r, θ)) = θ :=
  Function.rightInverse_invFun (hΦ.surjective hP hr) θ

theorem inverse_left {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    parameterizedCircleInverse Φ (r, Φ (r, θ)) = θ :=
  Function.leftInverse_invFun (hΦ.strictMono hr).injective θ

/-- Joint continuity includes both physical endpoints. -/
theorem inverse_continuous (hP : P ≠ 0) :
    ContinuousOn (parameterizedCircleInverse Φ) (Icc a b ×ˢ univ) :=
  continuousOn_parameterizedCircleInverse_of_strictMono hΦ.continuous
    (fun _ hr => hΦ.strictMono hr) (fun _ hr => hΦ.surjective hP hr)

/-- Interior smoothness is obtained from the actual triangular inverse. -/
theorem inverse_smooth (hP : P ≠ 0) :
    ContDiffOn ℝ ∞ (parameterizedCircleInverse Φ) (Ioo a b ×ˢ univ) := by
  apply contDiffOn_parameterizedCircleInverse_of_strictMono isOpen_Ioo hΦ.smooth
  · rintro ⟨r, θ⟩ hp
    have hd : DifferentiableAt ℝ Φ (r, θ) :=
      (hΦ.smooth.contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
    rw [← (hasDerivAt_angular_slice hd).deriv]
    exact hΦ.positive r ⟨hp.1.1.le, hp.1.2.le⟩ θ
  · intro r hr
    exact hΦ.strictMono ⟨hr.1.le, hr.2.le⟩
  · intro r hr
    exact hΦ.surjective hP ⟨hr.1.le, hr.2.le⟩

/-- The derivative belongs to the same actual `invFun` used above. -/
theorem inverse_hasDerivAt (hP : P ≠ 0) {r : ℝ} (hr : r ∈ Ioo a b) (θ : ℝ) :
    HasDerivAt (fun η => parameterizedCircleInverse Φ (r, η))
      (deriv (fun η => Φ (r, η)) (parameterizedCircleInverse Φ (r, θ)))⁻¹ θ := by
  let G := parameterizedCircleInverse Φ
  have hrclosed : r ∈ Icc a b := ⟨hr.1.le, hr.2.le⟩
  have hGd : DifferentiableAt ℝ G (r, θ) :=
    ((hΦ.inverse_smooth hP).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩)).differentiableAt (by simp)
  have hg := hasDerivAt_angular_slice hGd
  have hp := hΦ.positive r hrclosed (G (r, θ))
  have hf := (differentiableAt_of_deriv_ne_zero hp.ne').hasDerivAt
  have hc := hf.comp θ hg
  have he : (fun η => Φ (r, η)) ∘ (fun η => G (r, η)) = id := by
    funext η
    exact hΦ.inverse_right hP hrclosed η
  rw [he] at hc
  have hprod := hc.unique (hasDerivAt_id θ)
  have hrecip : angularPartial G (r, θ) =
      (deriv (fun η => Φ (r, η)) (G (r, θ)))⁻¹ := by
    apply mul_left_cancel₀ hp.ne'
    rw [hprod, mul_inv_cancel₀ hp.ne']
  exact hg.congr_deriv hrecip

theorem inverse_period_add (hP : P ≠ 0) {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    parameterizedCircleInverse Φ (r, θ + P) =
      parameterizedCircleInverse Φ (r, θ) + P := by
  apply (hΦ.strictMono hr).injective
  change Φ (r, parameterizedCircleInverse Φ (r, θ + P)) =
    Φ (r, parameterizedCircleInverse Φ (r, θ) + P)
  rw [hΦ.inverse_right hP hr, hΦ.periodic r hr, hΦ.inverse_right hP hr]

end N04bCircleFlowRegularity

/-- The first integral is the prescribed left normalization of the
actual initial angle of the forward minus characteristic. -/
def n04bMinusFirstIntegral (Φ : PolarPoint → ℝ) (hL : ℝ → ℝ) (p : PolarPoint) : ℝ :=
  hL (parameterizedCircleInverse Φ p)

theorem n04b_minusFirstIntegral_along_flow
    {Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hL : ℝ → ℝ)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    n04bMinusFirstIntegral Φ hL (r, Φ (r, θ)) = hL θ :=
  congrArg hL (hΦ.inverse_left hr θ)

theorem n04b_minusFirstIntegral_continuous
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : Continuous hL) :
    ContinuousOn (n04bMinusFirstIntegral Φ hL) (Icc a b ×ˢ univ) :=
  hhL.comp_continuousOn (hΦ.inverse_continuous hP)

theorem n04b_minusFirstIntegral_smooth
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL) :
    ContDiffOn ℝ ∞ (n04bMinusFirstIntegral Φ hL) (Ioo a b ×ˢ univ) :=
  hhL.comp_contDiffOn (hΦ.inverse_smooth hP)

/-- The angular derivative is a positive forward-Jacobian quotient. -/
theorem n04b_minusFirstIntegral_angularPartial
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL) {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ univ) :
    angularPartial (n04bMinusFirstIntegral Φ hL) p =
      deriv hL (parameterizedCircleInverse Φ p) /
        deriv (fun η => Φ (p.1, η)) (parameterizedCircleInverse Φ p) := by
  have hd : DifferentiableAt ℝ (n04bMinusFirstIntegral Φ hL) p :=
    ((n04b_minusFirstIntegral_smooth hΦ hP hhL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hc := ((hhL.differentiable (by simp) (parameterizedCircleInverse Φ p)).hasDerivAt).comp
    p.2 (hΦ.inverse_hasDerivAt hP hp.1 p.2)
  have hslice : HasDerivAt (fun θ => n04bMinusFirstIntegral Φ hL (p.1, θ))
      (deriv hL (parameterizedCircleInverse Φ p) *
        (deriv (fun η => Φ (p.1, η)) (parameterizedCircleInverse Φ p))⁻¹) p.2 := by
    simpa only [n04bMinusFirstIntegral, Function.comp_def] using hc
  simpa only [div_eq_mul_inv] using (hasDerivAt_angular_slice hd).unique hslice

theorem n04b_minusFirstIntegral_angularPartial_pos
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL) (hLpos : ∀ θ, 0 < deriv hL θ)
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ univ) :
    0 < angularPartial (n04bMinusFirstIntegral Φ hL) p := by
  rw [n04b_minusFirstIntegral_angularPartial hΦ hP hhL hp]
  exact div_pos (hLpos _) (hΦ.positive p.1 ⟨hp.1.1.le, hp.1.2.le⟩ _)

theorem n04b_minusFirstIntegral_period_add
    {Φ : PolarPoint → ℝ} {hL : ℝ → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hLperiod : ∀ θ, hL (θ + P) = hL θ + P)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    n04bMinusFirstIntegral Φ hL (r, θ + P) =
      n04bMinusFirstIntegral Φ hL (r, θ) + P := by
  unfold n04bMinusFirstIntegral
  rw [hΦ.inverse_period_add hP hr, hLperiod]

theorem n04b_minusFirstIntegral_left
    {Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hab : a ≤ b)
    (hleft : ∀ θ, Φ (a, θ) = θ) (hL : ℝ → ℝ) (θ : ℝ) :
    n04bMinusFirstIntegral Φ hL (a, θ) = hL θ := by
  have hi := hΦ.inverse_left (show a ∈ Icc a b from ⟨le_rfl, hab⟩) θ
  rw [hleft θ] at hi
  exact congrArg hL hi

theorem n04b_minusFirstIntegral_right
    {Φ : PolarPoint → ℝ} {hL hR : ℝ → ℝ} {a b P W : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0) (hab : a ≤ b)
    (hreturn : ∀ θ, hR (Φ (b, θ)) = hL θ - W) (θ : ℝ) :
    n04bMinusFirstIntegral Φ hL (b, θ) = hR θ + W := by
  have hi := hΦ.inverse_right hP (show b ∈ Icc a b from ⟨hab, le_rfl⟩) θ
  have he := hreturn (parameterizedCircleInverse Φ (b, θ))
  rw [hi] at he
  change hL (parameterizedCircleInverse Φ (b, θ)) = hR θ + W
  linarith

end ContinuousFlexibility.Analysis
