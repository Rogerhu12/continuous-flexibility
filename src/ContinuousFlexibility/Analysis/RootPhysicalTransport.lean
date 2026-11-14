module

public import ContinuousFlexibility.Analysis.RootPhysicalCharacteristicFlow
public import ContinuousFlexibility.Analysis.ActualRootChart
public import ContinuousFlexibility.Geometry.Primitive
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The actual root inverse coordinates satisfy transport

The physical characteristics are constructed by Picard and identified
with the regularized endpoint flow. The genuine inverse identity makes
the normalized inverse coordinate constant along these trajectories.
Differentiating that identity at a positive radial coordinate gives the
transport equation for the actual Fréchet partials. The angular partial
is positive by the true inverse derivative formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def rootCharacteristicCoordinate (G : ℝ × ℝ × ℝ → ℝ) (σ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  G (p.1, σ * p.1 ^ (3 / 2 : ℝ), p.2)

theorem contDiffAt_rootCharacteristicCoordinate
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    {σ x θ : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (rootCharacteristicCoordinate G σ) (x, θ) := by
  have hm : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ => (p.1, σ * p.1 ^ (3 / 2 : ℝ), p.2)) (x, θ) :=
    contDiffAt_fst.prodMk
      ((contDiffAt_const.mul (contDiffAt_fst.rpow_const_of_ne hx.ne')).prodMk contDiffAt_snd)
  exact hG.contDiffAt.comp (x, θ) hm

/-- Constancy along a true characteristic implies the actual first-order
transport equation at any point where the coordinate is differentiable. -/
theorem transport_of_constant_along_characteristic
    {U : ℝ × ℝ → ℝ} {u : ℝ → ℝ} {x θ v c : ℝ}
    (hU : DifferentiableAt ℝ U (x, θ))
    (hu : HasDerivAt u v x) (hvalue : u x = θ)
    (hconstant : (fun r => U (r, u r)) =ᶠ[𝓝 x] (fun _ => c)) :
    radialPartial U (x, θ) = -v * angularPartial U (x, θ) := by
  have hp : HasDerivAt (fun r : ℝ => (r, u r)) (1, v) x :=
    (hasDerivAt_id x).prodMk hu
  have hUr : HasFDerivAt U (fderiv ℝ U (x, θ)) (x, u x) := by
    simpa only [hvalue] using hU.hasFDerivAt
  have hc := hUr.comp_hasDerivAt x hp
  have he : U ∘ (fun r : ℝ => (r, u r)) = (fun r : ℝ => U (r, u r)) := by
    funext r
    exact Function.comp_apply
  rw [he] at hc
  have hz : HasDerivAt (fun r : ℝ => U (r, u r)) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hconstant
  have hzero := hc.unique hz
  rw [polarCLM_apply_decompose] at hzero
  dsimp only at hzero
  unfold radialPartial angularPartial
  linarith

/-- The transport PDE follows from the actual root ODE and inverse map.
The auxiliary ordinary physical flow is constructed inside the proof. -/
theorem rootInverseCoordinate_characteristic_transport
    {d c₀ : ℝ × ℝ → ℝ} {T : ℝ} {hL : ℝ → ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (hinit : ∀ p θ, Θ p 0 θ = θ)
    (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun r => Θ p r θ)
        (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
          2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
        (Icc (0 : ℝ) 1) t)
    (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2))
    (hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ)
    (hperiod : ∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T)
    (hhL : ContDiff ℝ ∞ hL)
    (σ : ℝ) {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    radialPartial (rootCharacteristicCoordinate (rootInverseCoordinate Θ hL) σ) (x, θ) =
      -rootPhysicalSpeed d c₀ σ (x, θ) *
        angularPartial (rootCharacteristicCoordinate (rootInverseCoordinate Θ hL) σ) (x, θ) := by
  let G := rootInverseCoordinate Θ hL
  let U := rootCharacteristicCoordinate G σ
  have hG : ContDiff ℝ ∞ G :=
    contDiff_rootInverseCoordinate hT hEndpoint hpositive hperiod hhL
  have hxI : x ∈ Icc (0 : ℝ) (x + 1) := ⟨hx.le, by linarith⟩
  obtain ⟨Φ, hΦinit, hΦ, _⟩ := exists_rootPhysicalFlow_on_Icc
    (R := x + 1) (by linarith) hT hd hc₀ hdperiod hc₀period σ
  have heq (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (x + 1)) (η : ℝ) :
      Θ (r, σ * r ^ (3 / 2 : ℝ)) 1 η = Φ η r :=
    rootRegularizedFlow_eq_physicalFlow hT hd hc₀ hdperiod hc₀period
      hinit hflow hΦinit hΦ hr η
  let η := parameterizedCircleInverse
    (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((x, σ * x ^ (3 / 2 : ℝ)), θ)
  have hη : Φ η x = θ :=
    (heq x hxI η).symm.trans
      (parameterizedCircleInverse_right_inverse hT hEndpoint hperiod
        ((x, σ * x ^ (3 / 2 : ℝ)), θ))
  have hu : HasDerivAt (Φ η) (rootPhysicalSpeed d c₀ σ (x, θ)) x := by
    have hh := (hΦ η x hxI).hasDerivAt
      (Icc_mem_nhds hx (show x < x + 1 by linarith))
    simpa only [hη] using hh
  have hfirst (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (x + 1)) :
      U (r, Φ η r) = hL η := by
    dsimp only [U, G, rootCharacteristicCoordinate, rootInverseCoordinate]
    rw [← heq r hr η]
    exact congrArg hL (parameterizedCircleInverse_left_inverse
      (fun z => hpositive z.1 z.2) ((r, σ * r ^ (3 / 2 : ℝ)), η))
  have hconstant : (fun r => U (r, Φ η r)) =ᶠ[𝓝 x] (fun _ => hL η) := by
    filter_upwards [Icc_mem_nhds hx (show x < x + 1 by linarith)] with r hr
    exact hfirst r hr
  exact transport_of_constant_along_characteristic
    ((contDiffAt_rootCharacteristicCoordinate hG hx).differentiableAt (by simp))
    hu hη hconstant

/-- Positivity of the physical angular derivative is inherited from the
actual circle inverse and the prescribed increasing angular normalization. -/
theorem rootInverseCoordinate_characteristic_angularPartial_pos
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {T : ℝ} {hL : ℝ → ℝ}
    (hT : T ≠ 0)
    (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2))
    (hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ)
    (hperiod : ∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T)
    (hhL : ContDiff ℝ ∞ hL) (hLpos : ∀ η, 0 < deriv hL η)
    (σ : ℝ) {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    0 < angularPartial
      (rootCharacteristicCoordinate (rootInverseCoordinate Θ hL) σ) (x, θ) := by
  let p : ℝ × ℝ := (x, σ * x ^ (3 / 2 : ℝ))
  let F : (ℝ × ℝ) × ℝ → ℝ := fun z => Θ z.1 1 z.2
  let U := rootCharacteristicCoordinate (rootInverseCoordinate Θ hL) σ
  let η := parameterizedCircleInverse F (p, θ)
  have hi := hasDerivAt_parameterizedCircleInverse hT hEndpoint
    (fun z => hpositive z.1 z.2) hperiod p θ
  have hl := (hhL.differentiable (by simp) η).hasDerivAt
  have hc := hl.comp θ hi
  have he : hL ∘ (fun φ : ℝ => parameterizedCircleInverse F (p, φ)) =
      (fun φ : ℝ => U (x, φ)) := by
    funext φ
    exact Function.comp_apply
  rw [he] at hc
  have hG := contDiff_rootInverseCoordinate hT hEndpoint hpositive hperiod hhL
  have hU : DifferentiableAt ℝ U (x, θ) :=
    (contDiffAt_rootCharacteristicCoordinate hG hx).differentiableAt (by simp)
  have hp : HasDerivAt (fun φ : ℝ => (x, φ)) (0, 1) θ :=
    (hasDerivAt_const θ x).prodMk (hasDerivAt_id θ)
  have hangle := hU.hasFDerivAt.comp_hasDerivAt θ hp
  have he' : U ∘ (fun φ : ℝ => (x, φ)) = (fun φ : ℝ => U (x, φ)) := by
    funext φ
    exact Function.comp_apply
  rw [he'] at hangle
  have hder := hangle.unique hc
  unfold angularPartial
  rw [hder]
  exact mul_pos (hLpos η) (inv_pos.mpr (hpositive p η))

end ContinuousFlexibility.Analysis
