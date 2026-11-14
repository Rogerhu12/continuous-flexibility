module

public import ContinuousFlexibility.Analysis.BoundaryTaylorExtension
public import ContinuousFlexibility.Analysis.FiniteRadialJets
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Positive heights from boundary Taylor extensions of logarithmic data

The positive-component construction extends the difference of logarithms
of the heights. The actual height is the reference height multiplied by
the exponential of this finite boundary extension. Positivity is therefore
automatic wherever the reference height is positive.

Only a smooth positive neighborhood of the two boundary circles is
required for the input height. Outside that neighborhood it is used only
through the already extracted boundary data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The logarithmic difference whose finite boundary jet is extended. -/
def boundaryHeightLogRatio (href h : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  Real.log (h p / href p)

/-- The actual positive height defined from a finite extension of its
logarithmic difference. The manuscript uses degree three. -/
def boundaryTaylorHeight (n : ℕ) (c d : ℝ) (href h : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  href p * Real.exp (boundaryTaylorExtension n c d
    (radialBoundaryJet (boundaryHeightLogRatio href h) c)
    (radialBoundaryJet (boundaryHeightLogRatio href h) d) p)

/-- Restricting actual radial jets to a full boundary circle is smooth
when the original field is smooth on an open neighborhood of that circle. -/
theorem contDiff_radialBoundaryJet_of_contDiffOn
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (c : ℝ)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (j : ℕ) :
    ContDiff ℝ ∞ (radialBoundaryJet F c j) := by
  have hjet := contDiffOn_mixedDerivative hU hF j 0
  have hcomp : ContDiffOn ℝ ∞
      (fun θ : ℝ => mixedDerivative j 0 F (c, θ)) univ :=
    hjet.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun θ _ => hc θ)
  have heq : radialBoundaryJet F c j = fun θ => mixedDerivative j 0 F (c, θ) := by
    funext θ
    simp only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero]
  rw [heq]
  exact contDiffOn_univ.mp hcomp

theorem contDiffOn_boundaryHeightLogRatio
    {U : Set PolarPoint} {href h : PolarPoint → ℝ}
    (hRef : ContDiffOn ℝ ∞ href U) (hField : ContDiffOn ℝ ∞ h U)
    (hRefPos : ∀ p ∈ U, 0 < href p) (hPos : ∀ p ∈ U, 0 < h p) :
    ContDiffOn ℝ ∞ (boundaryHeightLogRatio href h) U := by
  have hquot : ContDiffOn ℝ ∞ (fun p => h p / href p) U :=
    hField.fun_div hRef (fun p hp => (hRefPos p hp).ne')
  exact hquot.log (fun p hp => (div_pos (hPos p hp) (hRefPos p hp)).ne')

/-- The finite logarithmic correction is globally smooth, although the
input height need only be smooth and positive near the boundary circles. -/
theorem contDiff_boundaryHeightLogCorrection
    {U : Set PolarPoint} (hU : IsOpen U) {href h : PolarPoint → ℝ}
    (hRef : ContDiffOn ℝ ∞ href U) (hField : ContDiffOn ℝ ∞ h U)
    (hRefPos : ∀ p ∈ U, 0 < href p) (hPos : ∀ p ∈ U, 0 < h p)
    {c d : ℝ} (hc : ∀ θ : ℝ, (c, θ) ∈ U)
    (hd : ∀ θ : ℝ, (d, θ) ∈ U) (n : ℕ) :
    ContDiff ℝ ∞ (boundaryTaylorExtension n c d
      (radialBoundaryJet (boundaryHeightLogRatio href h) c)
      (radialBoundaryJet (boundaryHeightLogRatio href h) d)) := by
  have hlog := contDiffOn_boundaryHeightLogRatio hRef hField hRefPos hPos
  exact contDiff_boundaryTaylorExtension
    (fun j _ => contDiff_radialBoundaryJet_of_contDiffOn hU hlog c hc j)
    (fun j _ => contDiff_radialBoundaryJet_of_contDiffOn hU hlog d hd j) c d

/-- The resulting height is smooth on any region on which the reference
height is smooth. The input height is needed only near the ends. -/
theorem contDiffOn_boundaryTaylorHeight
    {U V : Set PolarPoint} (hU : IsOpen U) {href h : PolarPoint → ℝ}
    (hRef : ContDiffOn ℝ ∞ href U) (hField : ContDiffOn ℝ ∞ h U)
    (hRefPos : ∀ p ∈ U, 0 < href p) (hPos : ∀ p ∈ U, 0 < h p)
    {c d : ℝ} (hc : ∀ θ : ℝ, (c, θ) ∈ U)
    (hd : ∀ θ : ℝ, (d, θ) ∈ U) (n : ℕ)
    (hRefV : ContDiffOn ℝ ∞ href V) :
    ContDiffOn ℝ ∞ (boundaryTaylorHeight n c d href h) V := by
  have hE := contDiff_boundaryHeightLogCorrection hU hRef hField hRefPos hPos hc hd n
  exact hRefV.mul (Real.contDiff_exp.comp hE).contDiffOn

/-- Positivity follows from the construction and does not require
smallness of the logarithmic correction. -/
theorem boundaryTaylorHeight_pos (n : ℕ) (c d : ℝ) (href h : PolarPoint → ℝ)
    {p : PolarPoint} (hp : 0 < href p) :
    0 < boundaryTaylorHeight n c d href h p := by
  exact mul_pos hp (Real.exp_pos _)

/-- Exponentiation and multiplication by the reference height transfer
the matched logarithmic jets to actual height jets. Both endpoints are
handled by the same statement. -/
theorem iteratedDeriv_boundaryTaylorHeight_eq
    {U : Set PolarPoint} (hU : IsOpen U) {href h : PolarPoint → ℝ}
    (hRef : ContDiffOn ℝ ∞ href U) (hField : ContDiffOn ℝ ∞ h U)
    (hRefPos : ∀ p ∈ U, 0 < href p) (hPos : ∀ p ∈ U, 0 < h p)
    {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U)
    (n : ℕ) (side : Bool) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun r => boundaryTaylorHeight n c d href h (r, θ))
      (if side then d else c) =
      iteratedDeriv k (fun r => h (r, θ)) (if side then d else c) := by
  let F : PolarPoint → ℝ := boundaryHeightLogRatio href h
  let E : PolarPoint → ℝ := boundaryTaylorExtension n c d
    (radialBoundaryJet F c) (radialBoundaryJet F d)
  let x : ℝ := if side then d else c
  have hx : (x, θ) ∈ U := by
    cases side with
    | false => exact hc θ
    | true => exact hd θ
  have hlog : ContDiffOn ℝ ∞ F U :=
    contDiffOn_boundaryHeightLogRatio hRef hField hRefPos hPos
  have hE : ContDiff ℝ ∞ E :=
    contDiff_boundaryHeightLogCorrection hU hRef hField hRefPos hPos hc hd n
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  have hFslice : ContDiffAt ℝ ∞ (fun r => F (r, θ)) x :=
    ContDiffAt.comp (f := fun r : ℝ => (r, θ)) (g := F) x
      ((hlog (x, θ) hx).contDiffAt (hU.mem_nhds hx)) hline
  have hEslice : ContDiffAt ℝ ∞ (fun r => E (r, θ)) x :=
    hE.contDiffAt.comp x hline
  have hRefslice : ContDiffAt ℝ ∞ (fun r => href (r, θ)) x :=
    ((hRef (x, θ) hx).contDiffAt (hU.mem_nhds hx)).comp x hline
  have hjet (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j (fun r => E (r, θ)) x =
        iteratedDeriv j (fun r => F (r, θ)) x := by
    have he := iteratedDeriv_boundaryTaylorExtension n hcd
      (radialBoundaryJet F c) (radialBoundaryJet F d) side hj θ
    cases side <;> exact he
  have hexp (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j (fun r => Real.exp (E (r, θ))) x =
        iteratedDeriv j (fun r => Real.exp (F (r, θ))) x := by
    simpa only [Function.comp_def] using
      iteratedDeriv_vcomp_eq_of_finiteJet_eq hEslice hFslice
        Real.contDiff_exp.contDiffAt hjet hj
  have hExpE : ContDiffAt ℝ ∞ (fun r => Real.exp (E (r, θ))) x :=
    Real.contDiff_exp.contDiffAt.comp x hEslice
  have hExpF : ContDiffAt ℝ ∞ (fun r => Real.exp (F (r, θ))) x :=
    Real.contDiff_exp.contDiffAt.comp x hFslice
  have hprod := iteratedDeriv_mul_left_eq_of_finiteJet_eq
    hExpE hExpF hRefslice hexp hk
  have hgerm : (fun r => href (r, θ) * Real.exp (F (r, θ))) =ᶠ[𝓝 x]
      (fun r => h (r, θ)) := by
    have hlineC : Continuous (fun r : ℝ => (r, θ)) :=
      continuous_id.prodMk continuous_const
    filter_upwards [(hlineC.tendsto x).eventually (hU.mem_nhds hx)] with r hr
    have hratio : 0 < h (r, θ) / href (r, θ) :=
      div_pos (hPos (r, θ) hr) (hRefPos (r, θ) hr)
    dsimp only [F, boundaryHeightLogRatio]
    rw [Real.exp_log hratio, mul_comm,
      div_mul_cancel₀ _ (hRefPos (r, θ) hr).ne']
  change iteratedDeriv k (fun r => href (r, θ) * Real.exp (E (r, θ))) x =
    iteratedDeriv k (fun r => h (r, θ)) x
  exact hprod.trans (hgerm.iteratedDeriv k).eq_of_nhds

end ContinuousFlexibility.Analysis
