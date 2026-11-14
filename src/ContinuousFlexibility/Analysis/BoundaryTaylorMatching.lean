module

public import ContinuousFlexibility.Analysis.BoundaryMixedJets
public import ContinuousFlexibility.Analysis.BoundaryTaylorHeight

/-!
# Actual coordinate and height matching at both boundary circles

A coordinate component is the reference component plus the finite Taylor
extension of their difference. The height is the reference height times
the exponential of the extension of their logarithmic difference. These
actual constructions match every angular derivative of the prescribed
radial boundary jets. The coordinate construction uses degree four and
the height construction degree three in the application.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Add the finite boundary extension of a component difference to the
reference component. This is applied to each actual chart component. -/
def boundaryTaylorPerturbation (n : ℕ) (c d : ℝ)
    (Fref F : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  Fref p + boundaryTaylorExtension n c d
    (radialBoundaryJet (fun q => F q - Fref q) c)
    (radialBoundaryJet (fun q => F q - Fref q) d) p

private theorem contDiff_boundaryTaylorCorrection
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) {c d : ℝ}
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U) (n : ℕ) :
    ContDiff ℝ ∞ (boundaryTaylorExtension n c d
      (radialBoundaryJet F c) (radialBoundaryJet F d)) :=
  contDiff_boundaryTaylorExtension
    (fun j _ => contDiff_radialBoundaryJet_of_contDiffOn hU hF c hc j)
    (fun j _ => contDiff_radialBoundaryJet_of_contDiffOn hU hF d hd j) c d

/-- Only the boundary data of the input field are used away from the
boundary neighborhood. The reference field determines the final domain. -/
theorem contDiffOn_boundaryTaylorPerturbation
    {U V : Set PolarPoint} (hU : IsOpen U) {Fref F : PolarPoint → ℝ}
    (hRef : ContDiffOn ℝ ∞ Fref U) (hF : ContDiffOn ℝ ∞ F U)
    {c d : ℝ} (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U)
    (n : ℕ) (hRefV : ContDiffOn ℝ ∞ Fref V) :
    ContDiffOn ℝ ∞ (boundaryTaylorPerturbation n c d Fref F) V :=
  hRefV.add (contDiff_boundaryTaylorCorrection hU (hF.sub hRef) hc hd n).contDiffOn

/-- The actual component correction matches all prescribed radial jets.
Both endpoint orientations are covered by the same formula. -/
theorem iteratedDeriv_boundaryTaylorPerturbation_eq
    {U : Set PolarPoint} (hU : IsOpen U) {Fref F : PolarPoint → ℝ}
    (hRef : ContDiffOn ℝ ∞ Fref U) (hF : ContDiffOn ℝ ∞ F U)
    {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U)
    (n : ℕ) (side : Bool) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun r => boundaryTaylorPerturbation n c d Fref F (r, θ))
      (if side then d else c) =
      iteratedDeriv k (fun r => F (r, θ)) (if side then d else c) := by
  let δ : PolarPoint → ℝ := fun q => F q - Fref q
  let E : PolarPoint → ℝ := boundaryTaylorExtension n c d
    (radialBoundaryJet δ c) (radialBoundaryJet δ d)
  let x : ℝ := if side then d else c
  have hx : (x, θ) ∈ U := by
    cases side with
    | false => exact hc θ
    | true => exact hd θ
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  have hRefslice : ContDiffAt ℝ ∞ (fun r => Fref (r, θ)) x :=
    ContDiffAt.comp (f := fun r : ℝ => (r, θ)) (g := Fref) x
      (hRef.contDiffAt (hU.mem_nhds hx)) hline
  have hFslice : ContDiffAt ℝ ∞ (fun r => F (r, θ)) x :=
    ContDiffAt.comp (f := fun r : ℝ => (r, θ)) (g := F) x
      (hF.contDiffAt (hU.mem_nhds hx)) hline
  have hE : ContDiff ℝ ∞ E :=
    contDiff_boundaryTaylorCorrection hU (hF.sub hRef) hc hd n
  have hEslice : ContDiffAt ℝ ∞ (fun r => E (r, θ)) x :=
    ContDiffAt.comp (f := fun r : ℝ => (r, θ)) (g := E) x hE.contDiffAt hline
  have he : iteratedDeriv k (fun r => E (r, θ)) x =
      iteratedDeriv k (fun r => δ (r, θ)) x := by
    have ht := iteratedDeriv_boundaryTaylorExtension n hcd
      (radialBoundaryJet δ c) (radialBoundaryJet δ d) side hk θ
    cases side <;> exact ht
  change iteratedDeriv k (fun r => Fref (r, θ) + E (r, θ)) x =
    iteratedDeriv k (fun r => F (r, θ)) x
  rw [iteratedDeriv_fun_add
    (hRefslice.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    (hEslice.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)), he]
  dsimp only [δ]
  rw [iteratedDeriv_fun_sub
    (hFslice.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    (hRefslice.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))]
  ring

/-- Every angular derivative of every matched radial coordinate jet is
also matched by the actual corrected component. -/
theorem mixedDerivative_boundaryTaylorPerturbation_eq
    {U : Set PolarPoint} (hU : IsOpen U) {Fref F : PolarPoint → ℝ}
    (hRef : ContDiffOn ℝ ∞ Fref U) (hF : ContDiffOn ℝ ∞ F U)
    {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U)
    (n : ℕ) (side : Bool) {a : ℕ} (ha : a ≤ n) (b : ℕ) (θ : ℝ) :
    mixedDerivative a b (boundaryTaylorPerturbation n c d Fref F)
      (if side then d else c, θ) =
      mixedDerivative a b F (if side then d else c, θ) := by
  have hs := contDiffOn_boundaryTaylorPerturbation hU hRef hF hc hd n hRef
  have he : ∀ t : ℝ, (if side then d else c, t) ∈ U := by
    cases side with
    | false => exact hc
    | true => exact hd
  apply mixedDerivative_boundary_eq_of_radialBoundaryJet_eq hU hU hs hF
    (if side then d else c) he he (n := n) ?_ ha b θ
  intro j hj t
  exact iteratedDeriv_boundaryTaylorPerturbation_eq hU hRef hF hcd hc hd n side hj t

/-- Exponentiating the logarithmic correction matches the actual height
mixed jets, with no increase of the matched radial order. -/
theorem mixedDerivative_boundaryTaylorHeight_eq
    {U : Set PolarPoint} (hU : IsOpen U) {href h : PolarPoint → ℝ}
    (hRef : ContDiffOn ℝ ∞ href U) (hField : ContDiffOn ℝ ∞ h U)
    (hRefPos : ∀ p ∈ U, 0 < href p) (hPos : ∀ p ∈ U, 0 < h p)
    {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U)
    (n : ℕ) (side : Bool) {a : ℕ} (ha : a ≤ n) (b : ℕ) (θ : ℝ) :
    mixedDerivative a b (boundaryTaylorHeight n c d href h)
      (if side then d else c, θ) =
      mixedDerivative a b h (if side then d else c, θ) := by
  have hs := contDiffOn_boundaryTaylorHeight hU hRef hField hRefPos hPos hc hd n hRef
  have he : ∀ t : ℝ, (if side then d else c, t) ∈ U := by
    cases side with
    | false => exact hc
    | true => exact hd
  apply mixedDerivative_boundary_eq_of_radialBoundaryJet_eq hU hU hs hField
    (if side then d else c) he he (n := n) ?_ ha b θ
  intro j hj t
  exact iteratedDeriv_boundaryTaylorHeight_eq hU hRef hField hRefPos hPos
    hcd hc hd n side hj t

end ContinuousFlexibility.Analysis
