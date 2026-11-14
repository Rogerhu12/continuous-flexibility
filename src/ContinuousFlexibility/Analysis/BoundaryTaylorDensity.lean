module

public import ContinuousFlexibility.Analysis.BoundaryTaylorMatching
public import ContinuousFlexibility.Analysis.PrincipalDensityBoundaryJets

/-!
# Principal-density matching for the actual boundary construction

The chart is defined component by component by adding the boundary Taylor
extension of its difference from the reference chart. The height is the
positive exponential construction from the logarithmic difference.

Applying the actual density-jet calculation to these concrete functions
gives matching principal-density jets at both ends. This statement is in
physical coordinates; changing to canonical radial coordinates and the
global invertibility of the constructed chart are separate steps.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual chart obtained by correcting its two scalar components. -/
def boundaryTaylorChart (n : ℕ) (c d : ℝ)
    (Fref F : PolarPoint → PolarPoint) (p : PolarPoint) : PolarPoint :=
  (boundaryTaylorPerturbation n c d (fun q => (Fref q).1) (fun q => (F q).1) p,
    boundaryTaylorPerturbation n c d (fun q => (Fref q).2) (fun q => (F q).2) p)

/-- The chart correction is smooth wherever its reference chart is smooth,
using only a smooth neighborhood of the two boundary circles for its data. -/
theorem contDiffOn_boundaryTaylorChart
    {U V : Set PolarPoint} (hU : IsOpen U) {Fref F : PolarPoint → PolarPoint}
    (hRef : ContDiffOn ℝ ∞ Fref U) (hF : ContDiffOn ℝ ∞ F U)
    {c d : ℝ} (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U)
    (n : ℕ) (hRefV : ContDiffOn ℝ ∞ Fref V) :
    ContDiffOn ℝ ∞ (boundaryTaylorChart n c d Fref F) V :=
  (contDiffOn_boundaryTaylorPerturbation hU hRef.fst hF.fst hc hd n hRefV.fst).prodMk
    (contDiffOn_boundaryTaylorPerturbation hU hRef.snd hF.snd hc hd n hRefV.snd)

/-- Coordinate degree n+1 and logarithmic-height degree n match all
actual principal-density radial jets through order n. In particular the
degree-four / degree-three construction supplies the order-two jets used
for cubic division. No principal-density matching is assumed. -/
theorem radialBoundaryJets_boundaryTaylorDensity_eq
    {U : Set PolarPoint} (hU : IsOpen U) {A : SymmetricCoefficients}
    {Fref F : PolarPoint → PolarPoint} {href h : PolarPoint → ℝ}
    (hAa : ContDiffOn ℝ ∞ A.a U) (hAb : ContDiffOn ℝ ∞ A.b U)
    (hAc : ContDiffOn ℝ ∞ A.c U)
    (hFref : ContDiffOn ℝ ∞ Fref U) (hF : ContDiffOn ℝ ∞ F U)
    (hRef : ContDiffOn ℝ ∞ href U) (hh : ContDiffOn ℝ ∞ h U)
    (hRefPos : ∀ p ∈ U, 0 < href p) (hPos : ∀ p ∈ U, 0 < h p)
    {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hd : ∀ θ : ℝ, (d, θ) ∈ U)
    (n : ℕ) (side : Bool) (θ : ℝ)
    (hJ : planeJacobian F (if side then d else c, θ) ≠ 0) :
    ∀ k ≤ n,
      radialBoundaryJet (coordinatePrincipalDensity A
        (boundaryTaylorChart (n + 1) c d Fref F) (boundaryTaylorHeight n c d href h)).a
          (if side then d else c) k θ =
        radialBoundaryJet (coordinatePrincipalDensity A F h).a (if side then d else c) k θ ∧
      radialBoundaryJet (coordinatePrincipalDensity A
        (boundaryTaylorChart (n + 1) c d Fref F) (boundaryTaylorHeight n c d href h)).b
          (if side then d else c) k θ =
        radialBoundaryJet (coordinatePrincipalDensity A F h).b (if side then d else c) k θ ∧
      radialBoundaryJet (coordinatePrincipalDensity A
        (boundaryTaylorChart (n + 1) c d Fref F) (boundaryTaylorHeight n c d href h)).c
          (if side then d else c) k θ =
        radialBoundaryJet (coordinatePrincipalDensity A F h).c (if side then d else c) k θ := by
  let Fnew := boundaryTaylorChart (n + 1) c d Fref F
  let hnew := boundaryTaylorHeight n c d href h
  let x : ℝ := if side then d else c
  have hx : ∀ t : ℝ, (x, t) ∈ U := by
    cases side with
    | false => exact hc
    | true => exact hd
  have hNewF : ContDiffOn ℝ ∞ Fnew U :=
    contDiffOn_boundaryTaylorChart hU hFref hF hc hd (n + 1) hFref
  have hNewH : ContDiffOn ℝ ∞ hnew U :=
    contDiffOn_boundaryTaylorHeight hU hRef hh hRefPos hPos hc hd n hRef
  have hFst : ∀ k ≤ n + 1, ∀ t : ℝ,
      radialBoundaryJet (fun q => (F q).1) x k t =
        radialBoundaryJet (fun q => (Fnew q).1) x k t := by
    intro k hk t
    exact (iteratedDeriv_boundaryTaylorPerturbation_eq hU hFref.fst hF.fst
      hcd hc hd (n + 1) side hk t).symm
  have hSnd : ∀ k ≤ n + 1, ∀ t : ℝ,
      radialBoundaryJet (fun q => (F q).2) x k t =
        radialBoundaryJet (fun q => (Fnew q).2) x k t := by
    intro k hk t
    exact (iteratedDeriv_boundaryTaylorPerturbation_eq hU hFref.snd hF.snd
      hcd hc hd (n + 1) side hk t).symm
  have hHeight : ∀ k ≤ n, ∀ t : ℝ,
      radialBoundaryJet h x k t = radialBoundaryJet hnew x k t := by
    intro k hk t
    exact (iteratedDeriv_boundaryTaylorHeight_eq hU hRef hh hRefPos hPos
      hcd hc hd n side hk t).symm
  have hmatch := radialBoundaryJets_coordinatePrincipalDensity_eq hU hAa hAb hAc
    hF hNewF hh hNewH x hx hFst hSnd hHeight θ hJ
  intro k hk
  obtain ⟨ha, hb, hc'⟩ := hmatch k hk
  exact ⟨ha.symm, hb.symm, hc'.symm⟩

end ContinuousFlexibility.Analysis
