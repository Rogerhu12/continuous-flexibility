import ContinuousFlexibility.Analysis.WholeComponentReferenceIdentity

/-!
# Exact radial identity at an ambient positive endpoint

An identity source at one endpoint makes that actual radial collar the
identity, independently of the opposite endpoint and of the angular
lift. The displayed whole transport consequently fixes the radius on
that entire side of its middle interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem endpointFiberCollar_eq_fst_of_side_data
    (n : ℕ) {l r c d : ℝ} {η : Bool → ℝ} {A : Bool → ℕ → ℝ → ℝ}
    (side : Bool) (hη : 0 < η side)
    (hgap : 2 * η side < (if side then r else c) - (if side then d else l))
    (hA : A side = radialBoundaryJet (Prod.fst : PolarPoint → ℝ)
      (if side then r else l)) :
    endpointFiberCollar n l r c d η A side = (Prod.fst : PolarPoint → ℝ) := by
  unfold endpointFiberCollar
  rw [hA]
  cases side with
  | false =>
      exact positiveReferenceCollarCoordinate_reference_identity n hη hgap false
  | true =>
      exact positiveReferenceCollarCoordinate_reference_identity n hη hgap true

theorem twoEndpointFiberCoordinate_eq_fst_on_side
    {Y : Bool → PolarPoint → ℝ} {c d : ℝ} (hcd : c < d)
    (side : Bool) (hY : Y side = (Prod.fst : PolarPoint → ℝ))
    (p : PolarPoint) (hp : if side then d ≤ p.1 else p.1 ≤ c) :
    twoEndpointFiberCoordinate c d Y Prod.fst p = p.1 := by
  cases side with
  | false =>
      change p.1 ≤ c at hp
      by_cases hpc : p.1 < c
      · simp only [twoEndpointFiberCoordinate, radialGermGlue, if_pos hpc, hY]
      · have hpd : p.1 < d := hp.trans_lt hcd
        simp only [twoEndpointFiberCoordinate, radialGermGlue, if_neg hpc, if_pos hpd]
  | true =>
      change d ≤ p.1 at hp
      have hpc : ¬p.1 < c := not_lt_of_ge (hcd.le.trans hp)
      have hpd : ¬p.1 < d := not_lt_of_ge hp
      simp only [twoEndpointFiberCoordinate, radialGermGlue, if_neg hpc, if_neg hpd, hY]

theorem endpointFiberPullbackCoordinate_eq_fst_on_side
    (n : ℕ) {φ : PolarPoint → ℝ} {X : Bool → PolarPoint → ℝ}
    {l r c d κ Mσ : ℝ} (hcd : c < d) (side : Bool)
    (hX : X side = (Prod.fst : PolarPoint → ℝ))
    (hη : 0 < endpointFiberWidths n l r c d κ Mσ side)
    (hgap : 2 * endpointFiberWidths n l r c d κ Mσ side <
      (if side then r else c) - (if side then d else l))
    (p : PolarPoint) (hp : if side then d ≤ p.1 else p.1 ≤ c) :
    endpointFiberPullbackCoordinate n φ X l r c d κ Mσ p = p.1 := by
  have hpull : angularFiberPullback φ (X side) = (Prod.fst : PolarPoint → ℝ) := by
    rw [hX]
    rfl
  have hcollar : endpointFiberCollar n l r c d
      (endpointFiberWidths n l r c d κ Mσ)
      (fun t => radialBoundaryJet (angularFiberPullback φ (X t))
        (if t then r else l)) side = (Prod.fst : PolarPoint → ℝ) :=
    endpointFiberCollar_eq_fst_of_side_data n side hη hgap (by rw [hpull])
  exact twoEndpointFiberCoordinate_eq_fst_on_side hcd side hcollar p hp

theorem wholeComponentEndpointTransport_radial_eq_of_side_identity
    (n : ℕ) {ψ X : Bool → PolarPoint → ℝ} {l r c d κφ κX M Mσ : ℝ}
    (hcd : c < d) (side : Bool) (hX : X side = (Prod.fst : PolarPoint → ℝ))
    (hη : 0 < endpointFiberWidths n l r c d κX Mσ side)
    (hgap : 2 * endpointFiberWidths n l r c d κX Mσ side <
      (if side then r else c) - (if side then d else l))
    (p : PolarPoint) (hp : if side then d ≤ p.1 else p.1 ≤ c) :
    (wholeComponentEndpointTransport n ψ X l r c d κφ κX M Mσ p).1 = p.1 := by
  let φ := wholeComponentEndpointAngle n ψ l r c d κφ M
  change endpointFiberPullbackCoordinate n φ X l r c d κX Mσ (p.1, φ p) = p.1
  exact endpointFiberPullbackCoordinate_eq_fst_on_side n hcd side hX hη hgap
    (p.1, φ p) hp

/-- Only the chosen endpoint source has to have the identity germ.
The opposite endpoint and the actual angular inverse are unrestricted. -/
theorem oneSidedWholeComponentTransport_radial_eq_of_side_germ
    (n : ℕ) {ψ X : Bool → PolarPoint → ℝ} {l r c d κφ κX M Mσ : ℝ}
    (hcd : c < d) (side : Bool)
    (hX : ∀ θ, X side =ᶠ[𝓝 (if side then r else l, θ)]
      (Prod.fst : PolarPoint → ℝ))
    (hη : 0 < endpointFiberWidths n l r c d κX Mσ side)
    (hgap : 2 * endpointFiberWidths n l r c d κX Mσ side <
      (if side then r else c) - (if side then d else l))
    (p : PolarPoint) (hp : if side then d ≤ p.1 else p.1 ≤ c) :
    (oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ p).1 = p.1 := by
  have hrep : oneSidedEndpointRepresentative (n + 1) l r X side =
      (Prod.fst : PolarPoint → ℝ) :=
    oneSidedBoundaryTaylorRepresentative_eq_fst hX n
  exact wholeComponentEndpointTransport_radial_eq_of_side_identity
    (ψ := oneSidedEndpointRepresentative (n + 2) l r ψ)
    (X := oneSidedEndpointRepresentative (n + 1) l r X) n hcd side hrep hη hgap p hp

end ContinuousFlexibility.Analysis

