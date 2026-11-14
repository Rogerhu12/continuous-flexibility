module

public import ContinuousFlexibility.Analysis.RadialGermGlue
public import ContinuousFlexibility.Analysis.PositiveFiberCoordinates

/-!
# Gluing the two actual positive collars to a fixed reference coordinate

Both exits agree with the reference as genuine planar germs. Two radial
glues therefore preserve global smoothness, one common positive scalar
slope, exact reference values between the exits, and every ordinary jet
of each endpoint collar. The construction handles both ends symmetrically.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def twoEndpointFiberCoordinate (c d : ℝ)
    (Y : Bool → PolarPoint → ℝ) (Ref : PolarPoint → ℝ) : PolarPoint → ℝ :=
  radialGermGlue c (Y false) (radialGermGlue d Ref (Y true))

private theorem twoEndpointFiberCoordinate_left_match
    {c d : ℝ} (hcd : c < d)
    {Y : Bool → PolarPoint → ℝ} {Ref : PolarPoint → ℝ}
    (hmatch : ∀ side θ, Y side =ᶠ[𝓝 (if side then d else c, θ)] Ref)
    (θ : ℝ) :
    Y false =ᶠ[𝓝 (c, θ)] radialGermGlue d Ref (Y true) := by
  have he := radialGermGlue_eventuallyEq (fun η => (hmatch true η).symm) (c, θ)
  change radialGermGlue d Ref (Y true) =ᶠ[𝓝 (c, θ)]
    (if c < d then Ref else Y true) at he
  rw [if_pos hcd] at he
  exact (hmatch false θ).trans he.symm

/-- No partition-of-unity derivative enters the positive slope: both
glues are exact on a neighborhood of their interface. -/
theorem twoEndpointFiberCoordinate_geometry
    {c d : ℝ} (hcd : c < d)
    {Y : Bool → PolarPoint → ℝ} {Ref : PolarPoint → ℝ}
    (hY : ∀ side, ContDiff ℝ ∞ (Y side)) (hRef : ContDiff ℝ ∞ Ref)
    (hmatch : ∀ side θ, Y side =ᶠ[𝓝 (if side then d else c, θ)] Ref)
    {B : Bool → ℝ} {Bref : ℝ} (hB : ∀ side, 0 < B side) (hBref : 0 < Bref)
    (hYlow : ∀ side p, B side ≤ radialPartial (Y side) p)
    (hRefLow : ∀ p, Bref ≤ radialPartial Ref p) :
    ContDiff ℝ ∞ (twoEndpointFiberCoordinate c d Y Ref) ∧
      0 < min (B false) (min Bref (B true)) ∧
      (∀ p, min (B false) (min Bref (B true)) ≤
        radialPartial (twoEndpointFiberCoordinate c d Y Ref) p) := by
  have hright := fun θ => (hmatch true θ).symm
  have hinner := contDiff_radialGermGlue hRef (hY true) hright
  have hleft := twoEndpointFiberCoordinate_left_match hcd hmatch
  exact ⟨contDiff_radialGermGlue (hY false) hinner hleft,
    lt_min (hB false) (lt_min hBref (hB true)),
    radialPartial_radialGermGlue_lower hleft (hYlow false)
      (radialPartial_radialGermGlue_lower hright hRefLow (hYlow true))⟩

/-- The fixed reference coordinate is retained exactly throughout the
closed interval between the two collar exits. -/
theorem twoEndpointFiberCoordinate_eq_reference
    {c d : ℝ} {Y : Bool → PolarPoint → ℝ} {Ref : PolarPoint → ℝ}
    (hmatch : ∀ side θ, Y side =ᶠ[𝓝 (if side then d else c, θ)] Ref)
    {p : PolarPoint} (hp : p.1 ∈ Icc c d) :
    twoEndpointFiberCoordinate c d Y Ref p = Ref p := by
  rw [twoEndpointFiberCoordinate, radialGermGlue_eq_right _ _ hp.1]
  by_cases hd : p.1 < d
  · exact radialGermGlue_eq_left _ _ hd
  · rw [radialGermGlue_eq_right _ _ (le_of_not_gt hd)]
    have he : p.1 = d := le_antisymm hp.2 (le_of_not_gt hd)
    have hp' : p = (d, p.2) := Prod.ext he rfl
    rw [hp']
    exact (hmatch true p.2).eq_of_nhds

/-- All angular invariances are preserved, in particular periodicity
and evenness. No regularity of the angular transformation is needed. -/
theorem twoEndpointFiberCoordinate_angleInvariant
    (c d : ℝ) {Y : Bool → PolarPoint → ℝ} {Ref : PolarPoint → ℝ}
    (τ : ℝ → ℝ) (hY : ∀ side x θ, Y side (x, τ θ) = Y side (x, θ))
    (hRef : ∀ x θ, Ref (x, τ θ) = Ref (x, θ)) (x θ : ℝ) :
    twoEndpointFiberCoordinate c d Y Ref (x, τ θ) =
      twoEndpointFiberCoordinate c d Y Ref (x, θ) := by
  simp only [twoEndpointFiberCoordinate, radialGermGlue, hY, hRef]

/-- At either physical root, outside the exits, the glued scalar field
has the complete joint germ of that endpoint collar. -/
theorem twoEndpointFiberCoordinate_endpoint_germ
    {l r c d : ℝ} (hl : l < c) (hcd : c < d) (hr : d < r)
    {Y : Bool → PolarPoint → ℝ} {Ref : PolarPoint → ℝ}
    (hmatch : ∀ side θ, Y side =ᶠ[𝓝 (if side then d else c, θ)] Ref)
    (side : Bool) (η : ℝ) :
    twoEndpointFiberCoordinate c d Y Ref =ᶠ[𝓝 (if side then r else l, η)]
      Y side := by
  have hright := fun θ => (hmatch true θ).symm
  have hleft := twoEndpointFiberCoordinate_left_match hcd hmatch
  cases side with
  | false =>
      change twoEndpointFiberCoordinate c d Y Ref =ᶠ[𝓝 (l, η)] Y false
      have he := radialGermGlue_eventuallyEq hleft (l, η)
      simpa only [twoEndpointFiberCoordinate, if_pos hl] using he
  | true =>
      change twoEndpointFiberCoordinate c d Y Ref =ᶠ[𝓝 (r, η)] Y true
      have hcr : ¬r < c := not_lt_of_ge (hcd.trans hr).le
      have hdr : ¬r < d := not_lt_of_ge hr.le
      have he := radialGermGlue_eventuallyEq hleft (r, η)
      have hi := radialGermGlue_eventuallyEq hright (r, η)
      change radialGermGlue d Ref (Y true) =ᶠ[𝓝 (r, η)]
        (if r < d then Ref else Y true) at hi
      rw [if_neg hcr] at he
      rw [if_neg hdr] at hi
      exact he.trans hi

/-- The true fiber-angle composition transports a scalar joint germ to
a joint germ of the actual planar coordinate chart. -/
theorem positiveFiberChart_eventuallyEq_of_fiber_germ
    {φ Y Z : PolarPoint → ℝ} {p : PolarPoint}
    (hφ : ContinuousAt φ p)
    (hY : Y =ᶠ[𝓝 (p.1, φ p)] Z) :
    positiveFiberChart φ Y =ᶠ[𝓝 p] positiveFiberChart φ Z := by
  have hline : ContinuousAt (fun q : PolarPoint => (q.1, φ q)) p :=
    continuousAt_fst.prodMk hφ
  filter_upwards [hY.comp_tendsto hline.tendsto] with q hq
  exact Prod.ext hq rfl

/-- The two glued endpoint charts preserve all ordinary Fréchet jets.
The finite radial matching previously proved for each Taylor collar
therefore survives the actual global assembly without any loss of order. -/
theorem iteratedFDeriv_twoEndpointFiberChart_boundary
    {l r c d : ℝ} (hl : l < c) (hcd : c < d) (hr : d < r)
    {Y : Bool → PolarPoint → ℝ} {Ref φ : PolarPoint → ℝ}
    (hφ : Continuous φ)
    (hmatch : ∀ side θ, Y side =ᶠ[𝓝 (if side then d else c, θ)] Ref)
    (side : Bool) (k : ℕ) (θ : ℝ) :
    iteratedFDeriv ℝ k
        (positiveFiberChart φ (twoEndpointFiberCoordinate c d Y Ref))
        (if side then r else l, θ) =
      iteratedFDeriv ℝ k (positiveFiberChart φ (Y side))
        (if side then r else l, θ) := by
  have hg := twoEndpointFiberCoordinate_endpoint_germ hl hcd hr hmatch side
    (φ (if side then r else l, θ))
  have hc := positiveFiberChart_eventuallyEq_of_fiber_germ
    (hφ.continuousAt (x := (if side then r else l, θ))) hg
  exact (hc.iteratedFDeriv ℝ k).eq_of_nhds

end ContinuousFlexibility.Analysis
