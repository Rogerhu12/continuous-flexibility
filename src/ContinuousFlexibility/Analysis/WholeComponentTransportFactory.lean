import ContinuousFlexibility.Analysis.RawEndpointAngularInterpolation
import ContinuousFlexibility.Analysis.EndpointFiberPullbackAssembly
import ContinuousFlexibility.Analysis.EndpointTransportGeometry

/-!
# The displayed whole-component transport and its genuine inverse

Both endpoint fields are matched by the same angular Taylor patch and
the actual radial integral interpolation. Widths and the finite inverse
jet constant precede the family index. This file is a new reconstruction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def wholeComponentEndpointAngle (n : ℕ) (ψ : Bool → PolarPoint → ℝ)
    (l r c d κφ M : ℝ) : PolarPoint → ℝ :=
  positiveAngularTaylorInterpolation (n + 1) l r
    (endpointAngularWidth (n + 1) l r c d κφ M) (rawEndpointAngularData l r ψ)

def wholeComponentEndpointTransport (n : ℕ)
    (ψ X : Bool → PolarPoint → ℝ) (l r c d κφ κX M Mσ : ℝ) : PolarPoint → PolarPoint :=
  let φ := wholeComponentEndpointAngle n ψ l r c d κφ M
  positiveFiberChart φ (endpointFiberPullbackCoordinate n φ X l r c d κX Mσ)

def wholeComponentEndpointTransportInverse (n : ℕ)
    (ψ X : Bool → PolarPoint → ℝ) (l r c d κφ κX M Mσ : ℝ) : PolarPoint → PolarPoint :=
  let φ := wholeComponentEndpointAngle n ψ l r c d κφ M
  positiveFiberChartInverse φ (endpointFiberPullbackCoordinate n φ X l r c d κX Mσ)

theorem exists_wholeComponentEndpointTransport_family
    {ι : Type*} (n : ℕ) {ψ X : ι → Bool → PolarPoint → ℝ}
    {l r c d κφ κX M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκφ : 0 < κφ) (hκφone : κφ ≤ 1) (hκX : 0 < κX) (hM : 0 ≤ M)
    (hψ : ∀ i side, ContDiff ℝ ∞ (ψ i side))
    (hψangle : ∀ i side θ, κφ ≤ angularPartial (ψ i side) (if side then r else l, θ))
    (hψjets : ∀ i side k, 1 ≤ k → k ≤ n + 2 → ∀ θ,
      ‖iteratedFDeriv ℝ k (ψ i side) (if side then r else l, θ)‖ ≤ M)
    (hψperiod : ∀ i side x θ, ψ i side (x, θ + Real.pi) = ψ i side (x, θ) + Real.pi)
    (hψodd : ∀ i side x θ, ψ i side (x, -θ) = -ψ i side (x, θ))
    (hX : ∀ i side, ContDiff ℝ ∞ (X i side))
    (hXvalue : ∀ i side θ, X i side (if side then r else l, θ) = if side then r else l)
    (hXlow : ∀ i side θ, κX ≤ radialPartial (X i side) (if side then r else l, θ))
    (hXjets : ∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ k (X i side) (if side then r else l, θ)‖ ≤ M)
    (hXperiod : ∀ i side x θ, X i side (x, θ + Real.pi) = X i side (x, θ))
    (hXeven : ∀ i side x θ, X i side (x, -θ) = X i side (x, θ)) :
    let δ := endpointAngularWidth (n + 1) l r c d κφ M
    0 < δ ∧ δ ≤ 1 ∧ 2 * δ < r - l ∧ δ < c - l ∧ δ < r - d ∧
      ∃ Mσ : ℝ, 1 ≤ Mσ ∧
      let η := endpointFiberWidths n l r c d κX Mσ
      let B := endpointFiberLower n l r c d κX Mσ
      (∀ side, 0 < η side) ∧
      (∀ side, 2 * η side < (if side then r else c) - (if side then d else l)) ∧
      0 < B ∧ ∀ i,
      let τ := wholeComponentEndpointTransport n (ψ i) (X i) l r c d κφ κX M Mσ
      let σ := wholeComponentEndpointTransportInverse n (ψ i) (X i) l r c d κφ κX M Mσ
      WholeComponentTransportGeometry τ σ l r c d (B * (κφ / 2)) ∧
      (∀ side k, k ≤ n + 1 → ∀ θ,
        radialBoundaryJet (fun p => (τ p).1) (if side then r else l) k θ =
          radialBoundaryJet (X i side) (if side then r else l) k θ) ∧
      ∀ side k, k ≤ n + 1 → ∀ θ,
        radialBoundaryJet (fun p => (τ p).2) (if side then r else l) k θ =
          radialBoundaryJet (ψ i side) (if side then r else l) k θ := by
  have hang := rawEndpointAngularInterpolation_family (n + 1) hlc hcd hdr
    hκφ hκφone hM hψ hψangle hψjets hψperiod hψodd
  dsimp only at hang ⊢
  rcases hang with ⟨hδ, hδone, hδgap, hδL, hδR, hang⟩
  let φ : ι → PolarPoint → ℝ := fun i =>
    wholeComponentEndpointAngle n (ψ i) l r c d κφ M
  have hφ (i : ι) : ContDiff ℝ ∞ (φ i) := (hang i).1
  have hφlower (i : ι) (x θ : ℝ) :
      κφ / 2 ≤ deriv (fun η => φ i (x, η)) θ := (hang i).2.1 x θ
  have hφperiod (i : ι) (x θ : ℝ) :
      φ i (x, θ + Real.pi) = φ i (x, θ) + Real.pi := (hang i).2.2.2.2.1 x θ
  have hφodd (i : ι) (x θ : ℝ) :
      φ i (x, -θ) = -φ i (x, θ) := (hang i).2.2.2.2.2.1 x θ
  have hφraw (i : ι) (side : Bool) (k : ℕ) (hk : 1 ≤ k)
      (hkn : k ≤ n + 1) (θ : ℝ) :
      ‖iteratedFDeriv ℝ k (φ i) (if side then r else l, θ)‖ ≤ M := by
    dsimp only [φ, wholeComponentEndpointAngle]
    rw [(hang i).2.2.2.1 side k hkn θ]
    exact hψjets i side k hk (by omega) θ
  obtain ⟨Mσ, hMσ, hη, hηgap, hB, hfiber⟩ :=
    exists_endpointFiberPullback_family n hlc hcd hdr (half_pos hκφ) hκX hM
      hφ hX hφlower hφperiod hφodd hXvalue hXlow hφraw hXjets hXperiod hXeven
  refine ⟨hδ, hδone, hδgap, hδL, hδR, Mσ, hMσ, hη, hηgap, hB, ?_⟩
  intro i
  rcases hfiber i with ⟨hY, hYlower, hleft, hright, hYperiod, hYeven, hYmiddle, hYjets⟩
  refine ⟨wholeComponentTransportGeometry_of_scalars (hφ i) hY
    (half_pos hκφ) hB (hφlower i) hYlower (hφperiod i) (hφodd i)
    hYperiod hYeven hleft hright ((hang i).2.2.2.2.2.2) hYmiddle,
    hYjets, (hang i).2.2.1⟩

end ContinuousFlexibility.Analysis
