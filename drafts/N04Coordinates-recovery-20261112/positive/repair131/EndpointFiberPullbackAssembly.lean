import ContinuousFlexibility.Analysis.EndpointFiberInterpolation
import ContinuousFlexibility.Analysis.AngularFiberFiniteJetBounds

/-!
# Radial interpolation in the actual angular inverse coordinates

The displayed fiber coordinate uses the true inverse of the chosen
angular lift. A supplied bound on its finite boundary traces determines
the displayed widths. A second theorem obtains that bound from the
ordinary forward jets, uniformly before the family index.
This is a new reconstruction after the workspace reset.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def endpointFiberPullbackCoordinate (n : ℕ) (φ : PolarPoint → ℝ)
    (X : Bool → PolarPoint → ℝ) (l r c d κ Mσ : ℝ) : PolarPoint → ℝ :=
  endpointFiberInterpolation n l r c d (endpointFiberWidths n l r c d κ Mσ)
    (fun side => radialBoundaryJet (angularFiberPullback φ (X side))
      (if side then r else l))

theorem endpointFiberPullback_family_of_bound
    {ι : Type*} {n : ℕ} {φ : ι → PolarPoint → ℝ}
    {X : ι → Bool → PolarPoint → ℝ} {l r c d κX Mσ : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκX : 0 < κX) (hMσ : 0 ≤ Mσ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hX : ∀ i side, ContDiff ℝ ∞ (X i side))
    (hpositive : ∀ i (p : PolarPoint), 0 < deriv (fun θ => φ i (p.1, θ)) p.2)
    (hφperiod : ∀ i x θ, φ i (x, θ + Real.pi) = φ i (x, θ) + Real.pi)
    (hφodd : ∀ i x θ, φ i (x, -θ) = -φ i (x, θ))
    (hXvalue : ∀ i side θ, X i side (if side then r else l, θ) = if side then r else l)
    (hXlow : ∀ i side θ, κX ≤ radialPartial (X i side) (if side then r else l, θ))
    (hXperiod : ∀ i side x θ, X i side (x, θ + Real.pi) = X i side (x, θ))
    (hXeven : ∀ i side x θ, X i side (x, -θ) = X i side (x, θ))
    (hbound : ∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      |radialBoundaryJet (angularFiberPullback (φ i) (X i side))
        (if side then r else l) k θ| ≤ Mσ) :
    let η := endpointFiberWidths n l r c d κX Mσ
    let B := endpointFiberLower n l r c d κX Mσ
    (∀ side, 0 < η side) ∧
      (∀ side, 2 * η side < (if side then r else c) - (if side then d else l)) ∧
      0 < B ∧ ∀ i,
      let Y := endpointFiberPullbackCoordinate n (φ i) (X i) l r c d κX Mσ
      ContDiff ℝ ∞ Y ∧
      (∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x) ∧
      (∀ θ, Y (l, θ) = l) ∧ (∀ θ, Y (r, θ) = r) ∧
      (∀ x θ, Y (x, θ + Real.pi) = Y (x, θ)) ∧
      (∀ x θ, Y (x, -θ) = Y (x, θ)) ∧
      (∀ x ∈ Icc c d, ∀ θ, Y =ᶠ[𝓝 (x, θ)] (Prod.fst : PolarPoint → ℝ)) ∧
      ∀ side k, k ≤ n + 1 → ∀ θ,
        radialBoundaryJet (fun p => Y (p.1, φ i p)) (if side then r else l) k θ =
          radialBoundaryJet (X i side) (if side then r else l) k θ := by
  let e : Bool → ℝ := fun side => if side then r else l
  let Z : ι → Bool → PolarPoint → ℝ := fun i side =>
    angularFiberPullback (φ i) (X i side)
  let A : ι → Bool → ℕ → ℝ → ℝ := fun i side => radialBoundaryJet (Z i side) (e side)
  have hZ (i : ι) (side : Bool) : ContDiff ℝ ∞ (Z i side) :=
    contDiff_angularFiberPullback Real.pi_ne_zero (hφ i) (hX i side)
      (hpositive i) (hφperiod i)
  have hvalue (i : ι) (side : Bool) (θ : ℝ) : A i side 0 θ = e side := by
    change iteratedDeriv 0 (fun x => Z i side (x, θ)) (e side) = e side
    simpa only [iteratedDeriv_zero] using
      angularFiberPullback_boundary (φ := φ i) (hXvalue i side) θ
  have hlow (i : ι) (side : Bool) (θ : ℝ) : κX ≤ A i side 1 θ := by
    change κX ≤ iteratedDeriv 1 (fun x => Z i side (x, θ)) (e side)
    rw [iteratedDeriv_one,
      deriv_cylinder_radial_slice ((hZ i side).differentiable (by simp)) (e side) θ,
      radialPartial_angularFiberPullback_boundary Real.pi_ne_zero (hφ i) (hX i side)
        (hpositive i) (hφperiod i) (hXvalue i side)]
    exact hXlow i side _
  have hperiod (i : ι) (side : Bool) (j : ℕ) :
      Function.Periodic (A i side j) Real.pi := by
    intro θ
    exact radialBoundaryJet_angleInvariant (fun θ => θ + Real.pi)
      (angularFiberPullback_periodic Real.pi_ne_zero (hφ i) (hpositive i)
        (hφperiod i) (hXperiod i side)) (e side) j θ
  have heven (i : ι) (side : Bool) (j : ℕ) (θ : ℝ) :
      A i side j (-θ) = A i side j θ :=
    radialBoundaryJet_angleInvariant (fun θ => -θ)
      (angularFiberPullback_reflect Real.pi_ne_zero (hφ i) (hpositive i)
        (hφperiod i) (hφodd i) (hXeven i side)) (e side) j θ
  have hout := endpointFiberInterpolation_family hlc hcd hdr hκX hMσ
    (fun i side j _ => contDiff_radialBoundaryJet (hZ i side) (e side) j)
    hvalue hlow hbound (fun i side j _ => hperiod i side j)
    (fun i side j _ => heven i side j)
  dsimp only at hout ⊢
  rcases hout with ⟨hη, hηgap, hB, hout⟩
  refine ⟨hη, hηgap, hB, ?_⟩
  intro i
  rcases hout i with ⟨hY, hYlow, hleft, hright, hYperiod, hYeven, hmiddle, hjet⟩
  refine ⟨hY, hYlow, hleft, hright, hYperiod, hYeven, hmiddle, ?_⟩
  intro side
  exact radialBoundaryJets_angularFiber_composition Real.pi_ne_zero
    (hφ i) (hX i side) hY (hpositive i) (hφperiod i) (hjet side)

theorem exists_endpointFiberPullback_family
    {ι : Type*} (n : ℕ) {φ : ι → PolarPoint → ℝ}
    {X : ι → Bool → PolarPoint → ℝ} {l r c d κφ κX M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκφ : 0 < κφ) (hκX : 0 < κX) (hM : 0 ≤ M)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hX : ∀ i side, ContDiff ℝ ∞ (X i side))
    (hφLower : ∀ i x θ, κφ ≤ deriv (fun η => φ i (x, η)) θ)
    (hφperiod : ∀ i x θ, φ i (x, θ + Real.pi) = φ i (x, θ) + Real.pi)
    (hφodd : ∀ i x θ, φ i (x, -θ) = -φ i (x, θ))
    (hXvalue : ∀ i side θ, X i side (if side then r else l, θ) = if side then r else l)
    (hXlow : ∀ i side θ, κX ≤ radialPartial (X i side) (if side then r else l, θ))
    (hφraw : ∀ i (side : Bool) k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ k (φ i) (if side then r else l, θ)‖ ≤ M)
    (hXraw : ∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ k (X i side) (if side then r else l, θ)‖ ≤ M)
    (hXperiod : ∀ i side x θ, X i side (x, θ + Real.pi) = X i side (x, θ))
    (hXeven : ∀ i side x θ, X i side (x, -θ) = X i side (x, θ)) :
    ∃ Mσ : ℝ, 1 ≤ Mσ ∧
    let η := endpointFiberWidths n l r c d κX Mσ
    let B := endpointFiberLower n l r c d κX Mσ
    (∀ side, 0 < η side) ∧
      (∀ side, 2 * η side < (if side then r else c) - (if side then d else l)) ∧
      0 < B ∧ ∀ i,
      let Y := endpointFiberPullbackCoordinate n (φ i) (X i) l r c d κX Mσ
      ContDiff ℝ ∞ Y ∧
      (∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x) ∧
      (∀ θ, Y (l, θ) = l) ∧ (∀ θ, Y (r, θ) = r) ∧
      (∀ x θ, Y (x, θ + Real.pi) = Y (x, θ)) ∧
      (∀ x θ, Y (x, -θ) = Y (x, θ)) ∧
      (∀ x ∈ Icc c d, ∀ θ, Y =ᶠ[𝓝 (x, θ)] (Prod.fst : PolarPoint → ℝ)) ∧
      ∀ side k, k ≤ n + 1 → ∀ θ,
        radialBoundaryJet (fun p => Y (p.1, φ i p)) (if side then r else l) k θ =
          radialBoundaryJet (X i side) (if side then r else l) k θ := by
  have hpositive (i : ι) (p : PolarPoint) :
      0 < deriv (fun θ => φ i (p.1, θ)) p.2 :=
    hκφ.trans_le (hφLower i p.1 p.2)
  have hangle (i : ι) (side : Bool) (θ : ℝ) :
      κφ ≤ angularPartial (φ i) (if side then r else l, θ) := by
    rw [← deriv_cylinder_angular_slice ((hφ i).differentiable (by simp))]
    exact hφLower i _ θ
  have hradial (i : ι) (side : Bool) (θ : ℝ) :
      |radialPartial (φ i) (if side then r else l, θ)| ≤ M := by
    have hfirst : ‖fderiv ℝ (φ i) (if side then r else l, θ)‖ ≤ M := by
      simpa only [norm_iteratedFDeriv_one] using
        hφraw i side 1 le_rfl (by omega) θ
    have hunit :
        |radialPartial (φ i) (if side then r else l, θ)| ≤
          ‖fderiv ℝ (φ i) (if side then r else l, θ)‖ := by
      simpa [radialPartial, Prod.norm_def] using
        (fderiv ℝ (φ i) (if side then r else l, θ)).le_opNorm (1, 0)
    exact hunit.trans hfirst
  obtain ⟨Mσ, hMσ, hbound⟩ := exists_angularFiberBoundaryJets_bound (n + 1) hκφ hM
  refine ⟨Mσ, hMσ, endpointFiberPullback_family_of_bound hlc hcd hdr
    hκX (zero_le_one.trans hMσ) hφ hX hpositive hφperiod hφodd
    hXvalue hXlow hXperiod hXeven ?_⟩
  intro i side k hk hkn θ
  exact hbound (φ i) (X i side) Real.pi Real.pi_ne_zero (hφ i) (hX i side)
    (hpositive i) (hφperiod i) (if side then r else l)
    (hangle i side) (hradial i side) (hφraw i side) (hXraw i side) k hk hkn θ

end ContinuousFlexibility.Analysis
