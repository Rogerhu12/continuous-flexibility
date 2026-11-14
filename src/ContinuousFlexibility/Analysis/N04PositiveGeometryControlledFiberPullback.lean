import ContinuousFlexibility.Analysis.EndpointFiberPullbackAssembly
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledAngularFiber

/-!
# A polynomial choice for the displayed inverse-fiber interpolation

The actual inverse boundary traces are bounded before choosing a member
of the family. The supplied-bound interpolation then uses exactly this
fixed monomial as its numerical envelope and keeps its displayed formula.
-/

noncomputable section

universe u

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04PositiveGeometry_exists_endpointFiberPullback_polynomial_envelope (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
    ∀ {ι : Type u}, ∀ M : ℝ, 1 ≤ M → ∀ κφ κX : ℝ,
      0 < κφ → κφ⁻¹ ≤ M → 0 < κX →
      ∀ φ : ι → PolarPoint → ℝ, ∀ X : ι → Bool → PolarPoint → ℝ,
      ∀ l r c d : ℝ, l < c → c < d → d < r →
      (∀ i, ContDiff ℝ ∞ (φ i)) →
      (∀ i side, ContDiff ℝ ∞ (X i side)) →
      (∀ i x θ, κφ ≤ deriv (fun η => φ i (x, η)) θ) →
      (∀ i x θ, φ i (x, θ + Real.pi) = φ i (x, θ) + Real.pi) →
      (∀ i x θ, φ i (x, -θ) = -φ i (x, θ)) →
      (∀ i side θ, X i side (if side then r else l, θ) = if side then r else l) →
      (∀ i side θ, 2 * κX ≤ radialPartial (X i side) (if side then r else l, θ)) →
      (∀ i (side : Bool) k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
        ‖iteratedFDeriv ℝ k (φ i) (if side then r else l, θ)‖ ≤ M) →
      (∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
        ‖iteratedFDeriv ℝ k (X i side) (if side then r else l, θ)‖ ≤ M) →
      (∀ i side x θ, X i side (x, θ + Real.pi) = X i side (x, θ)) →
      (∀ i side x θ, X i side (x, -θ) = X i side (x, θ)) →
    ∃ Mσ : ℝ, 1 ≤ Mσ ∧ Mσ ≤ C * M ^ degree ∧
    (∀ i side θ, 2 * κX ≤
      radialBoundaryJet (angularFiberPullback (φ i) (X i side))
        (if side then r else l) 1 θ) ∧
    (∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      |radialBoundaryJet (angularFiberPullback (φ i) (X i side))
        (if side then r else l) k θ| ≤ Mσ / 2) ∧
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
  obtain ⟨C, hC, degree, hbound⟩ :=
    n04PositiveGeometry_exists_angularFiberBoundaryJets_polynomial_envelope (n + 1)
  refine ⟨2 * C, by linarith, degree, ?_⟩
  intro ι M hM κφ κX hκφ hκφinv hκX φ X l r c d hlc hcd hdr
    hφ hX hφLower hφperiod hφodd hXvalue hXlow hφraw hXraw hXperiod hXeven
  have hR : 1 ≤ C * M ^ degree := by
    simpa only [one_mul] using mul_le_mul hC (one_le_pow₀ hM)
      (show (0 : ℝ) ≤ 1 by norm_num) (zero_le_one.trans hC)
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
      simpa only [norm_iteratedFDeriv_one] using hφraw i side 1 le_rfl (by omega) θ
    have hunit : |radialPartial (φ i) (if side then r else l, θ)| ≤
        ‖fderiv ℝ (φ i) (if side then r else l, θ)‖ := by
      simpa [radialPartial, Prod.norm_def] using
        (fderiv ℝ (φ i) (if side then r else l, θ)).le_opNorm (1, 0)
    exact hunit.trans hfirst
  have hMσ : 1 ≤ 2 * (C * M ^ degree) := by linarith
  have htraceLow (i : ι) (side : Bool) (θ : ℝ) :
      2 * κX ≤ radialBoundaryJet (angularFiberPullback (φ i) (X i side))
        (if side then r else l) 1 θ := by
    have hZ := contDiff_angularFiberPullback Real.pi_ne_zero (hφ i) (hX i side)
      (hpositive i) (hφperiod i)
    change 2 * κX ≤ iteratedDeriv 1
      (fun x => angularFiberPullback (φ i) (X i side) (x, θ)) (if side then r else l)
    rw [iteratedDeriv_one,
      deriv_cylinder_radial_slice (hZ.differentiable (by simp)) (if side then r else l) θ,
      radialPartial_angularFiberPullback_boundary Real.pi_ne_zero (hφ i) (hX i side)
        (hpositive i) (hφperiod i) (hXvalue i side)]
    exact hXlow i side _
  have htraceBound (i : ι) (side : Bool) (k : ℕ) (hk : 1 ≤ k)
      (hkn : k ≤ n + 1) (θ : ℝ) :
      |radialBoundaryJet (angularFiberPullback (φ i) (X i side))
        (if side then r else l) k θ| ≤ C * M ^ degree :=
    hbound hM hκφ hκφinv (φ i) (X i side) Real.pi Real.pi_ne_zero
      (hφ i) (hX i side) (hpositive i) (hφperiod i) (if side then r else l)
      (hangle i side) (hradial i side) (hφraw i side) (hXraw i side) k hk hkn θ
  refine ⟨2 * (C * M ^ degree), hMσ, le_of_eq (by ring), htraceLow, ?_, ?_⟩
  · intro i side k hk hkn θ
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      htraceBound i side k hk hkn θ
  apply endpointFiberPullback_family_of_bound hlc hcd hdr hκX
    (zero_le_one.trans hMσ) hφ hX hpositive hφperiod hφodd
    hXvalue (fun i side θ => by have h := hXlow i side θ; linarith) hXperiod hXeven
  intro i side k hk hkn θ
  exact (htraceBound i side k hk hkn θ).trans (by linarith)

end ContinuousFlexibility.Analysis
