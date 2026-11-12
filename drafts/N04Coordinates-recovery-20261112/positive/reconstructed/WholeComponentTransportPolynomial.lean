import ContinuousFlexibility.Analysis.WholeComponentTransportFactory
import ContinuousFlexibility.Analysis.EndpointFiberPullbackPolynomial

/-!
# A fixed polynomial envelope for the same whole-component transport

The angular patch retains its original parameter M. Its angular lower
bound is kappa/2, so the inverse-fiber theorem is applied at 2M. The
resulting coefficient absorbs only the fixed factor 2^degree; neither
the actual angular patch nor either endpoint field is replaced.
This is a new reconstruction after the workspace reset.
-/

noncomputable section

universe u

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem exists_wholeComponentEndpointTransport_polynomial_envelope (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
    ∀ {ι : Type u}, ∀ M : ℝ, 1 ≤ M → ∀ κφ κX : ℝ,
      0 < κφ → κφ ≤ 1 → κφ⁻¹ ≤ M → 0 < κX →
      ∀ ψ X : ι → Bool → PolarPoint → ℝ, ∀ l r c d : ℝ,
      l < c → c < d → d < r →
      (∀ i side, ContDiff ℝ ∞ (ψ i side)) →
      (∀ i side θ, κφ ≤ angularPartial (ψ i side) (if side then r else l, θ)) →
      (∀ i side k, 1 ≤ k → k ≤ n + 2 → ∀ θ,
        ‖iteratedFDeriv ℝ k (ψ i side) (if side then r else l, θ)‖ ≤ M) →
      (∀ i side x θ, ψ i side (x, θ + Real.pi) = ψ i side (x, θ) + Real.pi) →
      (∀ i side x θ, ψ i side (x, -θ) = -ψ i side (x, θ)) →
      (∀ i side, ContDiff ℝ ∞ (X i side)) →
      (∀ i side θ, X i side (if side then r else l, θ) = if side then r else l) →
      (∀ i side θ, κX ≤ radialPartial (X i side) (if side then r else l, θ)) →
      (∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
        ‖iteratedFDeriv ℝ k (X i side) (if side then r else l, θ)‖ ≤ M) →
      (∀ i side x θ, X i side (x, θ + Real.pi) = X i side (x, θ)) →
      (∀ i side x θ, X i side (x, -θ) = X i side (x, θ)) →
    let δ := endpointAngularWidth (n + 1) l r c d κφ M
    0 < δ ∧ δ ≤ 1 ∧ 2 * δ < r - l ∧ δ < c - l ∧ δ < r - d ∧
      ∃ Mσ : ℝ, 1 ≤ Mσ ∧ Mσ ≤ C * M ^ degree ∧
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
  obtain ⟨C, hC, degree, hfactory⟩ := exists_endpointFiberPullback_polynomial_envelope n
  have hC' : 1 ≤ C * (2 : ℝ) ^ degree := by
    simpa only [one_mul] using mul_le_mul hC
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (show (0 : ℝ) ≤ 1 by norm_num) (zero_le_one.trans hC)
  refine ⟨C * 2 ^ degree, hC', degree, ?_⟩
  intro ι M hM κφ κX hκφ hκφone hκφinv hκX ψ X l r c d hlc hcd hdr
    hψ hψangle hψjets hψperiod hψodd hX hXvalue hXlow hXjets hXperiod hXeven
  have hMn : 0 ≤ M := zero_le_one.trans hM
  have hMtwo : 1 ≤ 2 * M := by linarith
  have hMM : M ≤ 2 * M := by linarith
  have hκhalf : (κφ / 2)⁻¹ ≤ 2 * M := by
    simpa only [inv_div, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hκφinv (by norm_num : (0 : ℝ) ≤ 2)
  have hang := rawEndpointAngularInterpolation_family (n + 1) hlc hcd hdr
    hκφ hκφone hMn hψ hψangle hψjets hψperiod hψodd
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
      ‖iteratedFDeriv ℝ k (φ i) (if side then r else l, θ)‖ ≤ 2 * M := by
    rw [(hang i).2.2.2.1 side k hkn θ]
    exact (hψjets i side k hk (by omega) θ).trans hMM
  obtain ⟨Mσ, hMσ, hcost, hη, hηgap, hB, hfiber⟩ :=
    hfactory (2 * M) hMtwo (κφ / 2) κX (half_pos hκφ) hκhalf hκX φ X l r c d
      hlc hcd hdr hφ hX hφlower hφperiod hφodd hXvalue hXlow hφraw
      (fun i side k hk hkn θ => (hXjets i side k hk hkn θ).trans hMM) hXperiod hXeven
  have hcost' : Mσ ≤ (C * 2 ^ degree) * M ^ degree := by
    simpa only [mul_pow, mul_assoc] using hcost
  refine ⟨hδ, hδone, hδgap, hδL, hδR, Mσ, hMσ, hcost', hη, hηgap, hB, ?_⟩
  intro i
  rcases hfiber i with ⟨hY, hYlower, hleft, hright, hYperiod, hYeven, hYmiddle, hYjets⟩
  refine ⟨wholeComponentTransportGeometry_of_scalars (hφ i) hY
    (half_pos hκφ) hB (hφlower i) hYlower (hφperiod i) (hφodd i)
    hYperiod hYeven hleft hright ((hang i).2.2.2.2.2.2) hYmiddle,
    hYjets, (hang i).2.2.1⟩

end ContinuousFlexibility.Analysis
