import ContinuousFlexibility.Analysis.PositiveFiberMaterialTransport
import ContinuousFlexibility.Analysis.WholePositiveAmbientRadialIdentity
import ContinuousFlexibility.Analysis.EndpointFiberPullbackPolynomial

/-!
# Material ratios for the same displayed whole-component factory

One inverse-fiber envelope is chosen and used both for the geometry and
for the weight comparison. The angular patch keeps its original raw
parameter. Material constants precede every component, state family and
jet order; the inverse-envelope constants precede its numerical input.
The endpoint fields here may be the actual finite Taylor representatives.
-/

noncomputable section

universe u

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem exists_wholeComponentEndpointTransport_material_envelope
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ n : ℕ,
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
    ∀ {ι : Type u}, ∀ M : ℝ, 1 ≤ M → ∀ κφ κX : ℝ,
      0 < κφ → κφ ≤ 1 → κφ⁻¹ ≤ M → 0 < κX →
      ∀ ψ X : ι → Bool → PolarPoint → ℝ, ∀ l r : ℝ,
      let c := positiveMaterialLeftExit D l r
      let d := positiveMaterialRightExit D l r
      D.a ≤ l → l < r → r ≤ D.b →
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
      (l = D.a → ∀ i, X i false = (Prod.fst : PolarPoint → ℝ)) →
      (r = D.b → ∀ i, X i true = (Prod.fst : PolarPoint → ℝ)) →
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
      (∀ side k, k ≤ n + 1 → ∀ θ,
        radialBoundaryJet (fun p => (τ p).2) (if side then r else l) k θ =
          radialBoundaryJet (ψ i side) (if side then r else l) k θ) ∧
      ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
        T.H (τ p).1 / T.H p.1 ≤ K * T.E0 p.1 ^ A ∧
          T.M (τ p).1 / T.M p.1 ≤ K * T.E0 p.1 ^ A := by
  obtain ⟨K, A, hK, hA, hweights⟩ :=
    positiveFiberChart_material_ratios_for_exit_choice hT hRef
  refine ⟨K, A, hK, hA, ?_⟩
  intro n
  obtain ⟨C, hC, degree, hfactory⟩ := exists_endpointFiberPullback_polynomial_envelope n
  have hC' : 1 ≤ C * (2 : ℝ) ^ degree := by
    simpa only [one_mul] using mul_le_mul hC
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (show (0 : ℝ) ≤ 1 by norm_num) (zero_le_one.trans hC)
  refine ⟨C * 2 ^ degree, hC', degree, ?_⟩
  intro ι M hM κφ κX hκφ hκφone hκφinv hκX ψ X l r
  dsimp only
  intro ha hlr hb hψ hψangle hψjets hψperiod hψodd
    hX hXvalue hXlow hXjets hXperiod hXeven hambientL hambientR
  let c := positiveMaterialLeftExit D l r
  let d := positiveMaterialRightExit D l r
  obtain ⟨hlc, hcd, hdr, _, _⟩ := positiveMaterialExits_spec ha hlr hb
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
    dsimp only [φ, wholeComponentEndpointAngle]
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
  let Y := endpointFiberPullbackCoordinate n (φ i) (X i) l r c d κX Mσ
  rcases hfiber i with ⟨hY, hYlower, hleft, hright, hYperiod, hYeven, hYmiddle, hYjets⟩
  have hmiddle (x : ℝ) (hx : x ∈ Icc c d) (θ : ℝ) : Y (x, θ) = x :=
    (hYmiddle x hx θ).self_of_nhds
  have hidentityL (hl : l = D.a) (x : ℝ) (hx : x ∈ Icc l c) (θ : ℝ) :
      Y (x, θ) = x :=
    endpointFiberPullbackCoordinate_eq_fst_on_side n hcd false
      (hambientL hl i) (hη false) (hηgap false) (x, θ) hx.2
  have hidentityR (hr : r = D.b) (x : ℝ) (hx : x ∈ Icc d r) (θ : ℝ) :
      Y (x, θ) = x :=
    endpointFiberPullbackCoordinate_eq_fst_on_side n hcd true
      (hambientR hr i) (hη true) (hηgap true) (x, θ) hx.1
  refine ⟨wholeComponentTransportGeometry_of_scalars (hφ i) hY
    (half_pos hκφ) hB (hφlower i) hYlower (hφperiod i) (hφodd i)
    hYperiod hYeven hleft hright ((hang i).2.2.2.2.2.2) hYmiddle,
    hYjets, (hang i).2.2.1, ?_⟩
  exact hweights l r (φ i) Y (endpointFiberLower n l r c d κX Mσ)
    ha hlr hb hY hB hYlower hleft hright hmiddle hidentityL hidentityR

end ContinuousFlexibility.Analysis
