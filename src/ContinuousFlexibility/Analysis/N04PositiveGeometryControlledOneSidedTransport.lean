import ContinuousFlexibility.Analysis.OneSidedWholeComponentTransport
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledWholeTransport

/-!
# Polynomial inverse choice for the actual one-sided endpoint fields

The same finite Taylor representatives preserve the true closed-root
jets. They now feed the polynomial whole-component factory. The new
coefficient and degree are selected before all endpoint data and states;
no common infinite-order collar is assumed or manufactured.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual positive-order coefficient field used by the displayed
radial interpolation after the finite endpoint representatives. -/
def n04PositiveGeometry_oneSidedFiberData (n : ℕ)
    (ψ X : Bool → PolarPoint → ℝ) (l r c d κφ M : ℝ)
    (side : Bool) : ℕ → ℝ → ℝ :=
  radialBoundaryJet (angularFiberPullback
    (wholeComponentEndpointAngle n (oneSidedEndpointRepresentative (n + 2) l r ψ)
      l r c d κφ M)
    (oneSidedEndpointRepresentative (n + 1) l r X side)) (if side then r else l)

private theorem polynomial_endpointRepresentative_fderiv_eq
    {F : PolarPoint → ℝ} {a b x : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hx : x ∈ Icc a b) (hFx : ∀ θ, ContDiffAt ℝ ∞ F (x, θ))
    {n : ℕ} (hn : 1 ≤ n) (θ : ℝ) :
    fderiv ℝ (oneSidedBoundaryTaylorRepresentative n x F) (x, θ) =
      fderiv ℝ F (x, θ) := by
  have he := iteratedFDeriv_oneSidedBoundaryTaylorRepresentative hab hF hx hFx n hn θ
  apply ContinuousLinearMap.ext
  intro v
  simpa only [iteratedFDeriv_one_apply] using
    congrArg (fun T : PolarPoint [×1]→L[ℝ] ℝ => T (fun _ => v)) he

theorem n04PositiveGeometry_exists_oneSidedWholeComponentTransport_polynomial_envelope (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
    ∀ {ι : Type u} {ψ X : ι → Bool → PolarPoint → ℝ}
    {a b : Bool → ℝ} {l r c d κφ κX M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hab : ∀ side, a side < b side)
    (hend : ∀ side, (if side then r else l) ∈ Icc (a side) (b side))
    (hκφ : 0 < κφ) (hκφone : κφ ≤ 1) (hκφinv : κφ⁻¹ ≤ M)
    (hκX : 0 < κX) (hM : 1 ≤ M)
    (hψ : ∀ i side, ContDiffOn ℝ ∞ (ψ i side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hψroot : ∀ i side θ, ContDiffAt ℝ ∞ (ψ i side) (if side then r else l, θ))
    (hψangle : ∀ i side θ, κφ ≤ angularPartial (ψ i side) (if side then r else l, θ))
    (hψjets : ∀ i side k, 1 ≤ k → k ≤ n + 2 → ∀ θ,
      ‖iteratedFDeriv ℝ k (ψ i side) (if side then r else l, θ)‖ ≤ M)
    (hψperiod : ∀ i side, ∀ x ∈ Ioo (a side) (b side), ∀ θ,
      ψ i side (x, θ + Real.pi) = ψ i side (x, θ) + Real.pi)
    (hψodd : ∀ i side, ∀ x ∈ Ioo (a side) (b side), ∀ θ,
      ψ i side (x, -θ) = -ψ i side (x, θ))
    (hX : ∀ i side, ContDiffOn ℝ ∞ (X i side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hXroot : ∀ i side θ, ContDiffAt ℝ ∞ (X i side) (if side then r else l, θ))
    (hXvalue : ∀ i side θ, X i side (if side then r else l, θ) = if side then r else l)
    (hXlow : ∀ i side θ, 2 * κX ≤ radialPartial (X i side) (if side then r else l, θ))
    (hXjets : ∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ k (X i side) (if side then r else l, θ)‖ ≤ M)
    (hXperiod : ∀ i side, ∀ x ∈ Ioo (a side) (b side), ∀ θ,
      X i side (x, θ + Real.pi) = X i side (x, θ))
    (hXeven : ∀ i side, ∀ x ∈ Ioo (a side) (b side), ∀ θ,
      X i side (x, -θ) = X i side (x, θ)),
    let δ := endpointAngularWidth (n + 1) l r c d κφ M
    0 < δ ∧ δ ≤ 1 ∧ 2 * δ < r - l ∧ δ < c - l ∧ δ < r - d ∧
      ∃ Mσ : ℝ, 1 ≤ Mσ ∧ Mσ ≤ C * M ^ degree ∧
      (∀ i side θ, 2 * κX ≤
        n04PositiveGeometry_oneSidedFiberData n (ψ i) (X i) l r c d κφ M side 1 θ) ∧
      (∀ i side k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
        |n04PositiveGeometry_oneSidedFiberData n (ψ i) (X i)
          l r c d κφ M side k θ| ≤ Mσ / 2) ∧
      let η := endpointFiberWidths n l r c d κX Mσ
      let B := endpointFiberLower n l r c d κX Mσ
      (∀ side, 0 < η side) ∧
      (∀ side, 2 * η side < (if side then r else c) - (if side then d else l)) ∧
      0 < B ∧ ∀ i,
      let τ := oneSidedWholeComponentTransport n (ψ i) (X i) l r c d κφ κX M Mσ
      let σ := oneSidedWholeComponentTransportInverse n (ψ i) (X i) l r c d κφ κX M Mσ
      WholeComponentTransportGeometry τ σ l r c d (B * (κφ / 2)) ∧
      (∀ side k, k ≤ n + 1 → ∀ θ,
        iteratedFDeriv ℝ k (fun p => (τ p).1) (if side then r else l, θ) =
          iteratedFDeriv ℝ k (X i side) (if side then r else l, θ)) ∧
      (∀ side k, k ≤ n + 1 → ∀ θ,
        iteratedFDeriv ℝ k (fun p => (τ p).2) (if side then r else l, θ) =
          iteratedFDeriv ℝ k (ψ i side) (if side then r else l, θ)) ∧
      ∀ side k, k ≤ n + 1 → ∀ θ,
        iteratedFDeriv ℝ k τ (if side then r else l, θ) =
          iteratedFDeriv ℝ k (fun p => (X i side p, ψ i side p))
            (if side then r else l, θ) := by
  obtain ⟨C, hC, degree, hfactory⟩ :=
    n04PositiveGeometry_exists_wholeComponentEndpointTransport_polynomial_envelope n
  refine ⟨C, hC, degree, ?_⟩
  intro ι ψ X a b l r c d κφ κX M hlc hcd hdr hab hend
    hκφ hκφone hκφinv hκX hM hψ hψroot hψangle hψjets hψperiod hψodd
    hX hXroot hXvalue hXlow hXjets hXperiod hXeven
  let Ψ : ι → Bool → PolarPoint → ℝ := fun i =>
    oneSidedEndpointRepresentative (n + 2) l r (ψ i)
  let Y : ι → Bool → PolarPoint → ℝ := fun i =>
    oneSidedEndpointRepresentative (n + 1) l r (X i)
  have hΨ (i : ι) (side : Bool) : ContDiff ℝ ∞ (Ψ i side) :=
    contDiff_oneSidedBoundaryTaylorRepresentative _ (hψroot i side) _
  have hY (i : ι) (side : Bool) : ContDiff ℝ ∞ (Y i side) :=
    contDiff_oneSidedBoundaryTaylorRepresentative _ (hXroot i side) _
  have hΨangle (i : ι) (side : Bool) (θ : ℝ) :
      κφ ≤ angularPartial (Ψ i side) (if side then r else l, θ) := by
    dsimp only [Ψ, oneSidedEndpointRepresentative]
    unfold angularPartial
    rw [polynomial_endpointRepresentative_fderiv_eq (hab side) (hψ i side)
      (hend side) (hψroot i side) (by omega : 1 ≤ n + 2)]
    exact hψangle i side θ
  have hYlow (i : ι) (side : Bool) (θ : ℝ) :
      2 * κX ≤ radialPartial (Y i side) (if side then r else l, θ) := by
    dsimp only [Y, oneSidedEndpointRepresentative]
    unfold radialPartial
    rw [polynomial_endpointRepresentative_fderiv_eq (hab side) (hX i side)
      (hend side) (hXroot i side) (by omega : 1 ≤ n + 1)]
    exact hXlow i side θ
  have hΨjets (i : ι) (side : Bool) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 2) (θ : ℝ) :
      ‖iteratedFDeriv ℝ k (Ψ i side) (if side then r else l, θ)‖ ≤ M := by
    dsimp only [Ψ, oneSidedEndpointRepresentative]
    rw [iteratedFDeriv_oneSidedBoundaryTaylorRepresentative
      (hab side) (hψ i side) (hend side) (hψroot i side) (n + 2) hkn]
    exact hψjets i side k hk hkn θ
  have hYjets (i : ι) (side : Bool) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) (θ : ℝ) :
      ‖iteratedFDeriv ℝ k (Y i side) (if side then r else l, θ)‖ ≤ M := by
    dsimp only [Y, oneSidedEndpointRepresentative]
    rw [iteratedFDeriv_oneSidedBoundaryTaylorRepresentative
      (hab side) (hX i side) (hend side) (hXroot i side) (n + 1) hkn]
    exact hXjets i side k hk hkn θ
  have hYvalue (i : ι) (side : Bool) (θ : ℝ) :
      Y i side (if side then r else l, θ) = if side then r else l := by
    have he := radialBoundaryJet_oneSidedBoundaryTaylorRepresentative
      (X i side) (n + 1) (if side then r else l) (Nat.zero_le _) θ
    dsimp only [Y, oneSidedEndpointRepresentative]
    simpa only [radialBoundaryJet, iteratedDeriv_zero, hXvalue i side θ] using he
  have hout := hfactory M hM κφ κX hκφ hκφone hκφinv hκX Ψ Y l r c d
    hlc hcd hdr hΨ hΨangle hΨjets
    (fun i side => oneSidedBoundaryTaylorRepresentative_lift
      (hab side) (hend side) (hψroot i side) (hψperiod i side) (n + 2))
    (fun i side => oneSidedBoundaryTaylorRepresentative_odd
      (hab side) (hend side) (hψroot i side) (hψodd i side) (n + 2))
    hY hYvalue hYlow hYjets
    (fun i side => oneSidedBoundaryTaylorRepresentative_angleInvariant
      (hab side) (hend side) (hXroot i side) (contDiff_id.add contDiff_const)
      (hXperiod i side) (n + 1))
    (fun i side => oneSidedBoundaryTaylorRepresentative_angleInvariant
      (hab side) (hend side) (hXroot i side) contDiff_id.neg
      (hXeven i side) (n + 1))
  dsimp only at hout ⊢
  rcases hout with ⟨hδ, hδone, hδgap, hδL, hδR, Mσ, hMσ, hcost,
    htraceLow, htraceBound, hη, hηgap, hB, hout⟩
  refine ⟨hδ, hδone, hδgap, hδL, hδR, Mσ, hMσ, hcost,
    htraceLow, htraceBound, hη, hηgap, hB, ?_⟩
  intro i
  rcases hout i with ⟨hgeometry, hradial, hangular⟩
  let τ := oneSidedWholeComponentTransport n (ψ i) (X i) l r c d κφ κX M Mσ
  have hτ : ContDiff ℝ ∞ τ := hgeometry.smooth
  have hfirst (side : Bool) (k : ℕ) (hk : k ≤ n + 1) (θ : ℝ) :
      iteratedFDeriv ℝ k (fun p => (τ p).1) (if side then r else l, θ) =
        iteratedFDeriv ℝ k (X i side) (if side then r else l, θ) := by
    apply iteratedFDeriv_eq_of_radialBoundaryJets_eq_on_closedStrip
      (hab side) hτ.fst.contDiffOn (hX i side) (hend side)
      (fun _ => hτ.fst.contDiffAt) (hXroot i side) (N := n + 1) _ hk θ
    intro j hj η
    exact (hradial side j hj η).trans
      (radialBoundaryJet_oneSidedBoundaryTaylorRepresentative
        (X i side) (n + 1) _ hj η)
  have hsecond (side : Bool) (k : ℕ) (hk : k ≤ n + 1) (θ : ℝ) :
      iteratedFDeriv ℝ k (fun p => (τ p).2) (if side then r else l, θ) =
        iteratedFDeriv ℝ k (ψ i side) (if side then r else l, θ) := by
    apply iteratedFDeriv_eq_of_radialBoundaryJets_eq_on_closedStrip
      (hab side) hτ.snd.contDiffOn (hψ i side) (hend side)
      (fun _ => hτ.snd.contDiffAt) (hψroot i side) (N := n + 1) _ hk θ
    intro j hj η
    exact (hangular side j hj η).trans
      (radialBoundaryJet_oneSidedBoundaryTaylorRepresentative
        (ψ i side) (n + 2) _ (by omega) η)
  refine ⟨hgeometry, hfirst, hsecond, ?_⟩
  intro side k hk θ
  have hτpair : τ = fun p => ((τ p).1, (τ p).2) :=
    funext (fun p => (Prod.eta (τ p)).symm)
  change iteratedFDeriv ℝ k τ (if side then r else l, θ) = _
  conv_lhs => rw [hτpair]
  rw [iteratedFDeriv_prodMk hτ.fst.contDiffAt hτ.snd.contDiffAt
      (by simp : (k : ℕ∞ω) ≤ ∞),
    iteratedFDeriv_prodMk (hXroot i side θ) (hψroot i side θ)
      (by simp : (k : ℕ∞ω) ≤ ∞), hfirst side k hk θ, hsecond side k hk θ]


end ContinuousFlexibility.Analysis
