import ContinuousFlexibility.Analysis.OneSidedBoundaryTaylorRepresentative
import ContinuousFlexibility.Analysis.PositiveChartRangeGeometry

/-!
# A positive reference chart from actual finite radial endpoint jets

The endpoint functions need only smoothness on the original open side
and ordinary smoothness at each point of its root circle. Their radial
Taylor representatives are global smooth functions and are independent
of angle when the original fields are radial on the open side. The
existing positive interpolation then gives one genuine reference chart
and height with the prescribed finite ordinary jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def radialEndpointTaylorSlice (n : ℕ) (c : ℝ)
    (f : PolarPoint → ℝ) (x : ℝ) : ℝ :=
  oneSidedBoundaryTaylorRepresentative n c f (x, 0)

theorem contDiff_radialEndpointTaylorSlice
    {f : PolarPoint → ℝ} (c : ℝ)
    (hf : ∀ θ, ContDiffAt ℝ ∞ f (c, θ)) (n : ℕ) :
    ContDiff ℝ ∞ (radialEndpointTaylorSlice n c f) :=
  (contDiff_oneSidedBoundaryTaylorRepresentative c hf n).comp
    (contDiff_id.prodMk contDiff_const)

theorem radialEndpointTaylorSlice_value
    (f : PolarPoint → ℝ) (n : ℕ) (c : ℝ) :
    radialEndpointTaylorSlice n c f c = f (c, 0) := by
  simpa only [radialEndpointTaylorSlice, radialBoundaryJet, iteratedDeriv_zero] using
    radialBoundaryJet_oneSidedBoundaryTaylorRepresentative f n c (Nat.zero_le n) 0

theorem radialEndpointTaylorSlice_deriv
    (f : PolarPoint → ℝ) {n : ℕ} (hn : 1 ≤ n) (c : ℝ) :
    deriv (radialEndpointTaylorSlice n c f) c =
      deriv (fun x : ℝ => f (x, 0)) c := by
  change deriv (fun x : ℝ => oneSidedBoundaryTaylorRepresentative n c f (x, 0)) c =
    deriv (fun x : ℝ => f (x, 0)) c
  simpa only [radialBoundaryJet, iteratedDeriv_one] using
    radialBoundaryJet_oneSidedBoundaryTaylorRepresentative f n c hn 0

/-- Radiality on the original side makes the full Taylor representative
equal to its zero-angle scalar slice on the whole plane. -/
theorem radialEndpointTaylorSlice_lift
    {f : PolarPoint → ℝ} {a b c : ℝ}
    (hab : a < b) (hc : c ∈ Icc a b)
    (hfc : ∀ θ, ContDiffAt ℝ ∞ f (c, θ))
    (hradial : ∀ x ∈ Ioo a b, ∀ θ, f (x, θ) = f (x, 0)) (n : ℕ) :
    (fun p : PolarPoint => radialEndpointTaylorSlice n c f p.1) =
      oneSidedBoundaryTaylorRepresentative n c f := by
  funext p
  exact oneSidedBoundaryTaylorRepresentative_angleInvariant
    (τ := fun _ : ℝ => 0) hab hc hfc contDiff_const
    (fun x hx θ => (hradial x hx θ).symm) n p.1 p.2

theorem radialEndpointTaylorSlice_fullJets
    {f : PolarPoint → ℝ} {a b c : ℝ}
    (hab : a < b) (hc : c ∈ Icc a b)
    (hf : ContDiffOn ℝ ∞ f (Ioo a b ×ˢ (univ : Set ℝ)))
    (hfc : ∀ θ, ContDiffAt ℝ ∞ f (c, θ))
    (hradial : ∀ x ∈ Ioo a b, ∀ θ, f (x, θ) = f (x, 0))
    (n : ℕ) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedFDeriv ℝ k (fun p : PolarPoint => radialEndpointTaylorSlice n c f p.1)
        (c, θ) = iteratedFDeriv ℝ k f (c, θ) := by
  rw [radialEndpointTaylorSlice_lift hab hc hfc hradial n]
  exact iteratedFDeriv_oneSidedBoundaryTaylorRepresentative hab hf hc hfc n hk θ

/-- The two actual endpoint fields determine a reference map from the
physical interval to `(0,1)`. The conclusion matches their full ordinary
jets through one fixed finite order; no common infinite-smoothness
neighborhood of the original fields is assumed. -/
theorem exists_positiveReferenceFiniteRadialJets
    {F : Set ℝ} (hF : IsClosed F) {l r : ℝ}
    (hl : l ∉ F) (hr : r ∉ F) (hlr : l < r)
    {a b : Bool → ℝ} {y h : Bool → PolarPoint → ℝ}
    (hab : ∀ side, a side < b side)
    (hc : ∀ side, (if side then r else l) ∈ Icc (a side) (b side))
    (hy : ∀ side, ContDiffOn ℝ ∞ (y side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hh : ∀ side, ContDiffOn ℝ ∞ (h side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hyc : ∀ side θ, ContDiffAt ℝ ∞ (y side) (if side then r else l, θ))
    (hhc : ∀ side θ, ContDiffAt ℝ ∞ (h side) (if side then r else l, θ))
    (hyr : ∀ side x, x ∈ Ioo (a side) (b side) → ∀ θ,
      y side (x, θ) = y side (x, 0))
    (hhr : ∀ side x, x ∈ Ioo (a side) (b side) → ∀ θ,
      h side (x, θ) = h side (x, 0))
    (hyvalue : ∀ side, y side (if side then r else l, 0) =
      (if side then (1 : ℝ) else 0))
    (hyslope : ∀ side, 0 < deriv (fun x : ℝ => y side (x, 0))
      (if side then r else l))
    (hhpositive : ∀ side, 0 < h side (if side then r else l, 0))
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ Y H : ℝ → ℝ,
      PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
        (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1 ∧
      (∀ x ∈ F, H x = 1) ∧
      (∀ side θ k, k ≤ n →
        iteratedFDeriv ℝ k (fun p : PolarPoint => Y p.1)
            (if side then r else l, θ) =
          iteratedFDeriv ℝ k (y side) (if side then r else l, θ)) ∧
      (∀ side θ k, k ≤ n →
        iteratedFDeriv ℝ k (fun p : PolarPoint => H p.1)
            (if side then r else l, θ) =
          iteratedFDeriv ℝ k (h side) (if side then r else l, θ)) := by
  let ys : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice n (if side then r else l) (y side)
  let hs : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice n (if side then r else l) (h side)
  have hys (side : Bool) : ContDiff ℝ ∞ (ys side) :=
    contDiff_radialEndpointTaylorSlice _ (hyc side) n
  have hhs (side : Bool) : ContDiff ℝ ∞ (hs side) :=
    contDiff_radialEndpointTaylorSlice _ (hhc side) n
  have hysv (side : Bool) : ys side (if side then r else l) =
      (if side then (1 : ℝ) else 0) :=
    (radialEndpointTaylorSlice_value (y side) n _).trans (hyvalue side)
  have hysd (side : Bool) : 0 < deriv (ys side) (if side then r else l) := by
    change 0 < deriv (radialEndpointTaylorSlice n _ (y side)) _
    rw [radialEndpointTaylorSlice_deriv _ hn]
    exact hyslope side
  have hhsp (side : Bool) : 0 < hs side (if side then r else l) := by
    change 0 < radialEndpointTaylorSlice n _ (h side) _
    rw [radialEndpointTaylorSlice_value]
    exact hhpositive side
  obtain ⟨δ, hδ, hδρ, hδε, hgap, havoidL, havoidR,
    hY, hYpos, hYlower, hYbij, hYinv, hYimage, hH, hHpos, hHf, hg⟩ :=
    exists_positiveReferenceInterpolation hF hl hr hlr
      (ε := 1) (ρL := 1) (ρR := 1) zero_lt_one zero_lt_one zero_lt_one
      (fun _ _ => (hys false).contDiffAt) (fun _ _ => (hys true).contDiffAt)
      (fun _ _ => (hhs false).contDiffAt) (fun _ _ => (hhs true).contDiffAt)
      (hysv false) (hysv true) (hysd false) (hysd true) (hhsp false) (hhsp true)
  let Y := positiveReferenceCoordinate l r δ (deriv (ys false)) (deriv (ys true))
  let H := positiveReferenceHeight l r δ (hs false) (hs true)
  have hYleft : Y l = 0 := (hg false).1.self_of_nhds.trans (hysv false)
  have hYright : Y r = 1 := (hg true).1.self_of_nhds.trans (hysv true)
  refine ⟨Y, H, positiveReferenceCylinder_rangeGeometry
    hY hYpos hYbij hYinv hH hHpos hYleft hYright, hHf, ?_, ?_⟩
  · intro side θ k hk
    have he : Y =ᶠ[𝓝 (if side then r else l)] ys side := by
      cases side with
      | false => exact (hg false).1
      | true => exact (hg true).1
    have hlift : (fun p : PolarPoint => Y p.1) =ᶠ[𝓝 (if side then r else l, θ)]
        (fun p : PolarPoint => ys side p.1) :=
      he.comp_tendsto (continuous_fst.tendsto (if side then r else l, θ))
    exact (hlift.iteratedFDeriv ℝ k).eq_of_nhds.trans
      (radialEndpointTaylorSlice_fullJets (hab side) (hc side) (hy side) (hyc side)
        (hyr side) n hk θ)
  · intro side θ k hk
    have he : H =ᶠ[𝓝 (if side then r else l)] hs side := by
      cases side with
      | false => exact (hg false).2
      | true => exact (hg true).2
    have hlift : (fun p : PolarPoint => H p.1) =ᶠ[𝓝 (if side then r else l, θ)]
        (fun p : PolarPoint => hs side p.1) :=
      he.comp_tendsto (continuous_fst.tendsto (if side then r else l, θ))
    exact (hlift.iteratedFDeriv ℝ k).eq_of_nhds.trans
      (radialEndpointTaylorSlice_fullJets (hab side) (hc side) (hh side) (hhc side)
        (hhr side) n hk θ)

end ContinuousFlexibility.Analysis
