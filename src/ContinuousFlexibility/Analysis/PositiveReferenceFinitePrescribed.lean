module

public import ContinuousFlexibility.Analysis.PositiveReferenceTaylorPrescribedWidth
public import ContinuousFlexibility.Analysis.PositiveReferenceValueEnvelope

/-!
# The actual finite reference construction at a displayed width

This is the prescribed-width counterpart of the qualitative finite
reference factory. It uses its actual radial Taylor slices, integral
coordinate and clipped-log height. The finite numerical data determine
the width before the coordinate is constructed. No assertion identifies
this new choice with a previously chosen qualitative interpolation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveReferenceFiniteRadialJets_prescribed
    (n : ℕ) {l r κ M : ℝ} (hlr : l < r) (hκ : 0 < κ) (hM : 0 ≤ M)
    {a b : Bool → ℝ} {y h : Bool → PolarPoint → ℝ}
    (hab : ∀ side, a side < b side)
    (hc : ∀ side : Bool, (if side then r else l) ∈ Icc (a side) (b side))
    (hy : ∀ side, ContDiffOn ℝ ∞ (y side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hh : ∀ side, ContDiffOn ℝ ∞ (h side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hyc : ∀ (side : Bool) θ, ContDiffAt ℝ ∞ (y side) (if side then r else l, θ))
    (hhc : ∀ (side : Bool) θ, ContDiffAt ℝ ∞ (h side) (if side then r else l, θ))
    (hyr : ∀ side x, x ∈ Ioo (a side) (b side) → ∀ θ,
      y side (x, θ) = y side (x, 0))
    (hhr : ∀ side x, x ∈ Ioo (a side) (b side) → ∀ θ,
      h side (x, θ) = h side (x, 0))
    (hyvalue : ∀ side : Bool, y side (if side then r else l, 0) =
      (if side then (1 : ℝ) else 0))
    (hyslope : ∀ side : Bool, κ ≤ radialBoundaryJet (y side) (if side then r else l) 1 0)
    (hhpositive : ∀ side : Bool, κ ≤ radialBoundaryJet (h side) (if side then r else l) 0 0)
    (hybound : ∀ (side : Bool) j, 1 ≤ j → j ≤ n + 1 →
      |radialBoundaryJet (y side) (if side then r else l) j 0| ≤ M)
    (hhbound : ∀ (side : Bool) j, j ≤ n + 1 →
      |radialBoundaryJet (h side) (if side then r else l) j 0| ≤ M) :
    let δ := positiveReferenceTaylorWidth n l r κ M
    let ys := fun side : Bool => radialEndpointTaylorSlice (n + 1)
      (if side then r else l) (y side)
    let hs := fun side : Bool => radialEndpointTaylorSlice (n + 1)
      (if side then r else l) (h side)
    let Y := positiveReferenceCoordinate l r δ (deriv (ys false)) (deriv (ys true))
    let H := positiveReferenceHeight l r δ (hs false) (hs true)
    PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1 ∧
    (∀ (side : Bool) (θ : ℝ) (k : ℕ), k ≤ n + 1 →
      iteratedFDeriv ℝ k (fun p : PolarPoint => Y p.1) (if side then r else l, θ) =
        iteratedFDeriv ℝ k (y side) (if side then r else l, θ)) ∧
    (∀ (side : Bool) (θ : ℝ) (k : ℕ), k ≤ n + 1 →
      iteratedFDeriv ℝ k (fun p : PolarPoint => H p.1) (if side then r else l, θ) =
        iteratedFDeriv ℝ k (h side) (if side then r else l, θ)) ∧
    (∀ x, min (κ / 2) (1 / (2 * (r - l))) ≤ deriv Y x ∧
      deriv Y x ≤ max (M + ((n + 1 : ℕ) : ℝ) * M) (2 / (r - l))) ∧
    ∀ x, H x ≤ (max 1 (max (2 * M) (2 / κ))) ^ 2 ∧
      (H x)⁻¹ ≤ (max 1 (max (2 * M) (2 / κ))) ^ 2 := by
  let δ := positiveReferenceTaylorWidth n l r κ M
  let ys : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (if side then r else l) (y side)
  let hs : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (if side then r else l) (h side)
  let Y := positiveReferenceCoordinate l r δ (deriv (ys false)) (deriv (ys true))
  let H := positiveReferenceHeight l r δ (hs false) (hs true)
  let L : ℝ := M + ((n + 1 : ℕ) : ℝ) * M
  have hspan : 0 < r - l := sub_pos.mpr hlr
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  obtain ⟨hδ, hδone, hfour, hgap, hsmall, hmass, _⟩ :=
    positiveReferenceTaylorWidth_margins n hlr hκ hM
  have hys (side : Bool) : ContDiff ℝ ∞ (ys side) :=
    contDiff_radialEndpointTaylorSlice _ (hyc side) (n + 1)
  have hhs (side : Bool) : ContDiff ℝ ∞ (hs side) :=
    contDiff_radialEndpointTaylorSlice _ (hhc side) (n + 1)
  have hds (side : Bool) (x : ℝ) : ContDiffAt ℝ ∞ (deriv (ys side)) x :=
    (hys side).contDiffAt.derivWithin (by simp)
  have hcollar (side : Bool) (x : ℝ) (hx : x ∈ Metric.ball (if side then r else l) δ) :
      κ / 2 ≤ deriv (ys side) x ∧ |deriv (ys side) x| ≤ L ∧
        κ / 2 ≤ hs side x ∧ |hs side x| ≤ 2 * M := by
    have hx' : |x - (if side then r else l)| ≤ δ :=
      (show |x - (if side then r else l)| < δ from
        (by simpa only [Metric.mem_ball, Real.dist_eq] using hx)).le
    exact radialEndpointTaylorSlice_collar_bounds n hδ.le hδone hM hx'
      (hyslope side) (hhpositive side) (hybound side) (hhbound side) hsmall
  have hder (x : ℝ) : min (κ / 2) (1 / (2 * (r - l))) ≤ deriv Y x ∧
      deriv Y x ≤ max L (2 / (r - l)) :=
    positiveReferenceCoordinate_deriv_bounds hδ hfour (half_pos hκ) hL
      (fun side x _ => hds side x) (fun side x hx => (hcollar side x hx).1)
      (fun side x hx => (hcollar side x hx).2.1) hmass x
  have hsmallmass : positiveReferenceEndMass l r δ (deriv (ys false))
      (deriv (ys true)) < 1 :=
    ((positiveReferenceEndMass_le hδ hL (fun x _ => hds false x)
      (fun x _ => hds true x) (fun x hx => (hcollar false x hx).2.1)
      (fun x hx => (hcollar true x hx).2.1)).trans hmass).trans_lt (by norm_num)
  obtain ⟨hbij, hinv⟩ := positiveReferenceCoordinate_bijective_smoothInverse hδ hgap
    (fun x _ => hds false x) (fun x _ => hds true x) (half_pos hκ)
    (fun x hx => (hcollar false x hx).1) (fun x hx => (hcollar true x hx).1) hsmallmass
  have hY : ContDiff ℝ ∞ Y := contDiff_positiveReferenceCoordinate hδ
    (fun x _ => hds false x) (fun x _ => hds true x)
  have hYpos (x : ℝ) : 0 < deriv Y x :=
    (lt_min (half_pos hκ) (by positivity : 0 < 1 / (2 * (r - l)))).trans_le (hder x).1
  have hHpos (side : Bool) (x : ℝ) (hx : x ∈ Metric.ball (if side then r else l) δ) :
      0 < hs side x := (half_pos hκ).trans_le (hcollar side x hx).2.2.1
  have hH : ContDiff ℝ ∞ H := contDiff_positiveReferenceHeight hδ
    (fun _ _ => (hhs false).contDiffAt) (fun _ _ => (hhs true).contDiffAt)
    (hHpos false) (hHpos true)
  have hysv (side : Bool) : ys side (if side then r else l) = (if side then 1 else 0) :=
    (radialEndpointTaylorSlice_value (y side) (n + 1) _).trans (hyvalue side)
  refine ⟨positiveReferenceCylinder_rangeGeometry hY hYpos hbij hinv hH
    (positiveReferenceHeight_pos l r δ (hs false) (hs true))
    (positiveReferenceCoordinate_left l r δ (deriv (ys false)) (deriv (ys true)))
    (positiveReferenceCoordinate_right hδ hgap (fun x _ => hds false x)
      (fun x _ => hds true x)), ?_, ?_, hder, ?_⟩
  · intro side θ k hk
    have hg := positiveReferenceCoordinate_endpoint_germ hδ hgap
      (fun _ _ => (hys false).contDiffAt) (fun _ _ => (hys true).contDiffAt)
      (hysv false) (hysv true) side
    have he : Y =ᶠ[𝓝 (if side then r else l)] ys side := by
      cases side <;> exact hg
    have hlift := he.comp_tendsto (continuous_fst.tendsto (if side then r else l, θ))
    exact (hlift.iteratedFDeriv ℝ k).eq_of_nhds.trans
      (radialEndpointTaylorSlice_fullJets (hab side) (hc side) (hy side) (hyc side)
        (hyr side) (n + 1) hk θ)
  · intro side θ k hk
    have hg := positiveReferenceHeight_endpoint_germ hδ hgap (hHpos false) (hHpos true) side
    have he : H =ᶠ[𝓝 (if side then r else l)] hs side := by
      cases side <;> exact hg
    have hlift := he.comp_tendsto (continuous_fst.tendsto (if side then r else l, θ))
    exact (hlift.iteratedFDeriv ℝ k).eq_of_nhds.trans
      (radialEndpointTaylorSlice_fullJets (hab side) (hc side) (hh side) (hhc side)
        (hhr side) (n + 1) hk θ)
  · intro x
    apply positiveReferenceHeight_value_bounds hδ (le_max_left _ _) hHpos
    · intro side t ht
      exact (le_abs_self _).trans ((hcollar side t ht).2.2.2.trans
        ((le_max_left _ _).trans (le_max_right _ _)))
    · intro side t ht
      have hi : (hs side t)⁻¹ ≤ 2 / κ := by
        simpa only [one_div, inv_div] using
          one_div_le_one_div_of_le (half_pos hκ) (hcollar side t ht).2.2.1
      exact hi.trans ((le_max_right _ _).trans (le_max_right _ _))

end ContinuousFlexibility.Analysis
