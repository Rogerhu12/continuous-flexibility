module

public import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer
public import ContinuousFlexibility.Analysis.PositiveChartRangeGeometry

/-!
# Arbitrarily small right collars in a qualitative normalization buffer

The normalization-buffer contract imposes strict ordering, but no quantitative
lower bound on the gap between its right center and the right endpoint. This
file records that freedom in the actual canonical coordinate. The normalization
interval and its support certificate remain unchanged.

These are consequences of the existing definitions, not new assumptions on a
positive-geometry realization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- The scalar coordinate underlying a cylindrical range certificate is smooth. -/
theorem n04PositiveGeometry_reference_coordinate_smooth
    {Y H : ℝ → ℝ} {l r : ℝ}
    (h : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1) :
    ContDiff ℝ ∞ Y := by
  have hslice : ContDiff ℝ ∞ (fun x : ℝ => (x, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  exact h.chart_smooth.fst.comp hslice

/-- The right endpoint has canonical coordinate one, as follows from the two
closed range conditions and the genuine inverse. -/
theorem n04PositiveGeometry_reference_coordinate_right
    {Y H : ℝ → ℝ} {l r : ℝ} (hlr : l < r)
    (h : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1) :
    Y r = 1 := by
  have hY := n04PositiveGeometry_reference_coordinate_smooth h
  have hpos (x : ℝ) : 0 < deriv Y x := by
    have hp := h.jacobian_positive (x, 0)
    rw [planeJacobian_positiveReferenceCylinderChart
      (hY.differentiable (by simp) x)] at hp
    exact hp
  have hm : StrictMono Y := strictMono_of_deriv_pos hpos
  have hu : Y r ≤ 1 :=
    (h.maps_closed (show (r, (0 : ℝ)) ∈ Icc l r ×ˢ (univ : Set ℝ) from
      ⟨⟨hlr.le, le_rfl⟩, mem_univ _⟩)).1.2
  have hi : Function.invFun Y 1 ≤ r :=
    (h.inverse_maps_closed (show ((1 : ℝ), (0 : ℝ)) ∈
      Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) from
      ⟨⟨zero_le_one, le_rfl⟩, mem_univ _⟩)).1.2
  have he : Y (Function.invFun Y 1) = 1 :=
    congrArg Prod.fst (h.right_inverse (1, 0))
  have hl : 1 ≤ Y r := by
    rw [← he]
    exact hm.monotone hi
  exact le_antisymm hu hl

/-- Continuity at an endpoint allows the right center to approach it by any
prescribed positive amount in canonical coordinates. -/
theorem n04PositiveGeometry_exists_right_collar_point
    {Y : ℝ → ℝ} {c r δ : ℝ} (hcr : c < r)
    (hY : ContinuousAt Y r) (hYr : Y r = 1) (hδ : 0 < δ)
    (hbelow : ∀ x, c < x → x < r → Y x < 1) :
    ∃ d : ℝ, c < d ∧ d < r ∧ 0 < 1 - Y d ∧ 1 - Y d < δ := by
  obtain ⟨ε, hε, hclose⟩ := Metric.continuousAt_iff.mp hY δ hδ
  let t : ℝ := min (r - c) ε / 2
  have ht : 0 < t := half_pos (lt_min (sub_pos.mpr hcr) hε)
  have htr : t < r - c := by
    have hm := min_le_left (r - c) ε
    dsimp only [t]
    linarith
  have hte : t < ε := by
    have hm := min_le_right (r - c) ε
    dsimp only [t]
    linarith
  let d : ℝ := r - t
  have hcd : c < d := by dsimp only [d]; linarith
  have hdr : d < r := by dsimp only [d]; linarith
  have hd : dist d r < ε := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hdr)]
    dsimp only [d]
    linarith
  have hy := hclose hd
  rw [Real.dist_eq, hYr] at hy
  refine ⟨d, hcd, hdr, sub_pos.mpr (hbelow d hcd hdr), ?_⟩
  have hl := (abs_lt.mp hy).1
  linarith

/-- Every positive function of the component can be an upper bound on the
right canonical collar width of another valid buffer. The support-bearing
normalization intervals and the left centers are exactly the old ones. -/
theorem n04PositiveGeometry_buffer_arbitrarily_small_right_canonical_gap
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B₀ : N04PositiveNormalizationBuffer a b f K)
    (Y H : N04PositiveComponent a b f → ℝ → ℝ)
    (hgeometry : ∀ i, PositiveChartRangeGeometry
      (positiveReferenceCylinderChart (Y i)) (positiveReferenceCylinderInverse (Y i))
      (fun p : PolarPoint => H i p.1) (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (δ : N04PositiveComponent a b f → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ B : N04PositiveNormalizationBuffer a b f K,
      B.centerLeft = B₀.centerLeft ∧
      B.normalizationLeft = B₀.normalizationLeft ∧
      B.normalizationRight = B₀.normalizationRight ∧
      ∀ i, B₀.centerRight i < B.centerRight i ∧
        0 < 1 - Y i (B.centerRight i) ∧ 1 - Y i (B.centerRight i) < δ i := by
  have hex (i : N04PositiveComponent a b f) :
      ∃ d : ℝ, B₀.centerRight i < d ∧ d < n04PositiveRight i ∧
        0 < 1 - Y i d ∧ 1 - Y i d < δ i := by
    have ho := B₀.ordered i
    have hlc : n04PositiveLeft i < B₀.centerRight i :=
      ((ho.1.trans ho.2.1).trans ho.2.2.1).trans ho.2.2.2.1
    have hcr : B₀.centerRight i < n04PositiveRight i := ho.2.2.2.2
    apply n04PositiveGeometry_exists_right_collar_point hcr
      (n04PositiveGeometry_reference_coordinate_smooth (hgeometry i)).continuous.continuousAt
      (n04PositiveGeometry_reference_coordinate_right (hlc.trans hcr) (hgeometry i)) (hδ i)
    intro x hcx hxr
    exact ((hgeometry i).maps_open
      (show (x, (0 : ℝ)) ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ
        (univ : Set ℝ) from ⟨⟨hlc.trans hcx, hxr⟩, mem_univ _⟩)).1.2
  choose d hd using hex
  let B : N04PositiveNormalizationBuffer a b f K := {
    centerLeft := B₀.centerLeft
    normalizationLeft := B₀.normalizationLeft
    normalizationRight := B₀.normalizationRight
    centerRight := d
    ordered := fun i => ⟨(B₀.ordered i).1, (B₀.ordered i).2.1,
      (B₀.ordered i).2.2.1, (B₀.ordered i).2.2.2.1.trans (hd i).1,
      (hd i).2.1⟩
    support := B₀.support }
  exact ⟨B, rfl, rfl, rfl, fun i => ⟨(hd i).1, (hd i).2.2.1, (hd i).2.2.2⟩⟩

end ContinuousFlexibility.Analysis
