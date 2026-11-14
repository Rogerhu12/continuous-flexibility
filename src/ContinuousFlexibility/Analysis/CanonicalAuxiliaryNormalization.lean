module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Sources supported in the actual normalization region

The two actual inverse charts agree whenever either inverse image is in
the normalization region.  Equality of the chart germs there also gives
equality of their real Jacobians.  A source supported in that region
therefore has exactly the same canonical transform in every state.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

private theorem canonical_normalized_inverse_data
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ} (hA : CanonicalGeometry D S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m)
    (hN : (K.inverseChart z m p).1 ∈ K.normalizationRegion ∨
      (K.inverseChart (C.referenceState, 0) m p).1 ∈ K.normalizationRegion) :
    K.inverseChart z m p = K.inverseChart (C.referenceState, 0) m p ∧
      K.height z m (K.inverseChart z m p) =
        K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) ∧
      planeJacobian (K.chart z m) (K.inverseChart z m p) =
        planeJacobian (K.chart (C.referenceState, 0) m)
          (K.inverseChart (C.referenceState, 0) m p) := by
  let x : PolarPoint := K.inverseChart z m p
  let y : PolarPoint := K.inverseChart (C.referenceState, 0) m p
  have hcz := hA.charts z hz hs m
  have hc₀ := hA.charts (C.referenceState, 0) hz₀ hs₀ m
  have hx : x ∈ physicalPieceOpen S K z m := hcz.2.1 hp
  have hy : y ∈ physicalPieceOpen S K (C.referenceState, 0) m := hc₀.2.1 hp
  have hnorm := hA.normalization z hz hs m
  have hxy : x = y := by
    rcases hN with hxN | hyN
    · have hx₀ : x ∈ physicalPieceOpen S K (C.referenceState, 0) m ∩
          (K.normalizationRegion ×ˢ (univ : Set ℝ)) := by
        rw [← hnorm.1]
        exact ⟨hx, hxN, mem_univ _⟩
      have hFx : K.chart (C.referenceState, 0) m x = p :=
        (hnorm.2 x hx hxN).1.symm.trans (hcz.2.2.2.1 p hp)
      exact (hc₀.2.2.1 x hx₀.1).symm.trans
        (congrArg (K.inverseChart (C.referenceState, 0) m) hFx)
    · have hyz : y ∈ physicalPieceOpen S K z m ∩
          (K.normalizationRegion ×ˢ (univ : Set ℝ)) := by
        rw [hnorm.1]
        exact ⟨hy, hyN, mem_univ _⟩
      have hFy : K.chart z m y = p :=
        (hnorm.2 y hyz.1 hyN).1.trans (hc₀.2.2.2.1 p hp)
      exact (congrArg (K.inverseChart z m) hFy).symm.trans (hcz.2.2.1 y hyz.1)
  have hxN : x.1 ∈ K.normalizationRegion := by
    rcases hN with hxN | hyN
    · exact hxN
    · rw [hxy]
      exact hyN
  have hopen : IsOpen (physicalPieceOpen S K z m ∩
      (K.normalizationRegion ×ˢ (univ : Set ℝ))) :=
    (hA.domains z hz hs m).1.inter (hA.normalizationOpen.prod isOpen_univ)
  have hchart : K.chart z m =ᶠ[𝓝 x] K.chart (C.referenceState, 0) m := by
    filter_upwards [hopen.mem_nhds ⟨hx, hxN, mem_univ _⟩] with q hq
    exact (hnorm.2 q hq.1 hq.2.1).1
  have hd := hchart.fderiv_eq (𝕜 := ℝ)
  have hJ : planeJacobian (K.chart z m) x =
      planeJacobian (K.chart (C.referenceState, 0) m) y := by
    calc
      _ = planeJacobian (K.chart (C.referenceState, 0) m) x := by
        simp only [planeJacobian, hd]
      _ = _ := congrArg (planeJacobian (K.chart (C.referenceState, 0) m)) hxy
  exact ⟨hxy, (hnorm.2 x hx hxN).2.trans
    (congrArg (K.height (C.referenceState, 0) m) hxy), hJ⟩

/-- Support in the genuine normalization region freezes the actual source
transform, including its inverse point, height, and Jacobian denominator. -/
theorem canonicalSource_eqOn_reference_of_normalization
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ} (hA : CanonicalGeometry D S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (f : PolarPoint → ℝ)
    (hsupport : ∀ p, f p ≠ 0 → p.1 ∈ K.normalizationRegion) :
    EqOn (canonicalSource S K z m f)
      (canonicalSource S K (C.referenceState, 0) m f) (canonicalOpen S K m) := by
  intro p hp
  by_cases hx : f (K.inverseChart z m p) = 0
  · by_cases hy : f (K.inverseChart (C.referenceState, 0) m p) = 0
    · simp only [canonicalSource, hx, hy, mul_zero, zero_div]
    · obtain ⟨he, _, _⟩ := canonical_normalized_inverse_data hA hz₀ hs₀ hz hs m hp
        (Or.inr (hsupport _ hy))
      exact False.elim (hy (by rw [← he]; exact hx))
  · obtain ⟨he, hh, hJ⟩ := canonical_normalized_inverse_data hA hz₀ hs₀ hz hs m hp
      (Or.inl (hsupport _ hx))
    dsimp only [canonicalSource]
    rw [hh, hJ, he]

end ContinuousFlexibility.Analysis
