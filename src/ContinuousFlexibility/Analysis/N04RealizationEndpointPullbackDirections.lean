module

public import ContinuousFlexibility.Analysis.N04RealizationEndpointFiberDirections
public import ContinuousFlexibility.Analysis.N04RealizationAngularFiberDirections
public import ContinuousFlexibility.Analysis.EndpointFiberPullbackAssembly

/-!
# Joint regularity of the actual fiber pullback coordinate and chart

The existing fixed widths are retained. Actual mixed differentiation
of the pulled-back fields supplies precisely the boundary data used
by the radial interpolation. The final chart is its original forward
fiber-angle formula, not a newly chosen inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {U : Set E}

def n04Realization_endpointFiberPullback_jointDirections
    (hU : IsOpen U) (hc : Convex ℝ U) (n : ℕ)
    {l r c d κ Mσ : ℝ} (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hMσ : 0 ≤ Mσ)
    (φ : E → PolarPoint → ℝ) (X : E → Bool → PolarPoint → ℝ)
    (Jinv : SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => parameterizedCircleInverse (φ p.1) p.2))
    (JX : ∀ side, SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => X p.1 side p.2)) :
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint =>
      endpointFiberPullbackCoordinate n (φ p.1) (X p.1) l r c d κ Mσ p.2) := by
  let F : Bool → E → PolarPoint → ℝ := fun side x =>
    angularFiberPullback (φ x) (X x side)
  let JF : ∀ side, SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => F side p.1 p.2) :=
    fun side => n04Realization_angularFiberPullback_jointDirections hU
      φ (fun x => X x side) Jinv (JX side)
  let A : E → Bool → ℕ → ℝ → ℝ := fun x side =>
    radialBoundaryJet (F side x) (if side then r else l)
  have hA (x : E) (hx : x ∈ U) (side : Bool) (j : ℕ) (_hj : j ≤ n + 1) :
      ContDiff ℝ ∞ (A x side j) :=
    contDiff_radialBoundaryJet
      (contDiffOn_univ.mp ((JF side).spatial_value_contDiffOn isOpen_univ x hx))
      (if side then r else l) j
  let JA : ∀ side (j : Fin (n + 2)), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => A p.1 side j p.2) := fun side j =>
    n04Realization_radialBoundaryJointDirections hU hc (F side) (JF side)
      (if side then r else l) j
  let a : Bool → ℝ := fun side => if side then d else l
  let b : Bool → ℝ := fun side => if side then r else c
  have hab (side : Bool) : a side < b side := by cases side <;> assumption
  have hmarg (side : Bool) := prescribedEndpointWidth_margins n
    (sub_pos.mpr (hab side)) zero_lt_one hκ hMσ
    (zero_le_one.trans (le_max_right (Mσ + ((n + 1 : ℕ) : ℝ) * Mσ) 1))
    (sub_pos.mpr (hab side))
  exact n04Realization_endpointFiberInterpolation_jointDirections hU n l r c d hcd
    (endpointFiberWidths n l r c d κ Mσ)
    (fun side => (hmarg side).1) (fun side => (hmarg side).2.2.2.1) A hA JA

/-- The final planar transport uses the same angular and radial fields. -/
def n04Realization_positiveFiberChart_jointDirections
    (hU : IsOpen U) (φ Y : E → PolarPoint → ℝ)
    (Jφ : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => φ p.1 p.2))
    (JY : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => Y p.1 p.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => positiveFiberChart (φ p.1) (Y p.1) p.2) := by
  have hdomain : IsOpen (U ×ˢ (univ : Set PolarPoint)) := hU.prod isOpen_univ
  let P : (E × PolarPoint) →L[ℝ] E := ContinuousLinearMap.fst ℝ E PolarPoint
  let R : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let JP : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => p.1) :=
    (smoothDirectionsLinearOn P hdomain).congrOn (fun _ _ => by
      simp only [P, ContinuousLinearMap.coe_fst'])
  let JR : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => p.2.1) :=
    (smoothDirectionsLinearOn R hdomain).congrOn (fun _ _ => by
      simp only [R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd'])
  let G := smoothDirectionsUniformProd JP (smoothDirectionsUniformProd JR Jφ)
  let K := smoothDirections_realCompTVS G JY (fun p hp => ⟨hp.1, mem_univ _⟩)
  exact (smoothDirectionsUniformProd K Jφ).congrOn (fun _ _ => rfl)

end ContinuousFlexibility.Analysis
