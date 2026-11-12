import ContinuousFlexibility.Analysis.N06RelativeChartHeightPatch
import ContinuousFlexibility.Blueprint.CanonicalParts

/-!
# Relative patches of the actual N04 coordinate witness

The explicit fields below use the original reference chart and the true
current chart of the same indexed physical piece. The boundary derivatives
are extracted from the existing closed-piece N04 clause. No freely assigned
jet data or global extension is assumed.

For a piece whose endpoints are true turning radii, one radius is selected
before the state so that the correction avoids the entire closed support
of chi. The current and reference fields then have exactly the same germ
there. The reference chart is retained everywhere, and the reference height
is retained throughout the original closed physical piece.

These are constructed chart and height fields. Jacobian nondegeneracy,
the global inverse, and the remaining N04 operator conditions are separate
obligations; this module does not assert them.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

def n06RelativeCanonicalChart {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S) (δ : ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) : PolarPoint → PolarPoint :=
  n06RelativeChartPatch (K.physicalLeft m) (K.physicalRight m) δ
    (K.chart (C.referenceState, 0) m) (fun _ => K.chart z m)

def n06RelativeCanonicalLogHeight {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S) (δ : ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) : PolarPoint → ℝ :=
  n06RelativeLogHeightPatch (K.physicalLeft m) (K.physicalRight m) δ
    (K.height (C.referenceState, 0) m) (fun _ => K.height z m)

def n06RelativeCanonicalHeight {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S) (δ : ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) : PolarPoint → ℝ :=
  n06RelativeHeightPatch (K.physicalLeft m) (K.physicalRight m) δ
    (K.height (C.referenceState, 0) m) (fun _ => K.height z m)

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

private theorem n06_actualCanonical_boundary_data
    (hA : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    (side : Bool) (θ : ℝ) :
    ContDiffAt ℝ ∞ (K.chart z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) ∧
      ContDiffAt ℝ ∞ (K.height z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) ∧
      0 < K.height z m (if side then K.physicalRight m else K.physicalLeft m, θ) := by
  have hle := (hA.2.2.2.1 m).1.le
  have hp : (if side then K.physicalRight m else K.physicalLeft m) ∈
      Icc (K.physicalLeft m) (K.physicalRight m) := by
    cases side
    · exact ⟨le_rfl, hle⟩
    · exact ⟨hle, le_rfl⟩
  have h := hA.2.2.2.2.2.2.2.2.1 z hz hs m
    (if side then K.physicalRight m else K.physicalLeft m, θ) hp
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- The new fields are smooth on the original closed physical piece and
the constructed height is strictly positive. -/
theorem n06_relativeCanonicalPatch_closed
    (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (δ : ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    ContDiffAt ℝ ∞ (n06RelativeCanonicalChart C K δ z m) p ∧
      ContDiffAt ℝ ∞ (n06RelativeCanonicalHeight C K δ z m) p ∧
      0 < n06RelativeCanonicalHeight C K δ z m p := by
  have h₀ := n06_actualCanonical_boundary_data hA href hsref m
  have hc := n06_actualCanonical_boundary_data hA hz hs m
  have hp₀ := hA.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hsref m p hp
  refine ⟨?_, ?_, n06RelativeHeightPatch_pos _ _ _ _ _ p⟩
  · exact n06RelativeChartPatch_contDiffAt (fun side θ => (h₀ side θ).1)
      (fun side θ => (hc side θ).1) hp₀.1
  · exact n06RelativeHeightPatch_contDiffAt
      (fun side θ => (h₀ side θ).2.1) (fun side θ => (hc side θ).2.1)
      (fun side θ => (h₀ side θ).2.2) (fun side θ => (hc side θ).2.2)
      hp₀.2.1 hp₀.2.2.2

/-- The four actual radial jets of both current chart entries are kept. -/
theorem n06_relativeCanonicalChart_boundary_jets
    (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ)
    (hgap : 2 * δ ≤ K.physicalRight m - K.physicalLeft m)
    (side : Bool) {j : ℕ} (hj : j ≤ 4) (θ : ℝ) :
    radialBoundaryJet (fun p => (n06RelativeCanonicalChart C K δ z m p).1)
        (if side then K.physicalRight m else K.physicalLeft m) j θ =
      radialBoundaryJet (fun p => (K.chart z m p).1)
        (if side then K.physicalRight m else K.physicalLeft m) j θ ∧
    radialBoundaryJet (fun p => (n06RelativeCanonicalChart C K δ z m p).2)
        (if side then K.physicalRight m else K.physicalLeft m) j θ =
      radialBoundaryJet (fun p => (K.chart z m p).2)
        (if side then K.physicalRight m else K.physicalLeft m) j θ :=
  n06RelativeChartPatch_boundary_jets hδ hgap
    (fun side θ => (n06_actualCanonical_boundary_data hA href hsref m side θ).1)
    (fun side θ => (n06_actualCanonical_boundary_data hA hz hs m side θ).1) side hj θ

/-- The three actual radial jets of the logarithm of the constructed
height coincide with the original current logarithmic-height jets. -/
theorem n06_relativeCanonicalHeight_log_boundary_jets
    (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ)
    (hgap : 2 * δ ≤ K.physicalRight m - K.physicalLeft m)
    (side : Bool) {j : ℕ} (hj : j ≤ 3) (θ : ℝ) :
    radialBoundaryJet (fun p => Real.log (n06RelativeCanonicalHeight C K δ z m p))
        (if side then K.physicalRight m else K.physicalLeft m) j θ =
      radialBoundaryJet (fun p => Real.log (K.height z m p))
        (if side then K.physicalRight m else K.physicalLeft m) j θ := by
  have h₀ := n06_actualCanonical_boundary_data hA href hsref m
  have hc := n06_actualCanonical_boundary_data hA hz hs m
  have he := n06RelativeLogHeightPatch_boundary_jets hδ hgap
    (fun side θ => (h₀ side θ).2.1) (fun side θ => (hc side θ).2.1)
    (fun side θ => (h₀ side θ).2.2) (fun side θ => (hc side θ).2.2) side hj θ
  simpa only [n06RelativeCanonicalHeight, n06RelativeHeightPatch, Real.log_exp] using he

/-- The original reference chart is retained on the whole plane. -/
theorem n06_relativeCanonicalChart_reference (δ : ℝ) (m : ℕ) :
    n06RelativeCanonicalChart C K δ (C.referenceState, 0) m =
      K.chart (C.referenceState, 0) m :=
  n06RelativeChartPatch_self _ _ _ _

/-- The reference height is retained throughout the old closed physical
piece, where its positivity is part of the original N04 contract. -/
theorem n06_relativeCanonicalHeight_reference
    (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState) (δ : ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    n06RelativeCanonicalHeight C K δ (C.referenceState, 0) m p =
      K.height (C.referenceState, 0) m p :=
  n06RelativeHeightPatch_self
    (hA.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hsref m p hp).2.2.2

/-- A true turning radius cannot lie in the closed support of chi. -/
theorem n06_turningRadius_notMem_tsupport_chi (hD : RadialTrueBorder D)
    {r : ℝ} (hr : deriv D.w r = 0) : r ∉ tsupport D.chi := by
  intro h
  have hpos := (hD.2.2.1 h).2
  rw [hr] at hpos
  exact lt_irrefl 0 hpos

/-- One actual collar radius works for every state. On the entire closed
support of chi, the constructed chart and height retain the complete
reference germ. The endpoint-root hypotheses identify the genuine
turning-boundary pieces; they are not inferred for arbitrary subdivisions. -/
theorem n06_exists_relativeCanonicalPatch_avoiding_chi
    (hD : RadialTrueBorder D) (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState) (m : ℕ)
    (hrootL : deriv D.w (K.physicalLeft m) = 0)
    (hrootR : deriv D.w (K.physicalRight m) = 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ρ ∧
      2 * δ < K.physicalRight m - K.physicalLeft m ∧
      ∀ (z : AnnularState S × ℝ) (p : PolarPoint),
        p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) →
        p.1 ∈ tsupport D.chi →
        n06RelativeCanonicalChart C K δ z m =ᶠ[𝓝 p] K.chart (C.referenceState, 0) m ∧
        n06RelativeCanonicalHeight C K δ z m =ᶠ[𝓝 p] K.height (C.referenceState, 0) m := by
  obtain ⟨δ, hδ, hδρ, hgap, hL, hR⟩ := exists_positiveEndpoint_collars_avoiding
    (isClosed_tsupport D.chi) (n06_turningRadius_notMem_tsupport_chi hD hrootL)
    (n06_turningRadius_notMem_tsupport_chi hD hrootR) (hA.2.2.2.1 m).1 hρ
  refine ⟨δ, hδ, hδρ, hgap, ?_⟩
  intro z p hp hpχ
  have hp₀ := hA.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hsref m p hp
  exact ⟨n06RelativeChartPatch_fixed_germ hδ _ _ hL hR hpχ,
    n06RelativeHeightPatch_fixed_germ hδ _ _ hL hR hpχ hp₀.2.1.continuousAt hp₀.2.2.2⟩

end ContinuousFlexibility.Statements
