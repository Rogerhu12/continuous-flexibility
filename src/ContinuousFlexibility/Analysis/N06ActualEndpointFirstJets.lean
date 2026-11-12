import ContinuousFlexibility.Analysis.N06FiniteBoundaryMatching
import ContinuousFlexibility.Analysis.N06CanonicalBoundaryValue

/-!
# First jets at the actual non-artificial endpoints

The original N04 closed-domain geometry already determines the location
and ordinary first jets of each genuine endpoint circle. The reference
endpoint labels are used only to name these true circles. Artificial
moving cuts are excluded explicitly.

For each piece the two true circles, when both are present, map to
different canonical endpoints. This determines one reversal flag for
that piece. The genuine closed inverse then maps the corresponding
canonical half-period circle to the actual physical endpoint radius.

These conclusions concern each piece separately. They do not assert
that independently chosen neighboring charts share the same angular
label, height, or radial scale.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

/-- An actual constant radial boundary value gives the full first-jet
record, with every boundary function taken from the chart and height
themselves. -/
theorem n06_firstJets_of_actual_boundary
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {r y : ℝ}
    (hF : ∀ θ, DifferentiableAt ℝ F (r, θ))
    (hh : ∀ θ, DifferentiableAt ℝ h (r, θ))
    (hy : ∀ θ, (F (r, θ)).1 = y) :
    N06RootFirstJets F h r y 1
      (fun θ => (F (r, θ)).2) (fun θ => h (r, θ))
      (fun θ => (fderiv ℝ F (r, θ) (1, 0)).1)
      (fun θ => (fderiv ℝ F (r, θ) (1, 0)).2)
      (fun θ => radialPartial h (r, θ)) := by
  refine ⟨hF, hh, ?_, fun _ => rfl, ?_, fun _ => rfl⟩
  · intro θ
    exact Prod.ext (hy θ) rfl
  · intro θ
    apply Prod.ext
    · simp only [one_mul]
    · rfl

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The whole true endpoint circle lies on the actual frontier. The
strict one-sided domain property rules out membership in the open piece. -/
theorem n06_trueEndpoint_frontier
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (side : Bool) (htrue : ¬n06ArtificialCutSide K m side) (θ : ℝ) :
    (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side, θ) ∈
      frontier (physicalPieceOpen S K z m) := by
  obtain ⟨hx, hside⟩ := n06_trueEndpoint_current_geometry hC h04 hz hs m side htrue
  rw [(h04.1.domains z hz hs m).1.frontier_eq]
  refine ⟨hx θ, ?_⟩
  intro hp
  have hlt := hside _ hp
  cases side
  · exact (lt_irrefl (K.physicalLeft m)) hlt
  · exact (lt_irrefl (K.physicalRight m)) hlt

/-- Each true physical endpoint maps to one canonical endpoint, with a
single choice valid for all angles. -/
theorem n06_trueEndpoint_radial_choice
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (side : Bool) (htrue : ¬n06ArtificialCutSide K m side) :
    ∃ upper : Bool, ∀ θ,
      (K.chart z m
        (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side, θ)).1 =
          n06Endpoint (K.left m) (K.right m) upper := by
  rcases n06_canonicalBoundary_radial_dichotomy h04.1 hz hs m
      (n06_trueEndpoint_frontier hC h04 hz hs m side htrue) with hl | hr
  · exact ⟨false, hl⟩
  · exact ⟨true, hr⟩

/-- The actual closed inverse prevents the two physical endpoint
circles from mapping to the same canonical endpoint. Reflection fixes
the angular seam at zero on both circles. -/
private theorem n06_trueEndpoint_radial_choices_ne
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ)
    (hleft : ¬n06ArtificialCutSide K m false)
    (hright : ¬n06ArtificialCutSide K m true)
    {ul ur : Bool}
    (hl : ∀ θ, (K.chart z m (K.physicalLeft m, θ)).1 =
      n06Endpoint (K.left m) (K.right m) ul)
    (hr : ∀ θ, (K.chart z m (K.physicalRight m, θ)).1 =
      n06Endpoint (K.left m) (K.right m) ur) : ul ≠ ur := by
  intro he
  have hxL := (n06_trueEndpoint_current_geometry hC h04 hz hs m false hleft).1
  have hxR := (n06_trueEndpoint_current_geometry hC h04 hz hs m true hright).1
  have hangleL := (n06_canonicalChart_closed_angle_seams h04 hz hs m hxL).1
  have hangleR := (n06_canonicalChart_closed_angle_seams h04 hz hs m hxR).1
  have hchart : K.chart z m (K.physicalLeft m, 0) =
      K.chart z m (K.physicalRight m, 0) := by
    apply Prod.ext
    · rw [hl 0, hr 0, he]
    · exact hangleL.trans hangleR.symm
  have hinverse := congrArg (K.inverseChart z m) hchart
  rw [(h04.1.boundary z hz hs m).2.2.1 _ (hxL 0),
    (h04.1.boundary z hz hs m).2.2.1 _ (hxR 0)] at hinverse
  exact (h04.1.referenceBounds m).1.ne (congrArg Prod.fst hinverse)

/-- One reversal flag simultaneously describes every true endpoint of
a piece. No choice is made at an artificial cut. -/
theorem n06_exists_trueEndpoint_orientation
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) :
    ∃ reverse : Bool, ∀ side : Bool, ¬n06ArtificialCutSide K m side → ∀ θ,
      (K.chart z m
        (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side, θ)).1 =
          n06Endpoint (K.left m) (K.right m) (if reverse then !side else side) := by
  classical
  by_cases hL : ¬n06ArtificialCutSide K m false
  · obtain ⟨ul, hl⟩ := n06_trueEndpoint_radial_choice hC h04 hz hs m false hL
    by_cases hR : ¬n06ArtificialCutSide K m true
    · obtain ⟨ur, hr⟩ := n06_trueEndpoint_radial_choice hC h04 hz hs m true hR
      have hne := n06_trueEndpoint_radial_choices_ne hC h04 hz hs m hL hR hl hr
      have he : ur = !ul := by
        cases ul <;> cases ur <;> simp_all
      refine ⟨ul, ?_⟩
      intro side _ θ
      cases side
      · cases ul <;> simpa only [n06Endpoint, Bool.false_eq_true, if_false,
          if_true, Bool.not_false] using hl θ
      · cases ul <;> simpa only [he, n06Endpoint, Bool.false_eq_true, if_false,
          if_true, Bool.not_true, Bool.not_false] using hr θ
    · refine ⟨ul, ?_⟩
      intro side htrue θ
      cases side
      · cases ul <;> simpa only [n06Endpoint, Bool.false_eq_true, if_false,
          if_true, Bool.not_false] using hl θ
      · exact (hR htrue).elim
  · by_cases hR : ¬n06ArtificialCutSide K m true
    · obtain ⟨ur, hr⟩ := n06_trueEndpoint_radial_choice hC h04 hz hs m true hR
      refine ⟨!ur, ?_⟩
      intro side htrue θ
      cases side
      · exact (hL htrue).elim
      · cases ur <;> simpa only [n06Endpoint, Bool.false_eq_true, if_false,
          if_true, Bool.not_true, Bool.not_false] using hr θ
    · refine ⟨false, ?_⟩
      intro side htrue θ
      cases side
      · exact (hL htrue).elim
      · exact (hR htrue).elim

/-- Closed regularity produces an actual first-jet record at any true
endpoint whose canonical radial value has been identified. -/
theorem n06_trueEndpoint_firstJets
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (side : Bool) (htrue : ¬n06ArtificialCutSide K m side) {y : ℝ}
    (hy : ∀ θ, (K.chart z m
      (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side, θ)).1 = y) :
    ∃ β H ρ κ Hr : ℝ → ℝ,
      N06RootFirstJets (K.chart z m) (K.height z m)
        (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side) y 1 β H ρ κ Hr := by
  let r := n06Endpoint (K.physicalLeft m) (K.physicalRight m) side
  have hx := (n06_trueEndpoint_current_geometry hC h04 hz hs m side htrue).1
  have hb := (h04.1.boundary z hz hs m).2.2.2.2.1
  refine ⟨(fun θ => (K.chart z m (r, θ)).2), (fun θ => K.height z m (r, θ)),
    (fun θ => (fderiv ℝ (K.chart z m) (r, θ) (1, 0)).1),
    (fun θ => (fderiv ℝ (K.chart z m) (r, θ) (1, 0)).2),
    (fun θ => radialPartial (K.height z m) (r, θ)), ?_⟩
  exact n06_firstJets_of_actual_boundary
    (fun θ => (hb (r, θ) (hx θ)).1.differentiableAt (by simp))
    (fun θ => (hb (r, θ) (hx θ)).2.1.differentiableAt (by simp)) hy

/-- The genuine closed inverse maps the full corresponding half-period
back to the true physical endpoint radius. -/
theorem n06_trueEndpoint_inverseCircle
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (side : Bool) (htrue : ¬n06ArtificialCutSide K m side) {y : ℝ}
    (hy : ∀ θ, (K.chart z m
      (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side, θ)).1 = y)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    (K.inverseChart z m (y, θ)).1 =
      n06Endpoint (K.physicalLeft m) (K.physicalRight m) side := by
  obtain ⟨β, H, ρ, κ, Hr, J⟩ := n06_trueEndpoint_firstJets hC h04 hz hs m side htrue hy
  have hx := (n06_trueEndpoint_current_geometry hC h04 hz hs m side htrue).1
  obtain ⟨η, hη, hβ⟩ := (n06_current_boundary_angular_surjOn J h04 hz hs hx).2.2 hθ
  have he := (h04.1.boundary z hz hs m).2.2.1 _ (hx η)
  rw [J.chart_value η, hβ] at he
  exact congrArg Prod.fst he

/-- The original N01 geometry and N04 properties supply all single-piece
endpoint records and inverse circles, with one actual orientation per
piece. Shared data across neighboring pieces are a separate assertion. -/
theorem n06_exists_actualEndpoint_firstJets
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) :
    ∃ reverse : ℕ → Bool,
      (∀ m, ∀ side : Bool, ¬n06ArtificialCutSide K m side →
        ∃ σ : ℝ, ∃ β H ρ κ Hr : ℝ → ℝ,
          Nonempty (N06RootFirstJets (K.chart z m) (K.height z m)
            (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side)
            (n06Endpoint (K.left m) (K.right m) (if reverse m then !side else side))
              σ β H ρ κ Hr)) ∧
      ∀ m, ∀ side : Bool, ¬n06ArtificialCutSide K m side →
        ∀ θ ∈ Icc (0 : ℝ) Real.pi,
          (K.inverseChart z m
            (n06Endpoint (K.left m) (K.right m) (if reverse m then !side else side), θ)).1 =
              n06Endpoint (K.physicalLeft m) (K.physicalRight m) side := by
  classical
  have hC : controlGeometryConditions D S C := h01.2.2.2.1
  choose reverse hreverse using n06_exists_trueEndpoint_orientation hC h04 hz hs
  refine ⟨reverse, ?_, ?_⟩
  · intro m side htrue
    obtain ⟨β, H, ρ, κ, Hr, J⟩ :=
      n06_trueEndpoint_firstJets hC h04 hz hs m side htrue (hreverse m side htrue)
    exact ⟨1, β, H, ρ, κ, Hr, ⟨J⟩⟩
  · intro m side htrue θ hθ
    exact n06_trueEndpoint_inverseCircle hC h04 hz hs m side htrue
      (hreverse m side htrue) hθ

end ContinuousFlexibility.Statements
