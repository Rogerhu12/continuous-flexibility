import ContinuousFlexibility.Analysis.N06RootGreenDensity
import ContinuousFlexibility.Analysis.N06CurrentChartChange
import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual angular image of a closed piece boundary

The genuine closed chart symmetries fix the angular seams at every
physical circle contained in the actual closed domain.
Thus any actual boundary map appearing in the first-jet record takes
0 to 0 and pi to pi, and its image covers the entire half-period by the
intermediate value theorem. No boundary inverse or assumed monotonicity
is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The two angular seams retain their actual values on any physical
circle belonging to the actual closed domain. -/
theorem n06_canonicalChart_closed_angle_seams
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {r : ℝ}
    (hx : ∀ θ : ℝ, (r, θ) ∈ physicalPieceClosed S K z m) :
    (K.chart z m (r, 0)).2 = 0 ∧ (K.chart z m (r, Real.pi)).2 = Real.pi := by
  have hreflection := congrArg Prod.snd
    (n05_canonical_closed_reflection h04 hz hs m (hx 0)).1
  have hzero : (K.chart z m (r, 0)).2 = 0 := by
    simp only [neg_zero, Prod.fst, Prod.snd] at hreflection
    linarith only [hreflection]
  have hperiod := congrArg Prod.snd
    (n05_canonical_closed_periodicity h04 hz hs m (hx 0)).1
  refine ⟨hzero, ?_⟩
  simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.snd_add, Prod.snd, hzero]
    using hperiod

/-- Every actual common boundary map covers the whole original angular
half-period. Smoothness of an arbitrarily assigned endpoint inverse is
neither used nor concluded. -/
theorem n06_current_boundary_angular_surjOn
    {m : ℕ} {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets (K.chart z m) (K.height z m) r y σ β H ρ κ Hr)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hx : ∀ θ : ℝ, (r, θ) ∈ physicalPieceClosed S K z m) :
    β 0 = 0 ∧ β Real.pi = Real.pi ∧
      SurjOn β (Icc (0 : ℝ) Real.pi) (Icc (0 : ℝ) Real.pi) := by
  have hseams := n06_canonicalChart_closed_angle_seams h04 hz hs m hx
  have hzero : β 0 = 0 := by simpa only [J.chart_value 0] using hseams.1
  have hpi : β Real.pi = Real.pi := by
    simpa only [J.chart_value Real.pi] using hseams.2
  have he : (fun θ => (K.chart z m (r, θ)).2) = β :=
    funext (fun θ => congrArg Prod.snd (J.chart_value θ))
  have hc : Continuous (fun θ => (K.chart z m (r, θ)).2) :=
    continuous_iff_continuousAt.mpr (fun θ =>
      (J.chart_differentiable θ).continuousAt.snd.comp
        (continuousAt_const.prodMk continuousAt_id))
  rw [he] at hc
  refine ⟨hzero, hpi, ?_⟩
  change Icc (0 : ℝ) Real.pi ⊆ β '' Icc (0 : ℝ) Real.pi
  simpa only [hzero, hpi] using
    (intermediate_value_Icc Real.pi_pos.le hc.continuousOn)

end ContinuousFlexibility.Statements
