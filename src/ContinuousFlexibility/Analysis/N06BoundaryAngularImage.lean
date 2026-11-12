import ContinuousFlexibility.Analysis.N06RootGreenDensity
import ContinuousFlexibility.Analysis.N06CurrentChartChange
import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual angular image of a closed piece boundary

The original open chart symmetry fixes the angular seams. Continuity of
the actual forward chart extends those values to either radial endpoint.
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

/-- The two angular seams retain their actual values on the whole closed
physical interval, including both possible radial endpoints. -/
theorem n06_canonicalChart_closed_angle_seams
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    (K.chart z m (r, 0)).2 = 0 ∧ (K.chart z m (r, Real.pi)).2 = Real.pi := by
  have hK := (n06_N04_qualitative_parts h04).1
  have hc := hK.2.2.2.2.2.2.2.1 z hz hs m
  have hreflection := hK.2.2.2.2.2.2.2.2.2.1 z hz hs m
  have hpF : ∀ p ∈ physicalPieceOpen S K m,
      K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) :=
    fun p hp => (hc.2.2.2.2.2.2.2 p hp).2.2.1
  have hopen (x : ℝ) (hx : x ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
      (K.chart z m (x, 0)).2 = 0 ∧
        (K.chart z m (x, Real.pi)).2 = Real.pi :=
    n06_chart_angle_seams hpF (fun p hp => (hreflection p hp).1) hx
  have hcont (θ : ℝ) :
      ContinuousOn (fun x => (K.chart z m (x, θ)).2)
        (Icc (K.physicalLeft m) (K.physicalRight m)) := by
    intro x hx
    have hd := (h04.2.2.2.2.2.2.2.2.1 z hz hs m (x, θ) hx).1
    have hline : ContinuousAt (fun t : ℝ => (t, θ)) x :=
      continuousAt_id.prodMk continuousAt_const
    have houter : ContinuousAt (fun p : PolarPoint => (K.chart z m p).2) (x, θ) :=
      hd.continuousAt.snd
    have he : ContinuousAt (fun t : ℝ => (K.chart z m (t, θ)).2) x :=
      ContinuousAt.comp (f := fun t : ℝ => (t, θ)) (x := x) houter hline
    exact he.continuousWithinAt
  have hsub : Ioo (K.physicalLeft m) (K.physicalRight m) ⊆
      Icc (K.physicalLeft m) (K.physicalRight m) := fun _ hx => mem_Icc_of_Ioo hx
  have hclosure : Icc (K.physicalLeft m) (K.physicalRight m) ⊆
      closure (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
    simpa only [closure_Ioo (h04.2.2.2.1 m).1.ne] using
      (Subset.rfl : Icc (K.physicalLeft m) (K.physicalRight m) ⊆
        Icc (K.physicalLeft m) (K.physicalRight m))
  have hzero : EqOn (fun x => (K.chart z m (x, 0)).2) (fun _ => (0 : ℝ))
      (Ioo (K.physicalLeft m) (K.physicalRight m)) := fun x hx => (hopen x hx).1
  have hpi : EqOn (fun x => (K.chart z m (x, Real.pi)).2) (fun _ => Real.pi)
      (Ioo (K.physicalLeft m) (K.physicalRight m)) := fun x hx => (hopen x hx).2
  exact ⟨hzero.of_subset_closure (hcont 0) continuousOn_const hsub hclosure hr,
    hpi.of_subset_closure (hcont Real.pi) continuousOn_const hsub hclosure hr⟩

/-- Every actual common boundary map covers the whole original angular
half-period. Smoothness of an arbitrarily assigned endpoint inverse is
neither used nor concluded. -/
theorem n06_current_boundary_angular_surjOn
    {m : ℕ} {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets (K.chart z m) (K.height z m) r y σ β H ρ κ Hr)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    β 0 = 0 ∧ β Real.pi = Real.pi ∧
      SurjOn β (Icc (0 : ℝ) Real.pi) (Icc (0 : ℝ) Real.pi) := by
  have hseams := n06_canonicalChart_closed_angle_seams h04 hz hs m hr
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
