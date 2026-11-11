import ContinuousFlexibility.Blueprint.Statements
import Mathlib.Topology.Separation.Hausdorff

/-!
# Images of physical endpoints

The frozen chart assumptions only specify the inverse on the open pieces.
Nevertheless continuity of the forward chart and continuity of that open
inverse force every physical endpoint to map to a canonical endpoint.
This does not prescribe the value of the totalized inverse at the endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem image_not_mem_open_of_boundary_leftInverse
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {U : Set X} {V : Set Y} {F : X → Y} {G : Y → X} {p : X}
    (hV : IsOpen V) (hF : ContinuousAt F p) (hG : ContinuousOn G V)
    (hmap : MapsTo G V U) (hinv : EqOn (fun x => G (F x)) id U)
    (hp : p ∈ closure U) (hpU : p ∉ U) : F p ∉ V := by
  intro hpV
  haveI : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hGF : ContinuousAt (fun x => G (F x)) p :=
    (hG.continuousAt (hV.mem_nhds hpV)).comp hF
  have he : G (F p) = p :=
    tendsto_nhds_unique_of_eventuallyEq
      (hGF.mono_left nhdsWithin_le_nhds)
      (continuousAt_id.mono_left nhdsWithin_le_nhds)
      (hinv.eventuallyEq_of_mem self_mem_nhdsWithin)
  exact hpU (by simpa only [he] using hmap hpV)

/-- The endpoint image is one of the two target endpoints. The argument
uses the actual open-strip inverse, not a chosen boundary extension. -/
theorem endpoint_image_mem_boundary_of_openStrip_inverse
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {F G : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : ContinuousAt F p)
    (hG : ContinuousOn G (Ioo c d ×ˢ (univ : Set ℝ)))
    (hmapF : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ)) (Ioo c d ×ˢ (univ : Set ℝ)))
    (hmapG : MapsTo G (Ioo c d ×ˢ (univ : Set ℝ)) (Ioo a b ×ˢ (univ : Set ℝ)))
    (hinv : ∀ x ∈ Ioo a b ×ˢ (univ : Set ℝ), G (F x) = x)
    (hp : p.1 = a ∨ p.1 = b) : (F p).1 = c ∨ (F p).1 = d := by
  have hpcc : p.1 ∈ Icc a b := by
    rcases hp with h | h
    · rw [h]
      exact ⟨le_rfl, hab.le⟩
    · rw [h]
      exact ⟨hab.le, le_rfl⟩
  have hpcl : p ∈ closure (Ioo a b ×ˢ (univ : Set ℝ)) := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_univ]
    exact ⟨hpcc, mem_univ _⟩
  have hcl := hF.continuousWithinAt.mem_closure hpcl hmapF
  rw [closure_prod_eq, closure_Ioo hcd.ne, closure_univ] at hcl
  have hpnot : p ∉ Ioo a b ×ˢ (univ : Set ℝ) := by
    intro hpin
    rcases hp with h | h
    · simpa only [h, lt_self_iff_false] using hpin.1.1
    · simpa only [h, lt_self_iff_false] using hpin.1.2
  have hnot := image_not_mem_open_of_boundary_leftInverse
    (isOpen_Ioo.prod isOpen_univ) hF hG hmapG hinv hpcl hpnot
  rcases lt_or_eq_of_le hcl.1.1 with hl | hl
  · rcases lt_or_eq_of_le hcl.1.2 with hr | hr
    · exact False.elim (hnot ⟨⟨hl, hr⟩, mem_univ _⟩)
    · exact Or.inr hr
  · exact Or.inl hl.symm

/-- In particular, PartA itself determines that the physical endpoints
land on canonical endpoints, although it does not specify their order. -/
theorem canonicalChart_endpoint_radial_eq_boundary
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (p : PolarPoint)
    (hp : p.1 = K.physicalLeft m ∨ p.1 = K.physicalRight m) :
    (K.chart z m p).1 = K.left m ∨ (K.chart z m p).1 = K.right m := by
  have hpiece := hK.2.2.2.1 m
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  have hpcc : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) := by
    rcases hp with h | h
    · rw [h]
      exact ⟨le_rfl, hpiece.1.le⟩
    · rw [h]
      exact ⟨hpiece.1.le, le_rfl⟩
  have hclosed := hK.2.2.2.2.2.2.2.2.1 z hz hsector m p hpcc
  exact endpoint_image_mem_boundary_of_openStrip_inverse hpiece.1 hpiece.2.1
    hclosed.1.continuousAt hcharts.2.2.2.2.2.1.continuousOn
    hcharts.1 hcharts.2.1 hcharts.2.2.1 hp

end ContinuousFlexibility.Analysis
