import ContinuousFlexibility.Blueprint.Statements
import Mathlib.Topology.Separation.Hausdorff

/-!
# Images of physical boundaries

The generic rectangle theorem uses only the open inverse and continuity.
For an actual state-dependent piece, the closed bijection and open inverse
send every frontier point to a canonical radial boundary. No current
physical domain is assumed to be a radial rectangle.
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

/-- Every point of the actual physical frontier maps to a canonical radial
boundary. The reference radial endpoints are not used for the current
state-dependent domain. -/
theorem canonicalChart_endpoint_radial_eq_boundary
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (p : PolarPoint)
    (hp : p ∈ frontier (physicalPieceOpen S K z m)) :
    (K.chart z m p).1 = K.left m ∨ (K.chart z m p).1 = K.right m := by
  have hcharts := hK.charts z hz hsector m
  have hclosed := hK.boundary z hz hsector m
  have hfront : p ∈ closure (physicalPieceOpen S K z m) ∧
      p ∉ physicalPieceOpen S K z m := by
    simpa only [(hK.domains z hz hsector m).1.frontier_eq] using hp
  have hpclosed : p ∈ physicalPieceClosed S K z m := hfront.1
  have himage := hclosed.1 hpclosed
  have hnot : K.chart z m p ∉ canonicalOpen S K m := by
    intro himageOpen
    apply hfront.2
    have hpre := hcharts.2.1 himageOpen
    rw [hclosed.2.2.1 p hpclosed] at hpre
    exact hpre
  rcases lt_or_eq_of_le himage.1.1 with hl | hl
  · rcases lt_or_eq_of_le himage.1.2 with hr | hr
    · exact False.elim (hnot ⟨⟨hl, hr⟩, mem_univ _⟩)
    · exact Or.inr hr
  · exact Or.inl hl.symm

end ContinuousFlexibility.Analysis
