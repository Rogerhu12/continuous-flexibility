import ContinuousFlexibility.Analysis.N04NegativeGeometryTravelMonotonicity
import ContinuousFlexibility.Analysis.N04NegativeGeometryTravelInverseContinuity
import ContinuousFlexibility.Analysis.N04bActualDomainGeometry

/-!
# Joint continuity and inverse identities of the stored negative charts

The actual travel inverse is continuous by its two proved monotonicities.
The fixed root substitution and the prescribed inverse germ identify it
with the stored inverse on the canonical strip. The forward chart is
injective on the whole original component, independently of the moving
physical half-domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

variable (W : N04RealizationStart)

theorem negativeTravelInverse_continuousOn (m : ℕ) :
    ContinuousOn
      (fun q : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualTravelInverse W.S W.C W.L (liftSectorParameter W.S W.C q.1) m q.2)
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (W.C.travel m) ×ˢ univ)) := by
  apply n04NegativeGeometry_travelInverse_continuousOn
    (W.negativeTravelJointTower m).continuousOn
  · intro z hz r hr
    exact (W.negativeTravelMonotonicity m hz).1 r (Ioo_subset_Icc_self hr)
  · intro z hz r hr
    exact (W.negativeTravelMonotonicity m hz).2.1 r (Ioo_subset_Icc_self hr)
  · intro z hz θ
    exact ((W.negativeTravelMonotonicity m hz).2.2 θ).mono Ioo_subset_Icc_self
  · intro q hq
    exact (n04b_actualTravelInverse_spec W.through03 W.hS W.hT W.field
      (liftSectorParameter_mem_stateNeighborhood hq.1 le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector q.1) m).1 hq.2
  · intro q hq
    exact (n04b_actualTravelInverse_spec W.through03 W.hS W.hT W.field
      (liftSectorParameter_mem_stateNeighborhood hq.1 le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector q.1) m).2.2.1 hq.2

/-- Continuity belongs to the actual chosen inverse, in state and target
point simultaneously, on the original sector neighborhood. -/
theorem negativeInverse_continuousOn (m : ℕ) (side : Bool) :
    ContinuousOn
      (fun q : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeInverse W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C q.1) m side q.2)
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ)) := by
  have hmap : MapsTo
      (fun q : (StateDirections W.S × ℝ) × PolarPoint =>
        (q.1, n04bRootStripInverse (W.C.travel m) side q.2))
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ))
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (W.C.travel m) ×ˢ univ)) := by
    intro q hq
    have hT := n04b_actualTravel_positive W.through03 W.hS W.hT W.field
      (liftSectorParameter_mem_stateNeighborhood hq.1 le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector q.1) m
    exact ⟨hq.1, n04b_rootStripInverse_mem_full_of_pos hT side
      ⟨hq.2.1.1, hq.2.1.2.le⟩⟩
  have hraw := (W.negativeTravelInverse_continuousOn m).comp
    (continuous_fst.prodMk
      ((n04b_continuous_rootStripInverse (W.C.travel m) side).comp continuous_snd)).continuousOn
    hmap
  apply hraw.congr
  intro q hq
  exact (n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    (liftSectorParameter_mem_stateNeighborhood hq.1 le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector q.1) m side).open_inverse_eq hq.2

/-- The stored forward chart is injective throughout the original open
component, including points beyond the current moving half-domain. -/
theorem negativeChart_injOn (m : ℕ) (side : Bool) {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε) :
    InjOn (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side)
      (Ioo (W.C.left m) (W.C.right m) ×ˢ univ) := by
  let w := liftSectorParameter W.S W.C z
  let F := n04bActualTravelChart W.S W.C W.L w m
  let X := n04bActualTravelInverse W.S W.C W.L w m
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hB := n04b_actualTravelChart_bijOn W.through03 W.hS W.hT W.field hw hs m
  have hX := n04b_actualTravelInverse_spec W.through03 W.hS W.hT W.field hw hs m
  have H := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side
  have hleft (p : PolarPoint)
      (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
      n04bRootPhysicalInverse X (W.C.travel m) side
        (n04bActualNegativeChart W.hT W.hS W.through03 W.field w m side p) = p := by
    rw [(H.component_chart_germ hp).self_of_nhds]
    change X (n04bRootStripInverse (W.C.travel m) side
      (n04bRootStripChart (W.C.travel m) side (F p))) = p
    rw [n04bRootStripInverse_chart_of_oriented_nonneg (W.C.travel m) side
      (n04b_travelOrientation_pos_of_fullStrip side (hB.mapsTo hp).1).le]
    exact hX.2.1 hp
  intro p hp q hq he
  exact (hleft p hp).symm.trans
    ((congrArg (n04bRootPhysicalInverse X (W.C.travel m) side) he).trans (hleft q hq))

/-- The actual inverse stays in the full physical component and is a
right inverse there. These are exactly the fibre hypotheses of the
parameterized inverse tower, on fixed domains. -/
theorem negativeInverse_maps_right (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε) :
    let F := n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side
    let G := n04bActualNegativeInverse W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side
    MapsTo G (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ)
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ) ∧
      RightInvOn G F (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ) := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have H := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side
  have hd := H.open_chart_data W.through03 W.hS W.hT W.field hw hs
  exact ⟨fun q hq => n04b_actualNegativeDomain_subset_component W.C W.L
    (liftSectorParameter W.S W.C z) m side (hd.2.1 hq), hd.2.2.2⟩

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverse_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverse_continuousOn
