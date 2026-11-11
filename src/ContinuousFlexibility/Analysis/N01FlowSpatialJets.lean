import ContinuousFlexibility.Analysis.N01FlowMixedParameterTower
import ContinuousFlexibility.Analysis.N01FlowCollarJetBounds
import ContinuousFlexibility.Analysis.MixedDerivativeHierarchy
import ContinuousFlexibility.Analysis.SmoothDirectionsSpatialJets
import ContinuousFlexibility.Analysis.SmoothDirectionsLocalJointAngular
import ContinuousFlexibility.Analysis.LocalJointJetSeminormBounds

/-!
# Spatial regularity of the actual N01 parameter jets on an interior strip

The only geometric condition is positivity of the actual discriminant
on the chosen strip. The optical collar supplies this condition on the
neighborhood used in the correction. All higher parameter-jet spatial
derivatives follow from the original N01 bounds and local FTC.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01FlowSpatialJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)
  (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ p : PolarPoint,
    p.1 ∈ Ioo l h →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

def N01Properties.sectorFlowStripTower
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ)) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => ordinaryFlowFamily S C m a b p (liftSectorParameter S C z)) :=
  hN.sectorFlowMixedTower m a b p ⟨hl.trans hp.1.1, hp.1.2.trans hh⟩

include hT in
theorem N01Properties.sectorFlowStripTower_uniform (a b : ℕ) :
    UniformScalarJetSeminormBounds (fun p : Ioo l h ×ˢ (univ : Set ℝ) =>
      hN.sectorFlowStripTower m l h hl hh a b p p.property) := by
  exact (hN.sectorFlowMixedTower_uniform_on_radial_interval hT m a b l h hl hh).reindex
    (fun p : Ioo l h ×ˢ (univ : Set ℝ) =>
      ((⟨p.1.1, ⟨p.2.1.1.le, p.2.1.2.le⟩⟩ : Icc l h), p.1.2))

include hT in
theorem N01Properties.sectorFlowStripTower_localUniform (a b : ℕ) :
    LocalUniformScalarJetSeminormBounds (hN.sectorFlowStripTower m l h hl hh a b) := by
  intro p hp
  exact ⟨Ioo l h ×ˢ univ, subset_rfl, isOpen_Ioo.prod isOpen_univ, hp,
    hN.sectorFlowStripTower_uniform hT m l h hl hh a b⟩

include hN hS hT hl hh hdisc

theorem N01Properties.sectorFlowStrip_increment_contDiffOn
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      C.minusFlow (liftSectorParameter S C z) m p.1 p.2 -
        C.minusFlow (C.referenceState, 0) m p.1 p.2) (Ioo l h ×ˢ univ) := by
  have hactual : ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      C.minusFlow (liftSectorParameter S C z) m p.1 p.2) (Ioo l h ×ˢ univ) := by
    intro p hp
    exact (hN.minusFlow_contDiffAt_of_discriminant hS hT
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z) m p
      ⟨hl.trans hp.1.1, hp.1.2.trans hh⟩
      (hdisc z hz (p.1, C.minusFlow (liftSectorParameter S C z) m p.1 p.2) hp.1)).contDiffWithinAt
  have href : ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      C.minusFlow (C.referenceState, 0) m p.1 p.2) (Ioo l h ×ˢ univ) := by
    intro p hp
    exact (hN.minusFlow_reference_contDiffAt hS hT m p
      ⟨hl.trans hp.1.1, hp.1.2.trans hh⟩).contDiffWithinAt
  exact hactual.sub href

theorem N01Properties.sectorFlowStrip_spatial_contDiffOn
    (a b : ℕ) (z : StateDirections S × ℝ)
    (hz : z ∈ sectorNeighborhood S base ε ε) :
    ContDiffOn ℝ ∞ (fun p => ordinaryFlowFamily S C m a b p
      (liftSectorParameter S C z)) (Ioo l h ×ˢ univ) :=
  contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ)
    (hN.sectorFlowStrip_increment_contDiffOn hS hT m l h hl hh hdisc z hz) a b

theorem N01Properties.sectorFlowStrip_hasDerivAt_radial
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    HasDerivAt (fun r => ordinaryFlowFamily S C m a b (r, p.2) (liftSectorParameter S C z))
      (ordinaryFlowFamily S C m (a + 1) b p (liftSectorParameter S C z)) p.1 :=
  mixedDerivative_hasDerivAt_radial (isOpen_Ioo.prod isOpen_univ)
    (hN.sectorFlowStrip_increment_contDiffOn hS hT m l h hl hh hdisc z hz) a b hp

theorem N01Properties.sectorFlowStrip_hasDerivAt_angular
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    HasDerivAt (fun θ => ordinaryFlowFamily S C m a b (p.1, θ) (liftSectorParameter S C z))
      (ordinaryFlowFamily S C m a (b + 1) p (liftSectorParameter S C z)) p.2 :=
  mixedDerivative_hasDerivAt_angular (isOpen_Ioo.prod isOpen_univ)
    (hN.sectorFlowStrip_increment_contDiffOn hS hT m l h hl hh hdisc z hz) a b hp

theorem N01Properties.sectorFlowStrip_parameterJets_contDiffOn
    (a b n : ℕ) (z : StateDirections S × ℝ)
    (hz : z ∈ sectorNeighborhood S base ε ε) (v : Fin n → StateDirections S × ℝ) :
    ContDiffOn ℝ ∞
      (localScalarJet (hN.sectorFlowStripTower m l h hl hh a b) n z v)
      (Ioo l h ×ˢ univ) :=
  localScalarJet_spatial_contDiffOn (hN.sectorFlowStripTower m l h hl hh)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (isOpen_Ioo.prod isOpen_univ)
    (fun i j x hx => (hN.sectorFlowStrip_spatial_contDiffOn hS hT m l h hl hh hdisc
      i j x hx).continuousOn)
    (hN.sectorFlowStripTower_localUniform hT m l h hl hh)
    (hN.sectorFlowStrip_hasDerivAt_radial hS hT m l h hl hh hdisc)
    (hN.sectorFlowStrip_hasDerivAt_angular hS hT m l h hl hh hdisc) a b n z hz v

theorem N01Properties.sectorFlowStrip_parameterJets_mixedDerivative
    (a b n : ℕ) {p : PolarPoint} (hp : p ∈ Ioo l h ×ˢ (univ : Set ℝ))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin n → StateDirections S × ℝ) :
    mixedDerivative a b
        (localScalarJet (hN.sectorFlowStripTower m l h hl hh 0 0) n z v) p =
      (hN.sectorFlowStripTower m l h hl hh a b p hp).D n z v :=
  localScalarJet_spatial_mixedDerivative (hN.sectorFlowStripTower m l h hl hh)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (isOpen_Ioo.prod isOpen_univ)
    (fun i j x hx => (hN.sectorFlowStrip_spatial_contDiffOn hS hT m l h hl hh hdisc
      i j x hx).continuousOn)
    (hN.sectorFlowStripTower_localUniform hT m l h hl hh)
    (hN.sectorFlowStrip_hasDerivAt_radial hS hT m l h hl hh hdisc)
    (hN.sectorFlowStrip_hasDerivAt_angular hS hT m l h hl hh hdisc) a b n hp z hz v

def N01Properties.sectorFlow_radialJointTower (b : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (fun z : (StateDirections S × ℝ) × ℝ =>
        ordinaryFlowFamily S C m 0 b (z.2, θ) (liftSectorParameter S C z.1)) := by
  let J : ∀ a r, r ∈ Ioo l h → SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => ordinaryFlowFamily S C m a b (r, θ) (liftSectorParameter S C z)) :=
    fun a r hr => hN.sectorFlowStripTower m l h hl hh a b (r, θ) ⟨hr, mem_univ θ⟩
  apply localAngularTowerJointDirectionsOfUniform J
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε) isOpen_Ioo
  · intro a z hz
    exact (hN.sectorFlowStrip_spatial_contDiffOn hS hT m l h hl hh hdisc a b z hz).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ θ⟩)
  · intro a
    exact (hN.sectorFlowStripTower_uniform hT m l h hl hh a b).reindex
      (fun r : Ioo l h => (⟨((r : ℝ), θ), ⟨r.property, mem_univ θ⟩⟩ : Ioo l h ×ˢ univ))
  · intro a r hr z hz
    exact hN.sectorFlowStrip_hasDerivAt_radial hS hT m l h hl hh hdisc a b
      (r, θ) ⟨hr, mem_univ θ⟩ z hz

theorem N01Properties.sectorFlow_radialJointTower_uniform (b : ℕ) :
    UniformScalarJetSeminormBounds
      (hN.sectorFlow_radialJointTower hS hT m l h hl hh hdisc b) := by
  let J : ∀ a θ r, r ∈ Ioo l h → SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => ordinaryFlowFamily S C m a b (r, θ) (liftSectorParameter S C z)) :=
    fun a θ r hr => hN.sectorFlowStripTower m l h hl hh a b (r, θ) ⟨hr, mem_univ θ⟩
  apply uniformScalarJetSeminormBounds_local_joint J
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε) isOpen_Ioo
    _ _ _ (hN.sectorFlow_radialJointTower hS hT m l h hl hh hdisc b)
  · intro a θ z hz
    exact (hN.sectorFlowStrip_spatial_contDiffOn hS hT m l h hl hh hdisc a b z hz).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ θ⟩)
  · intro a
    exact (hN.sectorFlowStripTower_uniform hT m l h hl hh a b).reindex
      (fun p : ℝ × Ioo l h =>
        (⟨((p.2 : ℝ), p.1), ⟨p.2.property, mem_univ p.1⟩⟩ : Ioo l h ×ˢ univ))
  · intro a θ r hr z hz
    exact hN.sectorFlowStrip_hasDerivAt_radial hS hT m l h hl hh hdisc a b
      (r, θ) ⟨hr, mem_univ θ⟩ z hz

end ContinuousFlexibility.Statements
