import ContinuousFlexibility.Analysis.N01EndpointParameterTower
import ContinuousFlexibility.Analysis.SmoothDirectionsAngularJets

/-!
# The actual closed-radius N01 tower as a smooth angular family

One genuine tower is selected for each angular jet and angle. Uniqueness
transfers every sharp N01 bound to those same towers. Their angular
derivatives, joint continuity and periodicity then follow from the
actual flow and the generic angular-jet theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.ordinaryFlowFamily_angular_hasDerivAt
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m b : ℕ) {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    HasDerivAt (fun ψ => ordinaryFlowFamily S C m 0 b (r, ψ) z)
      (ordinaryFlowFamily S C m 0 (b + 1) (r, θ) z) θ := by
  have href : referenceStateConditions D S C := hN.2.2.1
  have hF : ContDiff ℝ ∞ (fun ψ =>
      C.minusFlow z m r ψ - C.minusFlow (C.referenceState, 0) m r ψ) :=
    (hN.minusFlow_angular_contDiff hS hT hz hsector m hr).sub
      (hN.minusFlow_angular_contDiff hS hT hN.reference_mem_stateNeighborhood
        href.stateSector m hr)
  have hd := (hF.differentiable_iteratedDeriv b (by simp) θ).hasDerivAt
  simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero,
    iteratedDeriv_succ] using hd

theorem N01Properties.ordinaryFlowFamily_angular_periodic
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m b : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    Function.Periodic (fun θ => ordinaryFlowFamily S C m 0 b (r, θ) z) Real.pi := by
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  let F : ℝ → ℝ := fun θ =>
    C.minusFlow z m r θ - C.minusFlow (C.referenceState, 0) m r θ
  have hperiod : Function.Periodic F Real.pi := by
    intro θ
    dsimp only [F]
    rw [((hflow z hz m θ).2.2.2 r hr).2,
      ((hflow (C.referenceState, 0) hN.reference_mem_stateNeighborhood m θ).2.2.2 r hr).2]
    ring
  have heq : (fun θ => F (θ + Real.pi)) = F := funext hperiod
  intro θ
  have hj := congrArg (fun G : ℝ → ℝ => iteratedDeriv b G θ) heq
  simpa only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero,
    iteratedDeriv_comp_add_const, F] using hj

/-- A selected genuine tower for the actual closed-radius angular jet.
All estimates below concern this one family of towers. -/
def N01Properties.sectorFlow_closed_angularTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (b : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C z)) :=
  ((hN.sectorFlow_closed_tower hS hT 0 b).choose_spec.2 m b θ r le_rfl hr).choose

/-- The chosen towers retain the full original bound, simultaneously
for every component, closed radial point and angle. -/
theorem N01Properties.sectorFlow_closed_angularTower_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r (hr : r ∈ Icc (C.left m) (C.right m)) b θ,
      b ≤ s → ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ v : Fin k → (StateDirections S × ℝ),
        |(hN.sectorFlow_closed_angularTower hS hT m r hr b θ).D k z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B *
            oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
              base (s + loss) z v := by
  let hdata := hN.sectorFlow_closed_tower hS hT k s
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hpoint : ∀ (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (b : ℕ) (θ : ℝ),
      b ≤ s → ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ v : Fin k → (StateDirections S × ℝ),
        |(hN.sectorFlow_closed_angularTower hS hT m r hr b θ).D k z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B *
            oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
              base (s + loss) z v := by
    intro m r hr b θ hb z hz v
    let htower := hdata.choose_spec.2 m b θ r hb hr
    have heq : (hN.sectorFlow_closed_angularTower hS hT m r hr b θ).D k z =
        htower.choose.D k z :=
      (hN.sectorFlow_closed_angularTower hS hT m r hr b θ).unique htower.choose k z hz
    rw [heq]
    exact htower.choose_spec z hz v
  exact Exists.intro B (And.intro hB hpoint)

theorem N01Properties.sectorFlow_closed_angularTower_uniformBounds
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (b : ℕ) :
    UniformScalarJetSeminormBounds (hN.sectorFlow_closed_angularTower hS hT m r hr b) := by
  apply uniformScalarJetSeminormBounds_of_oneHigh
    (pairGrading (sectorGrading S) realGrading)
    (sectorPairGrading_continuous S) (sectorPairGrading_monotone S)
    base (fun _ => b + loss)
  intro n
  let hdata := hN.sectorFlow_closed_angularTower_bound hS hT n b
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hsample := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 (C.cell m)
  have hp := hT.2.1 _ hsample
  refine ⟨B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B,
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg hp.2.1.le _))
      (Real.rpow_nonneg hp.2.2.1.le _), ?_⟩
  intro θ z hz v
  exact hdata.choose_spec.2 m r hr b θ le_rfl z hz v

theorem N01Properties.sectorFlow_closed_angularTower_hasDerivAt
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (k b : ℕ)
    (θ : ℝ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin k → (StateDirections S × ℝ)) :
    HasDerivAt (fun ψ => (hN.sectorFlow_closed_angularTower hS hT m r hr b ψ).D k z v)
      ((hN.sectorFlow_closed_angularTower hS hT m r hr (b + 1) θ).D k z v) θ := by
  exact smoothDirections_angular_jet_hasDerivAt
    (fun b θ => hN.sectorFlow_closed_angularTower hS hT m r hr b θ)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (hN.sectorFlow_closed_angularTower_uniformBounds hS hT m r hr)
    (fun b θ y hy => hN.ordinaryFlowFamily_angular_hasDerivAt hS hT
      (liftSectorParameter_mem_stateNeighborhood hy (le_refl ε))
      (hN.2.2.1.liftSectorParameter_sector y) m b hr θ) k b θ z hz v

theorem N01Properties.sectorFlow_closed_angularTower_joint_continuous
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (k b : ℕ) :
    ContinuousOn
      (fun p : ℝ × ((StateDirections S × ℝ) × (Fin k → (StateDirections S × ℝ))) =>
        (hN.sectorFlow_closed_angularTower hS hT m r hr b p.1).D k p.2.1 p.2.2)
      (univ ×ˢ (sectorNeighborhood S base ε ε ×ˢ univ)) := by
  apply smoothDirections_angular_jet_joint_continuous
    (hN.sectorFlow_closed_angularTower hS hT m r hr b)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (hbound := hN.sectorFlow_closed_angularTower_uniformBounds hS hT m r hr b)
  intro z hz
  exact continuous_iff_continuousAt.mpr (fun θ =>
    (hN.ordinaryFlowFamily_angular_hasDerivAt hS hT
      (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
      (hN.2.2.1.liftSectorParameter_sector z) m b hr θ).continuousAt)

theorem N01Properties.sectorFlow_closed_angularTower_contDiff
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (k b : ℕ)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin k → (StateDirections S × ℝ)) :
    ContDiff ℝ ∞ (fun θ => (hN.sectorFlow_closed_angularTower hS hT m r hr b θ).D k z v) := by
  exact smoothDirections_angular_jet_contDiff
    (fun b θ => hN.sectorFlow_closed_angularTower hS hT m r hr b θ)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (hN.sectorFlow_closed_angularTower_uniformBounds hS hT m r hr)
    (fun b θ y hy => hN.ordinaryFlowFamily_angular_hasDerivAt hS hT
      (liftSectorParameter_mem_stateNeighborhood hy (le_refl ε))
      (hN.2.2.1.liftSectorParameter_sector y) m b hr θ) k b z hz v

theorem N01Properties.sectorFlow_closed_angularTower_iteratedDeriv
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (k b n : ℕ)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin k → (StateDirections S × ℝ)) (θ : ℝ) :
    iteratedDeriv n (fun ψ => (hN.sectorFlow_closed_angularTower hS hT m r hr b ψ).D k z v) θ =
      (hN.sectorFlow_closed_angularTower hS hT m r hr (b + n) θ).D k z v := by
  exact smoothDirections_angular_jet_iteratedDeriv
    (fun b θ => hN.sectorFlow_closed_angularTower hS hT m r hr b θ)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (hN.sectorFlow_closed_angularTower_uniformBounds hS hT m r hr)
    (fun b θ y hy => hN.ordinaryFlowFamily_angular_hasDerivAt hS hT
      (liftSectorParameter_mem_stateNeighborhood hy (le_refl ε))
      (hN.2.2.1.liftSectorParameter_sector y) m b hr θ) k b n z hz v θ

theorem N01Properties.sectorFlow_closed_angularTower_periodic
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) (k b : ℕ)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin k → (StateDirections S × ℝ)) :
    Function.Periodic
      (fun θ => (hN.sectorFlow_closed_angularTower hS hT m r hr b θ).D k z v) Real.pi := by
  intro θ
  let Jshift := hN.sectorFlow_closed_angularTower hS hT m r hr b (θ + Real.pi)
  let Jhere := hN.sectorFlow_closed_angularTower hS hT m r hr b θ
  let K := Jshift.congrOn (fun y hy => hN.ordinaryFlowFamily_angular_periodic
    (liftSectorParameter_mem_stateNeighborhood hy (le_refl ε)) m b hr θ)
  exact congrArg (fun A => A v) (K.unique Jhere k z hz)

end ContinuousFlexibility.Statements
