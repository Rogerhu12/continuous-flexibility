import ContinuousFlexibility.Analysis.N01EndpointAngularJets
import ContinuousFlexibility.Analysis.CircleJetAssembly

/-!
# The actual endpoint flow as a scalar multilinear circle jet family

These are the genuine closed-radius N01 jets, selected once and then
viewed as multilinear fields on all circle components. Their angular
and parameter derivative identities are inherited from the same towers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def N01Properties.endpointFlowScalarJets
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (n : ℕ) (z : StateDirections S × ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => StateDirections S × ℝ) (ℕ → ℝ → ℝ) :=
  MultilinearMap.pi (fun m => MultilinearMap.pi (fun θ =>
    (hN.sectorFlow_closed_angularTower hS hT m (C.right m)
      ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩ 0 θ).D n z |>.toMultilinearMap))

theorem N01Properties.endpointFlowScalarJets_apply
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (n : ℕ) (z : StateDirections S × ℝ) (v : Fin n → (StateDirections S × ℝ))
    (m : ℕ) (θ : ℝ) :
    hN.endpointFlowScalarJets hS hT n z v m θ =
      (hN.sectorFlow_closed_angularTower hS hT m (C.right m)
        ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩ 0 θ).D n z v := rfl

theorem N01Properties.endpointFlowScalarJets_zero
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    hN.endpointFlowScalarJets hS hT 0 z Fin.elim0 m θ =
      C.minusFlow (liftSectorParameter S C z) m (C.right m) θ -
        C.minusFlow (C.referenceState, 0) m (C.right m) θ := by
  rw [hN.endpointFlowScalarJets_apply hS hT]
  exact (hN.sectorFlow_closed_angularTower hS hT m (C.right m)
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩ 0 θ).zero z hz

theorem N01Properties.endpointFlowScalarJets_regular
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin n → (StateDirections S × ℝ)) (m : ℕ) :
    ContDiff ℝ ∞ (hN.endpointFlowScalarJets hS hT n z v m) ∧
      Function.Periodic (hN.endpointFlowScalarJets hS hT n z v m) Real.pi :=
  ⟨hN.sectorFlow_closed_angularTower_contDiff hS hT m (C.right m)
      ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩ n 0 z hz v,
    hN.sectorFlow_closed_angularTower_periodic hS hT m (C.right m)
      ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩ n 0 z hz v⟩

theorem N01Properties.endpointFlowScalarJets_iteratedDeriv
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin n → (StateDirections S × ℝ)) (m b : ℕ) (θ : ℝ) :
    iteratedDeriv b (hN.endpointFlowScalarJets hS hT n z v m) θ =
      (hN.sectorFlow_closed_angularTower hS hT m (C.right m)
        ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩ b θ).D n z v := by
  simpa only [Nat.zero_add] using
    hN.sectorFlow_closed_angularTower_iteratedDeriv hS hT m (C.right m)
      ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩ n 0 b z hz v θ

theorem N01Properties.endpointFlowScalarJets_hasDerivAt_line
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (n : ℕ) (x w : StateDirections S × ℝ) (v : Fin n → (StateDirections S × ℝ))
    (t : ℝ) (ht : x + t • w ∈ sectorNeighborhood S base ε ε) (m b : ℕ) (θ : ℝ) :
    HasDerivAt (fun u => iteratedDeriv b
      (hN.endpointFlowScalarJets hS hT n (x + u • w) v m) θ)
      (iteratedDeriv b (hN.endpointFlowScalarJets hS hT (n + 1)
        (x + t • w) (Fin.cons w v) m) θ) t := by
  rw [hN.endpointFlowScalarJets_iteratedDeriv hS hT (n + 1) _ ht]
  let J := hN.sectorFlow_closed_angularTower hS hT m (C.right m)
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩ b θ
  apply (J.hasDerivAt_line_jet x w n v ht).congr_of_eventuallyEq
  have hline : Continuous (fun u : ℝ => x + u • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ u in 𝓝 t, x + u • w ∈ sectorNeighborhood S base ε ε :=
    hline.continuousAt.eventually ((sectorNeighborhood_isOpen S base ε ε).mem_nhds ht)
  filter_upwards [hmem] with u hu
  exact hN.endpointFlowScalarJets_iteratedDeriv hS hT n _ hu v m b θ

end ContinuousFlexibility.Statements
