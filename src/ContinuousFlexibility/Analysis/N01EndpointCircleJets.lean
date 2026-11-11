import ContinuousFlexibility.Analysis.N01EndpointAngularJets
import ContinuousFlexibility.Analysis.CircleJetAssembly

/-!
# Closed-radius flow selectors as scalar multilinear circle jet families

An arbitrary fixed radius is chosen in each closed N01 flow interval.
The genuine jets at these radii are viewed as multilinear fields on all
circle components. Their angular and parameter identities come from
the same towers; choosing `C.right` recovers the endpoint family.
All downstream estimates use the original full flow intervals for
localization, and the selector imposes no new analytic hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointCircleJetsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointCircleJetsRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def N01Properties.endpointFlowScalarJets
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => StateDirections S × ℝ) (ℕ → ℝ → ℝ) :=
  MultilinearMap.pi (fun m => MultilinearMap.pi (fun θ =>
    (hN.sectorFlow_closed_angularTower hS hT m (rsel m)
      (hrsel m) 0 θ).D n z |>.toMultilinearMap))

theorem N01Properties.endpointFlowScalarJets_apply
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (v : Fin n → (StateDirections S × ℝ))
    (m : ℕ) (θ : ℝ) :
    hN.endpointFlowScalarJets hS hT rsel hrsel n z v m θ =
      (hN.sectorFlow_closed_angularTower hS hT m (rsel m)
        (hrsel m) 0 θ).D n z v := rfl

theorem N01Properties.endpointFlowScalarJets_zero
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    hN.endpointFlowScalarJets hS hT rsel hrsel 0 z Fin.elim0 m θ =
      C.minusFlow (liftSectorParameter S C z) m (rsel m) θ -
        C.minusFlow (C.referenceState, 0) m (rsel m) θ := by
  rw [hN.endpointFlowScalarJets_apply hS hT rsel hrsel]
  exact (hN.sectorFlow_closed_angularTower hS hT m (rsel m)
    (hrsel m) 0 θ).zero z hz

theorem N01Properties.endpointFlowScalarJets_regular
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin n → (StateDirections S × ℝ)) (m : ℕ) :
    ContDiff ℝ ∞ (hN.endpointFlowScalarJets hS hT rsel hrsel n z v m) ∧
      Function.Periodic (hN.endpointFlowScalarJets hS hT rsel hrsel n z v m) Real.pi :=
  ⟨hN.sectorFlow_closed_angularTower_contDiff hS hT m (rsel m)
      (hrsel m) n 0 z hz v,
    hN.sectorFlow_closed_angularTower_periodic hS hT m (rsel m)
      (hrsel m) n 0 z hz v⟩

theorem N01Properties.endpointFlowScalarJets_iteratedDeriv
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin n → (StateDirections S × ℝ)) (m b : ℕ) (θ : ℝ) :
    iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel n z v m) θ =
      (hN.sectorFlow_closed_angularTower hS hT m (rsel m)
        (hrsel m) b θ).D n z v := by
  simpa only [Nat.zero_add] using
    hN.sectorFlow_closed_angularTower_iteratedDeriv hS hT m (rsel m)
      (hrsel m) n 0 b z hz v θ

theorem N01Properties.endpointFlowScalarJets_hasDerivAt_line
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (x w : StateDirections S × ℝ) (v : Fin n → (StateDirections S × ℝ))
    (t : ℝ) (ht : x + t • w ∈ sectorNeighborhood S base ε ε) (m b : ℕ) (θ : ℝ) :
    HasDerivAt (fun u => iteratedDeriv b
      (hN.endpointFlowScalarJets hS hT rsel hrsel n (x + u • w) v m) θ)
      (iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1)
        (x + t • w) (Fin.cons w v) m) θ) t := by
  rw [hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel (n + 1) _ ht]
  let J := hN.sectorFlow_closed_angularTower hS hT m (rsel m)
    (hrsel m) b θ
  apply (J.hasDerivAt_line_jet x w n v ht).congr_of_eventuallyEq
  have hline : Continuous (fun u : ℝ => x + u • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ u in 𝓝 t, x + u • w ∈ sectorNeighborhood S base ε ε :=
    hline.continuousAt.eventually ((sectorNeighborhood_isOpen S base ε ε).mem_nhds ht)
  filter_upwards [hmem] with u hu
  exact hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel n _ hu v m b θ

end ContinuousFlexibility.Statements
