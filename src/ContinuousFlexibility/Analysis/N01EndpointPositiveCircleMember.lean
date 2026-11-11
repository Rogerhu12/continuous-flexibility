import ContinuousFlexibility.Analysis.N01EndpointStateCircleMember
import ContinuousFlexibility.Analysis.N01EndpointScalarCircleMember
import ContinuousFlexibility.Analysis.ScalarJetSchwarz

/-!
# All positive-order endpoint jets are actual circle fields

A cyclic identity moves any state slot to the localized last slot.
The exact multilinear telescoping identity then separates an arbitrary
tuple into its pure scalar part and finitely many tuples with a state
slot. Every term lies in the range of the actual circle decoder.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointPositiveCircleMemberStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointPositiveCircleMemberRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowScalarJets_rotate
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) :
    hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v =
      hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc (Fin.tail v) (v 0)) := by
  funext m θ
  rw [hN.endpointFlowScalarJets_apply hS hT rsel hrsel, hN.endpointFlowScalarJets_apply hS hT rsel hrsel]
  let J := hN.sectorFlow_closed_angularTower hS hT m (rsel m)
    (hrsel m) 0 θ
  simpa only [Fin.cons_self_tail] using
    J.cons_eq_snoc (sectorNeighborhood_convex S base ε ε) n z hz (v 0) (Fin.tail v)

theorem N01Properties.endpointFlowScalarJets_circleMember_of_state_slot
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ))
    (i : Fin (n + 1)) (hi : (v i).2 = 0) :
    CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) := by
  have haux : ∀ k : ℕ, ∀ (w : Fin (n + 1) → (StateDirections S × ℝ))
      (j : Fin (n + 1)), j.val = k → (w j).2 = 0 →
      CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z w) := by
    intro k
    induction k with
    | zero =>
      intro w j hj hw
      have hj0 : j = 0 := Fin.ext hj
      rw [hj0] at hw
      rw [hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w]
      exact hN.endpointFlowScalarJets_state_circleMember hS hT rsel hrsel n z hz
        (Fin.tail w) (w 0) hw
    | succ k ih =>
      intro w j hj hw
      have hk : k < n := by have hjlt := j.isLt; omega
      let i' : Fin n := ⟨k, hk⟩
      let w' : Fin (n + 1) → (StateDirections S × ℝ) :=
        Fin.snoc (Fin.tail w) (w 0)
      have hij : i'.succ = j := Fin.ext (by simpa only [i', Fin.val_succ] using hj.symm)
      have hw' : (w' i'.castSucc).2 = 0 := by
        dsimp only [w']
        rw [Fin.snoc_castSucc]
        change (w i'.succ).2 = 0
        rw [hij]
        exact hw
      rw [hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w]
      exact ih w' i'.castSucc rfl hw'
  exact haux i.val v i rfl hi

theorem N01Properties.endpointFlowScalarJets_positive_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) :
    CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) := by
  classical
  let A := hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
  let P : Submodule ℝ (ℕ → ℝ → ℝ) := LinearMap.range (S.circle (3 / 4 : ℝ)).decode
  let q : Fin (n + 1) → (StateDirections S × ℝ) :=
    fun i => (v i).2 • scalarParameterDirection S
  have hscalar : A (fun _ => scalarParameterDirection S) ∈ P :=
    (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mpr
      (hN.endpointFlow_pure_scalar_circleMember hS hT rsel hrsel n z hz)
  have hq : A q ∈ P := by
    have heq : A q = (∏ i : Fin (n + 1), (v i).2) •
        A (fun _ => scalarParameterDirection S) :=
      A.map_smul_univ (fun i => (v i).2) (fun _ => scalarParameterDirection S)
    rw [heq]
    exact P.smul_mem _ hscalar
  have hterm (i : Fin (n + 1)) :
      A (multilinearDifferenceTuple q v i) ∈ P := by
    apply (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mpr
    apply hN.endpointFlowScalarJets_circleMember_of_state_slot hS hT rsel hrsel n z hz
      (multilinearDifferenceTuple q v i) i
    simp only [multilinearDifferenceTuple, lt_self_iff_false, if_false, if_true]
    change (v i).2 - (v i).2 * 1 = 0
    rw [mul_one, sub_self]
  have hdiff : A v - A q ∈ P := by
    have heq : A v - A q = ∑ i : Fin (n + 1), A (multilinearDifferenceTuple q v i) := by
      simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies,
        multilinearDifferenceTuple] using A.map_sub_map_piecewise v q Finset.univ
    rw [heq]
    exact P.sum_mem (fun i _ => hterm i)
  apply (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mp
  simpa only [sub_add_cancel] using P.add_mem hdiff hq

end ContinuousFlexibility.Statements
