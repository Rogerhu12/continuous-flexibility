module

public import ContinuousFlexibility.Analysis.N01EndpointStateCircleMember
public import ContinuousFlexibility.Analysis.N01EndpointScalarCircleMember
public import ContinuousFlexibility.Analysis.ScalarJetSchwarz

/-!
# All positive-order endpoint jets are actual circle fields

A cyclic identity moves any state slot to the localized last slot.
The exact multilinear telescoping identity then separates an arbitrary
tuple into its pure scalar part and finitely many tuples with a state
slot. Every term lies in the range of the actual circle decoder.
-/

@[expose] public section

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

private theorem cyclic_last_slot_property
    {E F : Type*} (n : ℕ) (A : (Fin (n + 1) → E) → F)
    (P : F → Prop) (Q : E → Prop)
    (hrotate : ∀ v, A v = A (Fin.snoc (Fin.tail v) (v 0)))
    (hlast : ∀ (vs : Fin n → E) (u : E), Q u → P (A (Fin.snoc vs u)))
    (v : Fin (n + 1) → E) (i : Fin (n + 1)) (hi : Q (v i)) :
    P (A v) := by
  have haux : ∀ k : ℕ, ∀ (w : Fin (n + 1) → E) (j : Fin (n + 1)),
      j.val = k → Q (w j) → P (A w) := by
    intro k
    induction k with
    | zero =>
      intro w j hj hw
      have hj0 : j = 0 := Fin.ext hj
      have hw0 : Q (w 0) := Eq.mp (congrArg (fun t : Fin (n + 1) => Q (w t)) hj0) hw
      exact Eq.mpr (congrArg P (hrotate w)) (hlast (Fin.tail w) (w 0) hw0)
    | succ k ih =>
      intro w j hj hw
      have hk : k < n := by have hjlt := j.isLt; omega
      let i' : Fin n := ⟨k, hk⟩
      let w' : Fin (n + 1) → E :=
        Fin.snoc (α := fun _ : Fin (n + 1) => E) (Fin.tail w) (w 0)
      have hij : i'.succ = j := Fin.ext hj.symm
      have hentry : w' i'.castSucc = w j :=
        (show w' i'.castSucc = w i'.succ from
          Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => E) (w 0) (Fin.tail w) i').trans
            (congrArg w hij)
      have hw' : Q (w' i'.castSucc) := Eq.mpr (congrArg Q hentry) hw
      exact Eq.mpr (congrArg P (hrotate w)) (ih w' i'.castSucc rfl hw')
  exact haux i.val v i rfl hi

private theorem multilinear_mem_of_scalar_and_zero_slot
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (n : ℕ) (A : MultilinearMap ℝ (fun _ : Fin (n + 1) => E) F)
    (P : Submodule ℝ F) (q : E →ₗ[ℝ] ℝ) (e : E) (he : q e = 1)
    (hscalar : A (fun _ => e) ∈ P)
    (hstate : ∀ (w : Fin (n + 1) → E) (i : Fin (n + 1)), q (w i) = 0 → A w ∈ P)
    (v : Fin (n + 1) → E) : A v ∈ P := by
  classical
  let qv : Fin (n + 1) → E := fun i => q (v i) • e
  have hq : A qv ∈ P := by
    have heq : A qv = (∏ i : Fin (n + 1), q (v i)) • A (fun _ => e) :=
      A.map_smul_univ (fun i => q (v i)) (fun _ => e)
    exact Eq.mpr (congrArg (fun y : F => y ∈ P) heq) (P.smul_mem _ hscalar)
  have hterm (i : Fin (n + 1)) :
      A (fun j => if j < i then v j else if i = j then v j - qv j else qv j) ∈ P := by
    apply hstate _ i
    simp only [lt_self_iff_false, ite_false, ite_true]
    change q (v i - q (v i) • e) = 0
    simp only [map_sub, map_smul, he, smul_eq_mul, mul_one, sub_self]
  have hdiff : A v - A qv ∈ P := by
    have heq : A v - A qv = ∑ i : Fin (n + 1),
        A (fun j => if j < i then v j else if i = j then v j - qv j else qv j) := by
      simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies] using
        A.map_sub_map_piecewise v qv Finset.univ
    exact Eq.mpr (congrArg (fun y : F => y ∈ P) heq) (P.sum_mem (fun i _ => hterm i))
  exact Eq.mp (congrArg (fun y : F => y ∈ P) (sub_add_cancel (A v) (A qv)))
    (P.add_mem hdiff hq)

theorem N01Properties.endpointFlowScalarJets_rotate
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) :
    hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v =
      hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc (Fin.tail v) (v 0)) := by
  funext m θ
  let J := hN.sectorFlow_closed_angularTower hS hT m (rsel m)
    (hrsel m) 0 θ
  have hhead : J.D (n + 1) z v = J.D (n + 1) z (Fin.cons (v 0) (Fin.tail v)) :=
    (congrArg (fun w : Fin (n + 1) → (StateDirections S × ℝ) => J.D (n + 1) z w)
      (Fin.cons_self_tail v)).symm
  have hcycle :=
    J.cons_eq_snoc (sectorNeighborhood_convex S base ε ε) n z hz (v 0) (Fin.tail v)
  exact (hN.endpointFlowScalarJets_apply hS hT rsel hrsel (n + 1) z v m θ).trans
    (hhead.trans (hcycle.trans
      (hN.endpointFlowScalarJets_apply hS hT rsel hrsel (n + 1) z
        (Fin.snoc (Fin.tail v) (v 0)) m θ).symm))

theorem N01Properties.endpointFlowScalarJets_circleMember_of_state_slot
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ))
    (i : Fin (n + 1)) (hi : (v i).2 = 0) :
    CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) := by
  exact cyclic_last_slot_property n
    (fun w => hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z w)
    (CircleMember T (3 / 4 : ℝ)) (fun u : StateDirections S × ℝ => u.2 = 0)
    (fun w => hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w)
    (fun vs u hu => hN.endpointFlowScalarJets_state_circleMember hS hT rsel hrsel n z hz vs u hu)
    v i hi

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
  let q : (StateDirections S × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ (StateDirections S) ℝ
  have hscalar : A (fun _ => scalarParameterDirection S) ∈ P :=
    (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mpr
      (hN.endpointFlow_pure_scalar_circleMember hS hT rsel hrsel n z hz)
  have hstate (w : Fin (n + 1) → (StateDirections S × ℝ)) (i : Fin (n + 1))
      (hi : q (w i) = 0) : A w ∈ P :=
    (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mpr
      (hN.endpointFlowScalarJets_circleMember_of_state_slot hS hT rsel hrsel n z hz w i hi)
  exact (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mp
    (multilinear_mem_of_scalar_and_zero_slot n A P q (scalarParameterDirection S) rfl
      hscalar hstate v)

end ContinuousFlexibility.Statements
