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

private theorem tuple_rotate_of_cons_snoc
    {E F : Type*} {n : ℕ}
    (A : (Fin (n + 1) → E) → F)
    (hA : ∀ (w : E) (v : Fin n → E),
      A (Fin.cons w v) = A (Fin.snoc v w))
    (v : Fin (n + 1) → E) :
    A v = A (Fin.snoc (Fin.tail v) (v 0)) :=
  (congrArg A (Fin.cons_self_tail v)).symm.trans (hA (v 0) (Fin.tail v))

private theorem value_property_of_zero_slot
    {E F : Type*} {n : ℕ}
    (A : (Fin (n + 1) → E) → F) (P : F → Prop) (q : E → ℝ)
    (hrotate : ∀ v, A v = A (Fin.snoc (Fin.tail v) (v 0)))
    (hlast : ∀ (v : Fin n → E) (w : E), q w = 0 → P (A (Fin.snoc v w)))
    (v : Fin (n + 1) → E) (i : Fin (n + 1)) (hi : q (v i) = 0) :
    P (A v) := by
  have haux : ∀ k : ℕ, ∀ (w : Fin (n + 1) → E) (j : Fin (n + 1)),
      j.val = k → q (w j) = 0 → P (A w) := by
    intro k
    induction k with
    | zero =>
        intro w j hj hw
        have hj0 : j = 0 := Fin.ext hj
        rw [hj0] at hw
        exact (congrArg P (hrotate w)).mpr (hlast (Fin.tail w) (w 0) hw)
    | succ k ih =>
        intro w j hj hw
        have hk : k < n := by have hjlt := j.isLt; omega
        let i' : Fin n := ⟨k, hk⟩
        let w' : Fin (n + 1) → E := Fin.snoc (Fin.tail w) (w 0)
        have hij : i'.succ = j := by
          apply Fin.ext
          change k + 1 = j.val
          exact hj.symm
        have hw' : q (w' i'.castSucc) = 0 := by
          change q ((Fin.snoc (Fin.tail w) (w 0) : Fin (n + 1) → E) i'.castSucc) = 0
          rw [Fin.snoc_castSucc]
          change q (w i'.succ) = 0
          exact (congrArg (fun j => q (w j)) hij).trans hw
        exact (congrArg P (hrotate w)).mpr (ih w' i'.castSucc rfl hw')
  exact haux i.val v i rfl hi

private theorem multilinear_mem_of_scalar_split
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {n : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin (n + 1) => E) F)
    (P : Submodule ℝ F) (q : E →ₗ[ℝ] ℝ) (d : E) (hd : q d = 1)
    (hscalar : A (fun _ => d) ∈ P)
    (hslot : ∀ (w : Fin (n + 1) → E) (i : Fin (n + 1)),
      q (w i) = 0 → A w ∈ P)
    (v : Fin (n + 1) → E) :
    A v ∈ P := by
  classical
  let u : Fin (n + 1) → E := fun i => q (v i) • d
  have hu : A u ∈ P := by
    have heq : A u = (∏ i : Fin (n + 1), q (v i)) • A (fun _ => d) :=
      A.map_smul_univ (fun i => q (v i)) (fun _ => d)
    rw [heq]
    exact P.smul_mem _ hscalar
  have hterm (i : Fin (n + 1)) :
      A (multilinearDifferenceTuple u v i) ∈ P := by
    apply hslot (multilinearDifferenceTuple u v i) i
    simp only [multilinearDifferenceTuple, lt_self_iff_false, if_false, if_true]
    change q (v i - q (v i) • d) = 0
    simp only [map_sub, map_smul, RingHom.id_apply, hd, smul_eq_mul, mul_one, sub_self]
  have hdiff : A v - A u ∈ P := by
    have heq : A v - A u = ∑ i : Fin (n + 1), A (multilinearDifferenceTuple u v i) := by
      simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies,
        multilinearDifferenceTuple] using A.map_sub_map_piecewise v u Finset.univ
    rw [heq]
    exact P.sum_mem (fun i _ => hterm i)
  simpa only [sub_add_cancel] using P.add_mem hdiff hu

theorem N01Properties.endpointFlowScalarJets_rotate
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) :
    hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v =
      hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc (Fin.tail v) (v 0)) := by
  funext m θ
  let J := hN.sectorFlow_closed_angularTower hS hT m (rsel m) (hrsel m) 0 θ
  have hrot :
      J.D (n + 1) z v =
        J.D (n + 1) z (Fin.snoc (Fin.tail v) (v 0)) :=
    tuple_rotate_of_cons_snoc (fun w => J.D (n + 1) z w)
      (J.cons_eq_snoc (sectorNeighborhood_convex S base ε ε) n z hz) v
  exact (hN.endpointFlowScalarJets_apply hS hT rsel hrsel (n + 1) z v m θ).trans
    (hrot.trans (hN.endpointFlowScalarJets_apply hS hT rsel hrsel (n + 1) z
      (Fin.snoc (Fin.tail v) (v 0)) m θ).symm)

theorem N01Properties.endpointFlowScalarJets_circleMember_of_state_slot
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ))
    (i : Fin (n + 1)) (hi : (v i).2 = 0) :
    CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) := by
  exact value_property_of_zero_slot
    (fun w => hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z w)
    (CircleMember T (3 / 4 : ℝ)) (fun w : StateDirections S × ℝ => w.2)
    (fun w => hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w)
    (fun vs w hw =>
      hN.endpointFlowScalarJets_state_circleMember hS hT rsel hrsel n z hz vs w hw)
    v i hi

theorem N01Properties.endpointFlowScalarJets_positive_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) :
    CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) := by
  let A : MultilinearMap ℝ (fun _ : Fin (n + 1) => StateDirections S × ℝ)
      (ℕ → ℝ → ℝ) := hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
  let P : Submodule ℝ (ℕ → ℝ → ℝ) := LinearMap.range (S.circle (3 / 4 : ℝ)).decode
  have hscalar : A (fun _ => scalarParameterDirection S) ∈ P :=
    (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mpr
      (hN.endpointFlow_pure_scalar_circleMember hS hT rsel hrsel n z hz)
  have hslot (w : Fin (n + 1) → (StateDirections S × ℝ)) (i : Fin (n + 1))
      (hi : (w i).2 = 0) : A w ∈ P :=
    (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mpr
      (hN.endpointFlowScalarJets_circleMember_of_state_slot hS hT rsel hrsel n z hz w i hi)
  apply (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mp
  exact multilinear_mem_of_scalar_split A P
    (LinearMap.snd ℝ (StateDirections S) ℝ) (scalarParameterDirection S)
    (by rfl) hscalar hslot v

end ContinuousFlexibility.Statements
