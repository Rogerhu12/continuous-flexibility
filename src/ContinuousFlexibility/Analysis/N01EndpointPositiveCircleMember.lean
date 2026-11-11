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

private theorem rotating_last_slot
    {E F : Type*} (n : ℕ) (A : (Fin (n + 1) → E) → F)
    (P : F → Prop) (Q : E → Prop)
    (hrotate : ∀ w, A w = A (Fin.snoc (Fin.tail w) (w 0)))
    (hlast : ∀ (w : Fin n → E) (u : E), Q u → P (A (Fin.snoc w u)))
    (v : Fin (n + 1) → E) (i : Fin (n + 1)) (hi : Q (v i)) :
    P (A v) := by
  have haux : ∀ k : ℕ, ∀ (w : Fin (n + 1) → E) (j : Fin (n + 1)),
      j.val = k → Q (w j) → P (A w) := by
    intro k
    induction k with
    | zero =>
      intro w j hj hw
      have hj0 : j = 0 := Fin.ext hj
      rw [hj0] at hw
      rw [hrotate w]
      exact hlast (Fin.tail w) (w 0) hw
    | succ k ih =>
      intro w j hj hw
      have hk : k < n := by have hjlt := j.isLt; omega
      let i' : Fin n := ⟨k, hk⟩
      let w' : Fin (n + 1) → E := Fin.snoc (Fin.tail w) (w 0)
      have hij : i'.succ = j := Fin.ext (by simpa only [i', Fin.val_succ] using hj.symm)
      have hw' : Q (w' i'.castSucc) := by
        dsimp only [w']
        rw [Fin.snoc_castSucc]
        change Q (w i'.succ)
        rw [hij]
        exact hw
      rw [hrotate w]
      exact ih w' i'.castSucc rfl hw'
  exact haux i.val v i rfl hi

private theorem circleMember_of_scalar_split
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    (hH : IsCircleModel T γ H) (n : ℕ)
    (A : MultilinearMap ℝ (fun _ : Fin (n + 1) => E) (ℕ → ℝ → ℝ))
    (e : E) (q : E →ₗ[ℝ] ℝ) (he : q e = 1)
    (hscalar : CircleMember T γ (A (fun _ => e)))
    (hstate : ∀ (w : Fin (n + 1) → E) (i : Fin (n + 1)),
      q (w i) = 0 → CircleMember T γ (A w))
    (v : Fin (n + 1) → E) : CircleMember T γ (A v) := by
  classical
  let P : Submodule ℝ (ℕ → ℝ → ℝ) := LinearMap.range H.decode
  let u : Fin (n + 1) → E := fun i => q (v i) • e
  have hscalar_mem : A (fun _ => e) ∈ P :=
    (circleDecode_mem_range_iff hH _).mpr hscalar
  have hu : A u ∈ P := by
    have heq : A u = (∏ i : Fin (n + 1), q (v i)) • A (fun _ => e) :=
      A.map_smul_univ (fun i => q (v i)) (fun _ => e)
    rw [heq]
    exact P.smul_mem _ hscalar_mem
  have hterm (i : Fin (n + 1)) : A (multilinearDifferenceTuple u v i) ∈ P := by
    apply (circleDecode_mem_range_iff hH _).mpr
    apply hstate (multilinearDifferenceTuple u v i) i
    simp only [multilinearDifferenceTuple, lt_self_iff_false, if_false, if_true]
    change q (v i - q (v i) • e) = 0
    rw [map_sub, map_smul, he, smul_eq_mul, mul_one, sub_self]
  have hdiff : A v - A u ∈ P := by
    have heq : A v - A u = ∑ i : Fin (n + 1), A (multilinearDifferenceTuple u v i) := by
      change A v - A u = ∑ i : Fin (n + 1),
        A (fun j => if j < i then v j else if i = j then v j - u j else u j)
      simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies] using
        A.map_sub_map_piecewise v u Finset.univ
    rw [heq]
    exact P.sum_mem (fun i _ => hterm i)
  apply (circleDecode_mem_range_iff hH _).mp
  simpa only [sub_add_cancel] using P.add_mem hdiff hu

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
  let J := hN.sectorFlow_closed_angularTower hS hT m (rsel m)
    (hrsel m) 0 θ
  have hrotate : J.D (n + 1) z v =
      J.D (n + 1) z (Fin.snoc (Fin.tail v) (v 0)) :=
    (congrArg (fun w : Fin (n + 1) → (StateDirections S × ℝ) =>
      J.D (n + 1) z w) (Fin.cons_self_tail v)).symm.trans
      (J.cons_eq_snoc (sectorNeighborhood_convex S base ε ε) n z hz (v 0) (Fin.tail v))
  exact (hN.endpointFlowScalarJets_apply hS hT rsel hrsel (n + 1) z v m θ).trans
    (hrotate.trans (hN.endpointFlowScalarJets_apply hS hT rsel hrsel
      (n + 1) z (Fin.snoc (Fin.tail v) (v 0)) m θ).symm)

theorem N01Properties.endpointFlowScalarJets_circleMember_of_state_slot
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ))
    (i : Fin (n + 1)) (hi : (v i).2 = 0) :
    CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) := by
  exact rotating_last_slot n
    (fun w => hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z w)
    (CircleMember T (3 / 4 : ℝ)) (fun w : StateDirections S × ℝ => w.2 = 0)
    (fun w => hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w)
    (fun w u hu => hN.endpointFlowScalarJets_state_circleMember hS hT rsel hrsel
      n z hz w u hu) v i hi

theorem N01Properties.endpointFlowScalarJets_positive_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin (n + 1) → (StateDirections S × ℝ)) :
    CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) := by
  exact circleMember_of_scalar_split (hS.2.1 (3 / 4 : ℝ)) n
    (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z)
    (scalarParameterDirection S) (LinearMap.snd ℝ (StateDirections S) ℝ) rfl
    (hN.endpointFlow_pure_scalar_circleMember hS hT rsel hrsel n z hz)
    (fun w i hi => hN.endpointFlowScalarJets_circleMember_of_state_slot hS hT rsel hrsel
      n z hz w i hi) v

end ContinuousFlexibility.Statements
