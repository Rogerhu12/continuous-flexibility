module

public import ContinuousFlexibility.Analysis.N05SeedNegativeEnumerationGeometry
public import ContinuousFlexibility.Radial.MorseChainPartitionData

/-!
# An explicit enumeration of the actual seed's negative components

Slot zero is the central component.  The remaining slots use precisely
the same two-tail enumeration as the original Morse partition, beginning
at the actual retained model index.  No cell-index estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Real
open ContinuousFlexibility.Statements

variable {q : ℝ} (P : SeedReferenceConstruction q)

abbrev N05NegativeComponent :=
  {p : ℝ × ℝ // NegativeRadialComponent P.reference p.1 p.2}

def n05CentralNegativeComponent (hq : 0 < q) : P.N05NegativeComponent :=
  ⟨(centralRadius (-sqrt centralOscillatorA), centralRadius (sqrt centralOscillatorA)), by
    simpa only [NegativeRadialComponent, P.left_endpoint, P.right_endpoint, P.profile]
      using (P.glued.central_model_return hq (P.entry_core false) (P.entry_core true)).1⟩

def n05TailNegativeComponent (side : Bool) (k : ℕ) : P.N05NegativeComponent :=
  ⟨(P.n05TailScale side * P.n05ModelLeft side (P.retainedIndex + k),
    P.n05TailScale side * P.n05ModelRight side (P.retainedIndex + k)),
    P.n05_tail_component side
      (P.n05_model_component side (P.retainedIndex_ge.trans (Nat.le_add_right _ _)))
      (P.n05_model_closed_subset_retained_tail side (Nat.le_add_right _ _))⟩

/-- A tail component's left endpoint is strictly on its own side of the
central turning interval. -/
theorem n05_tail_left_separated (hq : 0 < q) (side : Bool) (k : ℕ) :
    if side then
      centralRadius (sqrt centralOscillatorA) < (P.n05TailNegativeComponent side k).val.1
    else (P.n05TailNegativeComponent side k).val.1 <
      centralRadius (-sqrt centralOscillatorA) := by
  have hn := P.retainedIndex_ge.trans (Nat.le_add_right P.retainedIndex k)
  have hc := P.n05_model_component side hn
  have ht := P.n05_model_closed_subset_retained_tail side
    (Nat.le_add_right P.retainedIndex k) (left_mem_Icc.mpr hc.2.1.le)
  cases side with
  | false =>
    have hL : exp P.cutoff.left < centralRadius (-sqrt centralOscillatorA) :=
      (lt_log_iff_exp_lt (centralRadius_pos _)).mp P.cutoff.left_turn
    exact ((mul_lt_mul_of_pos_left ht.2 P.glued.radiusL_pos).trans P.glued.left_entry).trans
      ((exp_lt_exp.mpr (by linarith only [hq])).trans hL)
  | true =>
    have hR : centralRadius (sqrt centralOscillatorA) < exp P.cutoff.right :=
      (log_lt_iff_lt_exp (centralRadius_pos _)).mp P.cutoff.right_turn
    exact (hR.trans ((exp_lt_exp.mpr (by linarith only [hq])).trans
      P.glued.right_entry)).trans
      (mul_lt_mul_of_pos_left ht.1 (P.n05TailScale_pos true))

theorem n05_central_ne_tail (hq : 0 < q) (side : Bool) (k : ℕ) :
    P.n05CentralNegativeComponent hq ≠ P.n05TailNegativeComponent side k := by
  intro he
  have heleft := congrArg (fun J : P.N05NegativeComponent => J.val.1) he
  have hp := P.n05_tail_left_separated hq side k
  cases side with
  | false => exact (ne_of_lt hp) heleft.symm
  | true => exact (ne_of_lt (central_turning_radii_pos_ordered.2.trans hp)) heleft

theorem n05_tailComponent_index_injective (side : Bool) :
    Function.Injective (P.n05TailNegativeComponent side) := by
  intro k l he
  have heleft : P.n05TailScale side * P.n05ModelLeft side (P.retainedIndex + k) =
      P.n05TailScale side * P.n05ModelLeft side (P.retainedIndex + l) :=
    congrArg (fun J : P.N05NegativeComponent => J.val.1) he
  have hleft := (mul_left_cancel₀ (P.n05TailScale_pos side).ne') heleft
  have hk := P.retainedIndex_ge.trans (Nat.le_add_right P.retainedIndex k)
  have hl := P.retainedIndex_ge.trans (Nat.le_add_right P.retainedIndex l)
  have hmem : P.n05ModelLeft side (P.retainedIndex + k) ∈
      Icc (P.n05ModelLeft side (P.retainedIndex + l))
        (P.n05ModelRight side (P.retainedIndex + l)) := by
    rw [hleft]
    exact left_mem_Icc.mpr (P.n05_model_component side hl).2.1.le
  have hindex := P.n05_model_index_eq_of_mem side hk hl
    (left_mem_Icc.mpr (P.n05_model_component side hk).2.1.le) hmem
  exact Nat.add_left_cancel hindex

theorem n05_tailComponent_injective (hq : 0 < q) :
    Function.Injective (fun p : Bool × ℕ => P.n05TailNegativeComponent p.1 p.2) := by
  rintro ⟨side, k⟩ ⟨other, l⟩ he
  have hside : side = other := by
    have heleft := congrArg (fun J : P.N05NegativeComponent => J.val.1) he
    cases side <;> cases other
    · rfl
    · have hL := P.n05_tail_left_separated hq false k
      have hR := P.n05_tail_left_separated hq true l
      exact False.elim ((ne_of_lt
        ((hL.trans central_turning_radii_pos_ordered.2).trans hR)) heleft)
    · have hR := P.n05_tail_left_separated hq true k
      have hL := P.n05_tail_left_separated hq false l
      exact False.elim ((ne_of_lt
        ((hL.trans central_turning_radii_pos_ordered.2).trans hR)) heleft.symm)
    · rfl
  subst other
  exact Prod.ext rfl (P.n05_tailComponent_index_injective side he)

def n05NegativeComponentAt (hq : 0 < q) : ℕ → P.N05NegativeComponent :=
  morseTwoTailAt (P.n05CentralNegativeComponent hq) P.n05TailNegativeComponent

theorem n05NegativeComponentAt_zero (hq : 0 < q) :
    P.n05NegativeComponentAt hq 0 = P.n05CentralNegativeComponent hq := rfl

theorem n05NegativeComponentAt_tail (hq : 0 < q) (side : Bool) (k : ℕ) :
    P.n05NegativeComponentAt hq (morseTailIndex side k) =
      P.n05TailNegativeComponent side k :=
  morseTwoTailAt_tail (P.n05CentralNegativeComponent hq) P.n05TailNegativeComponent side k

theorem n05_seed_slot_cases (m : ℕ) :
    m = 0 ∨ ∃ (side : Bool) (k : ℕ), m = morseTailIndex side k := by
  cases m with
  | zero => exact Or.inl rfl
  | succ m =>
    refine Or.inr ⟨(Equiv.boolProdNatEquivNat.symm m).1,
      (Equiv.boolProdNatEquivNat.symm m).2, ?_⟩
    unfold morseTailIndex
    simpa only [Prod.eta] using
      (congrArg Nat.succ (Equiv.boolProdNatEquivNat.apply_symm_apply m)).symm

theorem n05NegativeComponentAt_injective (hq : 0 < q) :
    Function.Injective (P.n05NegativeComponentAt hq) := by
  intro m n he
  rcases n05_seed_slot_cases m with rfl | ⟨side, k, rfl⟩ <;>
    rcases n05_seed_slot_cases n with rfl | ⟨other, l, rfl⟩
  · rfl
  · exact False.elim (P.n05_central_ne_tail hq other l
      (by simpa only [n05NegativeComponentAt_zero, n05NegativeComponentAt_tail] using he))
  · exact False.elim (P.n05_central_ne_tail hq side k
      (by simpa only [n05NegativeComponentAt_zero, n05NegativeComponentAt_tail] using he.symm))
  · have hp : (side, k) = (other, l) := P.n05_tailComponent_injective hq
      (by simpa only [n05NegativeComponentAt_tail] using he)
    exact congrArg (fun p : Bool × ℕ => morseTailIndex p.1 p.2) hp

theorem n05NegativeComponentAt_surjective (hq : 0 < q) :
    Function.Surjective (P.n05NegativeComponentAt hq) := by
  intro J
  rcases P.n05_component_cases_retained hq J.property with
    ⟨hl, hh⟩ | ⟨side, n, hn, hl, hh⟩
  · refine ⟨0, ?_⟩
    rw [n05NegativeComponentAt_zero]
    apply Subtype.ext
    exact Prod.ext hl.symm hh.symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine ⟨morseTailIndex side k, ?_⟩
    rw [n05NegativeComponentAt_tail]
    apply Subtype.ext
    exact Prod.ext hl.symm hh.symm

/-- The same concrete component map is used in the later host-index bound. -/
def n05NegativeEnumeration (hq : 0 < q) : ℕ ≃ P.N05NegativeComponent :=
  Equiv.ofBijective (P.n05NegativeComponentAt hq)
    ⟨P.n05NegativeComponentAt_injective hq, P.n05NegativeComponentAt_surjective hq⟩

theorem n05NegativeEnumeration_apply (hq : 0 < q) (m : ℕ) :
    P.n05NegativeEnumeration hq m = P.n05NegativeComponentAt hq m := by
  exact congrFun (Equiv.coe_ofBijective (P.n05NegativeComponentAt hq)
    ⟨P.n05NegativeComponentAt_injective hq, P.n05NegativeComponentAt_surjective hq⟩) m

end ContinuousFlexibility.Radial.SeedReferenceConstruction
