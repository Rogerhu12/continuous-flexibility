module

public import ContinuousFlexibility.Analysis.HeightSectorDirections

/-!
# The sharp one-high weight for scalar and height directions

The finite-product identity is proved for an abstract seminorm family
before it is instantiated in the physical state space. Any number of
unit scalar directions leaves one low and one high height factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance heightScalarVariationWeightsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set
open scoped BigOperators

private theorem oneHighVariationWeight_unit_snoc
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high n : ℕ)
    (x q w : E) (hbaseq : p base q = 1) (hhighq : p high q = 1) :
    oneHighVariationWeight p base high x (Fin.snoc (fun _ : Fin n => q) w) =
      ((n : ℝ) + 1 + p high x) * p base w + p high w := by
  classical
  let v : Fin (n + 1) → E := Fin.snoc (fun _ : Fin n => q) w
  have hvcast (i : Fin n) : v i.castSucc = q := Fin.snoc_castSucc _ _ i
  have hvlast : v (Fin.last n) = w := Fin.snoc_last _ _
  have hnotlast (i : Fin n) : i.castSucc ≠ Fin.last n := by
    intro hi
    have he := congrArg Fin.val hi
    simp only [Fin.val_castSucc, Fin.val_last] at he
    omega
  have hbase (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : p base (v i) = 1 := by
    cases i using Fin.lastCases with
    | last => exact (hi rfl).elim
    | cast i => rw [hvcast, hbaseq]
  have hlast : (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n),
      p base (v j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    exact hbase j (Finset.mem_erase.mp hj).1
  have hcast (i : Fin n) :
      (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.castSucc, p base (v j)) =
        p base w := by
    have hm : Fin.last n ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.castSucc :=
      Finset.mem_erase.mpr ⟨(hnotlast i).symm, Finset.mem_univ _⟩
    calc
      _ = p base (v (Fin.last n)) :=
        Finset.prod_eq_single_of_mem (Fin.last n) hm (fun j _ hj => hbase j hj)
      _ = _ := congrArg (p base) hvlast
  have hprod : (∏ i : Fin (n + 1), p base (v i)) = p base w := by
    rw [Fin.prod_univ_castSucc]
    simp only [hvcast, hvlast, hbaseq, Finset.prod_const_one, one_mul]
  have hsum :
      (∑ i : Fin (n + 1), p high (v i) *
        ∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, p base (v j)) =
        (n : ℝ) * p base w + p high w := by
    rw [Fin.sum_univ_castSucc]
    simp only [hcast, hlast, hvcast, hvlast, hhighq, one_mul, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change oneHighVariationWeight p base high x v = _
  rw [oneHighVariationWeight, hprod, hsum]
  ring

theorem oneHighVariationWeight_scalar_height
    (S : PhysicalSpacesData) (base high n : ℕ)
    (z : StateDirections S × ℝ) (η : HeightPair S) :
    oneHighVariationWeight (pairGrading (sectorGrading S) realGrading) base high z
      (Fin.snoc (fun _ : Fin n => scalarParameterDirection S) (heightParameterDirection S η)) =
      ((n : ℝ) + 1 + pairGrading (sectorGrading S) realGrading high z) *
        heightPairGrading S base η + heightPairGrading S high η := by
  have h := oneHighVariationWeight_unit_snoc
    (pairGrading (sectorGrading S) realGrading) base high n z
    (scalarParameterDirection S) (heightParameterDirection S η)
    (scalarParameterDirection_grading S base) (scalarParameterDirection_grading S high)
  simpa only [heightParameterDirection_grading] using h

theorem sectorPairGrading_scalar_segment_le
    (S : PhysicalSpacesData) (n : ℕ) (x : StateDirections S)
    {t q : ℝ} (ht : t ∈ uIcc (0 : ℝ) q) :
    pairGrading (sectorGrading S) realGrading n (x, t) ≤
      pairGrading (sectorGrading S) realGrading n (x, q) := by
  change sectorGrading S n x + ‖t‖ ≤ sectorGrading S n x + ‖q‖
  have h : ‖t‖ ≤ ‖q‖ := by
    simpa only [sub_zero, Real.norm_eq_abs] using abs_sub_left_of_mem_uIcc ht
  exact add_le_add (le_refl _) h

end ContinuousFlexibility.Statements
