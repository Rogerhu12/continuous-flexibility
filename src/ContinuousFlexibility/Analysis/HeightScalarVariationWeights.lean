import ContinuousFlexibility.Analysis.HeightSectorDirections

/-!
# The sharp one-high weight for scalar and height directions

Any number of unit scalar directions and one physical height direction
leave precisely one low height term and one high height term. The
parameter order affects a numerical coefficient, never the material
grading order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators

theorem oneHighVariationWeight_scalar_height
    (S : PhysicalSpacesData) (base high n : ℕ)
    (z : StateDirections S × ℝ) (η : HeightPair S) :
    oneHighVariationWeight (pairGrading (sectorGrading S) realGrading) base high z
      (Fin.snoc (fun _ : Fin n => scalarParameterDirection S) (heightParameterDirection S η)) =
      ((n : ℝ) + 1 + pairGrading (sectorGrading S) realGrading high z) *
        heightPairGrading S base η + heightPairGrading S high η := by
  classical
  let p := pairGrading (sectorGrading S) realGrading
  let v : Fin (n + 1) → (StateDirections S × ℝ) :=
    Fin.snoc (fun _ : Fin n => scalarParameterDirection S) (heightParameterDirection S η)
  have hvcast (i : Fin n) : v i.castSucc = scalarParameterDirection S :=
    Fin.snoc_castSucc _ _ i
  have hvlast : v (Fin.last n) = heightParameterDirection S η := Fin.snoc_last _ _
  have hnotlast (i : Fin n) : i.castSucc ≠ Fin.last n := by
    intro hi
    have he := congrArg Fin.val hi
    simp only [Fin.val_castSucc, Fin.val_last] at he
    omega
  have hbase (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : p base (v i) = 1 := by
    cases i using Fin.lastCases with
    | last => exact (hi rfl).elim
    | cast i => rw [hvcast]; exact scalarParameterDirection_grading S base
  have hlast : (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n),
      p base (v j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    exact hbase j (Finset.mem_erase.mp hj).1
  have hcast (i : Fin n) :
      (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.castSucc, p base (v j)) =
        heightPairGrading S base η := by
    have hm : Fin.last n ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.castSucc :=
      Finset.mem_erase.mpr ⟨(hnotlast i).symm, Finset.mem_univ _⟩
    calc
      _ = p base (v (Fin.last n)) :=
        Finset.prod_eq_single_of_mem (Fin.last n) hm (fun j _ hj => hbase j hj)
      _ = _ := by rw [hvlast]; exact heightParameterDirection_grading S η base
  have hprod : (∏ i : Fin (n + 1), p base (v i)) = heightPairGrading S base η := by
    rw [Fin.prod_univ_castSucc]
    simp only [hvcast, hvlast, p, scalarParameterDirection_grading,
      heightParameterDirection_grading, Finset.prod_const_one, one_mul]
  have hsum :
      (∑ i : Fin (n + 1), p high (v i) *
        ∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, p base (v j)) =
        (n : ℝ) * heightPairGrading S base η + heightPairGrading S high η := by
    rw [Fin.sum_univ_castSucc]
    simp only [hcast, hlast, hvcast, hvlast, p, scalarParameterDirection_grading,
      heightParameterDirection_grading, one_mul, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change oneHighVariationWeight p base high z v = _
  rw [oneHighVariationWeight, hprod, hsum]
  ring

theorem sectorPairGrading_scalar_segment_le
    (S : PhysicalSpacesData) (n : ℕ) (x : StateDirections S)
    {t q : ℝ} (ht : t ∈ uIcc (0 : ℝ) q) :
    pairGrading (sectorGrading S) realGrading n (x, t) ≤
      pairGrading (sectorGrading S) realGrading n (x, q) := by
  change sectorGrading S n x + ‖t‖ ≤ sectorGrading S n x + ‖q‖
  apply add_le_add_left
  simpa only [sub_zero, Real.norm_eq_abs] using abs_sub_left_of_mem_uIcc ht

end ContinuousFlexibility.Statements
