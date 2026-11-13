import ContinuousFlexibility.Analysis.N04RealizationCoefficientAnnularTowers
import ContinuousFlexibility.Analysis.N04PulledFieldsStripPhysicalCost

/-!
# Full physical height for the actual original coefficient increment

The N01 bound keeps its sample height while the containing cell is
chosen at the physical point. Material transfer moves the complete
height and exponential cost to that point. The original low grading
and loss remain fixed for every parameter order and every coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

private theorem n04PulledFields_constantShiftJet_difference
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f g : E → ℝ}
    (J : SmoothDirections U f) (K : SmoothDirections U g) (c : ℝ)
    (heq : ∀ x ∈ U, f x = g x + c)
    (k : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E) :
    J.D k x v - (if k = 0 then c else 0) = K.D k x v := by
  cases k with
  | zero =>
      have hv : v = (Fin.elim0 : Fin 0 → E) := Subsingleton.elim _ _
      have hJ : J.D 0 x v = f x := (congrArg (J.D 0 x) hv).trans (J.zero x hx)
      have hK : K.D 0 x v = g x := (congrArg (K.D 0 x) hv).trans (K.zero x hx)
      rw [hJ, hK, if_pos rfl, heq x hx]
      ring
  | succ k =>
      simp only [Nat.succ_ne_zero, ite_false, sub_zero]
      exact J.positive_jet_eq_of_constant_shift K c heq k x hx v

local instance n04PulledFieldsOriginalDifferenceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- Every actual increment jet has the original one-high bound with
the full height evaluated at the same physical point. -/
theorem n04PulledFields_annularCoefficientIncrement_physicalOneHigh
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (k s : ℕ) :
    ∃ A Q : ℝ, 0 < A ∧ 0 ≤ Q ∧ ∀ (i : Fin 3) (a b : ℕ), a + b ≤ s →
      ∀ (p : PolarPoint) (hp : p ∈ annularOpen D),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → StateDirections S × ℝ,
        |(n04Realization_annularCoefficientIncrementTower hN i a b p hp).D k z v| ≤
          A * T.E0 p.1 ^ Q * T.H p.1 ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
              base (s + loss) z v := by
  obtain ⟨B, hB, hbound⟩ := hN.sectorCoefficientTower_bound k s
  obtain ⟨K, Q, hK, hQ, htransfer⟩ := n04PulledFields_cellSample_physicalCost
    hT hN.1.1 (by norm_num : 0 < (3 / 4 : ℝ)) hB.le
  refine ⟨B * K, Q, mul_pos hB hK, hQ, ?_⟩
  intro i a b hab p hp z hz v
  let j := n04CellAt D p.1
  have hj : p.1 ∈ D.cells j := n04_cell_at_mem hN.1.1.choose_spec.2.1 hp.1
  let W := oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
    base (s + loss) z v
  have hW : 0 ≤ W := oneHighVariationWeight_nonneg _ _ _ _ _
  have hraw : |(n04Realization_annularCoefficientIncrementTower hN i a b p hp).D k z v| ≤
      B * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B * W :=
    hbound j i a b p hab hj z hz v
  calc
    _ ≤ B * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B * W := hraw
    _ = B * (T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B) * W := by ring
    _ ≤ B * (K * T.H p.1 ^ (3 / 4 : ℝ) * T.E0 p.1 ^ Q) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (htransfer j p.1 hj) hB.le) hW
    _ = _ := by dsimp only [W]; ring

/-- The same estimate holds for any genuine original-coefficient tower
on a smaller open parameter domain. The reference term occurs exactly
at parameter order zero; the chosen constants precede that domain. -/
theorem n04PulledFields_originalCoefficient_difference_physicalOneHigh
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (k s : ℕ) :
    ∃ A Q : ℝ, 0 < A ∧ 0 ≤ Q ∧ ∀ (i : Fin 3) (a b : ℕ), a + b ≤ s →
      ∀ (p : PolarPoint) (hp : p ∈ annularOpen D),
      ∀ (U : Set (StateDirections S × ℝ)) (hU : IsOpen U),
      U ⊆ sectorNeighborhood S base ε ε →
      ∀ J : SmoothDirections U (fun z => mixedDerivative a b
        (originalCoefficientEntry D S C i (liftSectorParameter S C z)) p),
      ∀ z ∈ U, ∀ v : Fin k → StateDirections S × ℝ,
        |J.D k z v - (if k = 0 then mixedDerivative a b
          (originalCoefficientEntry D S C i (C.referenceState, 0)) p else 0)| ≤
          A * T.E0 p.1 ^ Q * T.H p.1 ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
              base (s + loss) z v := by
  obtain ⟨A, Q, hA, hQ, hb⟩ :=
    n04PulledFields_annularCoefficientIncrement_physicalOneHigh hN hT k s
  refine ⟨A, Q, hA, hQ, ?_⟩
  intro i a b hab p hp U hU hsub J z hz v
  let K := (n04Realization_annularCoefficientIncrementTower hN i a b p hp).restrict hU hsub
  have heq := n04PulledFields_constantShiftJet_difference J K
    (mixedDerivative a b (originalCoefficientEntry D S C i (C.referenceState, 0)) p)
    (fun x hx => n04Realization_coefficientMixed_eq_increment_add hN hS hT i a b hp (hsub hx))
    k z hz v
  exact (congrArg abs heq).trans_le (hb i a b hab p hp z (hsub hz) v)

end ContinuousFlexibility.Analysis
